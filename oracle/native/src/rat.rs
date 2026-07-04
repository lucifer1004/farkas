//! Tiered exact rational arithmetic (`TRat`) for the optimized engines.
//!
//! Representation (design justification):
//!   * `S(i64, i64)`  — the fast path.  Corpus coefficients are almost always
//!     tiny (4587/4599 instances have max coefficient < 10^50, and the vast
//!     majority < 10^6), and simplex pivot intermediates usually stay small,
//!     so a two-word unboxed variant with checked native ops wins by avoiding
//!     every heap allocation BigRational would make.
//!   * `M(i128, i128)` — one promotion step: any product of two i64 values
//!     fits i128 exactly, so an i64 overflow can always be *recomputed*
//!     losslessly in i128 (no wasted work beyond the failed checked op).
//!   * `B(Box<BigRational>)` — the exact catch-all (607-digit corpus
//!     coefficients land here directly via `from_bigint`).  Boxed so the enum
//!     stays at 32 bytes (i128 pair + tag) instead of embedding two BigInts.
//!
//! Invariants (all constructors preserve them):
//!   * denominator > 0, gcd(num, den) = 1;
//!   * canonical tier: a value is stored in the *smallest* tier it fits
//!     (results are opportunistically demoted after every op, so a transient
//!     overflow — e.g. a huge pivot value followed by cancellation — does not
//!     poison the rest of the solve into the slow tier).
//!
//! Instrumentation: per-thread counters record how many ring ops (+,-,*,/)
//! executed at each tier and how many overflow promotions occurred
//! (i64→i128 and i128→Big).  Counters are thread-local (no atomic traffic in
//! the hot loop) and are folded into global atomics by `flush_tls()`, which
//! the engines call once per solved instance.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};
use std::cell::Cell;
use std::cmp::Ordering;
use std::sync::atomic::{AtomicU64, Ordering as AtOrd};

// ---------------------------------------------------------------------------
// Counters
// ---------------------------------------------------------------------------

/// Indices: 0..3 = ops executed at tier i64/i128/Big; 3 = promotions
/// i64→i128; 4 = promotions i128→Big.
const NCTR: usize = 5;

thread_local! {
    /// Cumulative per-thread counters (never reset within a thread).
    static TLS: [Cell<u64>; NCTR] = const { [const { Cell::new(0) }; NCTR] };
    /// Value of TLS at the last flush, so flushes add only the delta.
    static TLS_FLUSHED: [Cell<u64>; NCTR] = const { [const { Cell::new(0) }; NCTR] };
}

static GLOBAL: [AtomicU64; NCTR] = [const { AtomicU64::new(0) }; NCTR];

#[inline]
fn bump(k: usize) {
    TLS.with(|t| t[k].set(t[k].get() + 1));
}

/// Fold this thread's counter deltas into the global totals.  Engines call
/// this once per instance, so worker threads never hold unflushed counts
/// between instances.
pub fn flush_tls() {
    TLS.with(|t| {
        TLS_FLUSHED.with(|f| {
            for k in 0..NCTR {
                let cur = t[k].get();
                let delta = cur - f[k].get();
                if delta > 0 {
                    GLOBAL[k].fetch_add(delta, AtOrd::Relaxed);
                    f[k].set(cur);
                }
            }
        })
    });
}

#[derive(Clone, Copy, Default, Debug)]
pub struct Counters {
    /// Ring ops (+,-,*,/; a division counts as one multiplicative op)
    /// executed at tier [i64, i128, Big].  An op is attributed to the tier of
    /// its widest operand; an op that overflows and promotes is still counted
    /// once, at the tier it started in.
    pub ops: [u64; 3],
    pub promo_to_i128: u64,
    pub promo_to_big: u64,
}

/// Global counter totals (flushes the calling thread's TLS first).
pub fn counters() -> Counters {
    flush_tls();
    Counters {
        ops: [
            GLOBAL[0].load(AtOrd::Relaxed),
            GLOBAL[1].load(AtOrd::Relaxed),
            GLOBAL[2].load(AtOrd::Relaxed),
        ],
        promo_to_i128: GLOBAL[3].load(AtOrd::Relaxed),
        promo_to_big: GLOBAL[4].load(AtOrd::Relaxed),
    }
}

/// Reset the global totals (used between per-engine benchmark runs).
pub fn reset_counters() {
    flush_tls();
    for g in &GLOBAL {
        g.store(0, AtOrd::Relaxed);
    }
}

/// Cumulative counters of the *current thread* only — race-free for tests
/// that assert on promotion behaviour (other test threads cannot interfere).
#[cfg_attr(not(test), allow(dead_code))]
pub fn tls_counters() -> Counters {
    TLS.with(|t| Counters {
        ops: [t[0].get(), t[1].get(), t[2].get()],
        promo_to_i128: t[3].get(),
        promo_to_big: t[4].get(),
    })
}

// ---------------------------------------------------------------------------
// TRat
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum TRat {
    /// num/den, den > 0, reduced.
    S(i64, i64),
    /// num/den, den > 0, reduced, does not fit `S` (num is never i128::MIN).
    M(i128, i128),
    /// Reduced, positive denominator (BigRational invariant); numerator or
    /// denominator does not fit i128.
    B(Box<BigRational>),
}

#[inline]
fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

#[inline]
fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Reduce n/d with d > 0 (both i64).  Result always fits `S`.
#[inline]
fn norm_s(n: i64, d: i64) -> TRat {
    debug_assert!(d > 0);
    if n == 0 {
        return TRat::S(0, 1);
    }
    // gcd divides d < 2^63, so the cast is safe even when |n| = 2^63.
    let g = gcd_u64(n.unsigned_abs(), d as u64) as i64;
    TRat::S(n / g, d / g)
}

/// Reduce n/d (i128, d != 0) and demote to the smallest fitting tier.
fn norm_m(n: i128, d: i128) -> TRat {
    debug_assert!(d != 0);
    if n == 0 {
        return TRat::S(0, 1);
    }
    if n == i128::MIN || d == i128::MIN {
        // unsigned_abs/neg edge case: settle it in BigInt space.
        return shrink_big(BigRational::new(BigInt::from(n), BigInt::from(d)));
    }
    let g = gcd_u128(n.unsigned_abs(), d.unsigned_abs()) as i128;
    let (mut n, mut d) = (n / g, d / g);
    if d < 0 {
        n = -n;
        d = -d;
    }
    match (i64::try_from(n), i64::try_from(d)) {
        (Ok(a), Ok(b)) => TRat::S(a, b),
        _ => TRat::M(n, d),
    }
}

/// Demote a (already reduced) BigRational to the smallest fitting tier.
/// A numerator of exactly i128::MIN stays Big: the M tier must never hold
/// i128::MIN (neg/recip negate the numerator, which would wrap).
fn shrink_big(r: BigRational) -> TRat {
    if let (Some(n), Some(d)) = (r.numer().to_i128(), r.denom().to_i128()) {
        if n == i128::MIN {
            return TRat::B(Box::new(r));
        }
        match (i64::try_from(n), i64::try_from(d)) {
            (Ok(a), Ok(b)) => TRat::S(a, b),
            _ => TRat::M(n, d),
        }
    } else {
        TRat::B(Box::new(r))
    }
}

impl TRat {
    pub fn zero() -> TRat {
        TRat::S(0, 1)
    }

    pub fn one() -> TRat {
        TRat::S(1, 1)
    }

    /// Test-support constructor.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn from_i64(n: i64) -> TRat {
        TRat::S(n, 1)
    }

    pub fn from_bigint(v: &BigInt) -> TRat {
        if let Some(n) = v.to_i64() {
            TRat::S(n, 1)
        } else if let Some(n) = v.to_i128().filter(|&n| n != i128::MIN) {
            // i128::MIN is excluded: the M tier must never hold it (see
            // shrink_big), so exactly -2^127 goes to the Big tier.
            TRat::M(n, 1)
        } else {
            TRat::B(Box::new(BigRational::from(v.clone())))
        }
    }

    /// 0 = i64, 1 = i128, 2 = Big (test-support introspection).
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn tier(&self) -> usize {
        match self {
            TRat::S(..) => 0,
            TRat::M(..) => 1,
            TRat::B(..) => 2,
        }
    }

    pub fn to_bigrational(&self) -> BigRational {
        match self {
            // Reduced with positive denominator by invariant -> new_raw is safe.
            TRat::S(n, d) => BigRational::new_raw(BigInt::from(*n), BigInt::from(*d)),
            TRat::M(n, d) => BigRational::new_raw(BigInt::from(*n), BigInt::from(*d)),
            TRat::B(r) => (**r).clone(),
        }
    }

    pub fn is_zero(&self) -> bool {
        match self {
            TRat::S(n, _) => *n == 0,
            TRat::M(n, _) => *n == 0,
            TRat::B(r) => r.is_zero(),
        }
    }

    pub fn is_positive(&self) -> bool {
        match self {
            TRat::S(n, _) => *n > 0,
            TRat::M(n, _) => *n > 0,
            TRat::B(r) => r.is_positive(),
        }
    }

    pub fn is_negative(&self) -> bool {
        match self {
            TRat::S(n, _) => *n < 0,
            TRat::M(n, _) => *n < 0,
            TRat::B(r) => r.is_negative(),
        }
    }

    /// Negation is exact and cheap; it is not counted as a ring op.
    pub fn neg(&self) -> TRat {
        match self {
            TRat::S(n, d) => match n.checked_neg() {
                Some(m) => TRat::S(m, *d),
                None => TRat::M(-(*n as i128), *d as i128), // -(i64::MIN) = 2^63
            },
            TRat::M(n, d) => TRat::M(-n, *d), // M never stores i128::MIN
            TRat::B(r) => shrink_big(-(**r).clone()),
        }
    }

    #[inline]
    fn as_i128(&self) -> (i128, i128) {
        match self {
            TRat::S(n, d) => (*n as i128, *d as i128),
            TRat::M(n, d) => (*n, *d),
            TRat::B(_) => unreachable!("as_i128 on Big tier"),
        }
    }

    pub fn add(&self, o: &TRat) -> TRat {
        self.addsub(o, false)
    }

    pub fn sub(&self, o: &TRat) -> TRat {
        self.addsub(o, true)
    }

    fn addsub(&self, o: &TRat, subtract: bool) -> TRat {
        match (self, o) {
            (TRat::S(a, b), TRat::S(c, d)) => {
                bump(0);
                let (a, b, c, d) = (*a, *b, *c, *d);
                let fast = (|| {
                    let t1 = a.checked_mul(d)?;
                    let t2 = c.checked_mul(b)?;
                    let n = if subtract {
                        t1.checked_sub(t2)?
                    } else {
                        t1.checked_add(t2)?
                    };
                    Some(norm_s(n, b.checked_mul(d)?))
                })();
                if let Some(r) = fast {
                    return r;
                }
                bump(3);
                // Exact in i128: |a*d|, |c*b| < 2^126 (d, b > 0), so the
                // sum/difference and b*d cannot overflow i128.
                let t1 = a as i128 * d as i128;
                let t2 = c as i128 * b as i128;
                let n = if subtract { t1 - t2 } else { t1 + t2 };
                norm_m(n, b as i128 * d as i128)
            }
            (TRat::B(_), _) | (_, TRat::B(_)) => {
                bump(2);
                let x = self.to_bigrational();
                let y = o.to_bigrational();
                shrink_big(if subtract { x - y } else { x + y })
            }
            _ => {
                bump(1);
                let (a, b) = self.as_i128();
                let (c, d) = o.as_i128();
                let fast = (|| {
                    let t1 = a.checked_mul(d)?;
                    let t2 = c.checked_mul(b)?;
                    let n = if subtract {
                        t1.checked_sub(t2)?
                    } else {
                        t1.checked_add(t2)?
                    };
                    Some(norm_m(n, b.checked_mul(d)?))
                })();
                if let Some(r) = fast {
                    return r;
                }
                bump(4);
                let t1 = BigInt::from(a) * BigInt::from(d);
                let t2 = BigInt::from(c) * BigInt::from(b);
                let n = if subtract { t1 - t2 } else { t1 + t2 };
                shrink_big(BigRational::new(n, BigInt::from(b) * BigInt::from(d)))
            }
        }
    }

    pub fn mul(&self, o: &TRat) -> TRat {
        match (self, o) {
            (TRat::S(a, b), TRat::S(c, d)) => {
                bump(0);
                let (a, b, c, d) = (*a, *b, *c, *d);
                if a == 0 || c == 0 {
                    return TRat::S(0, 1);
                }
                // Cross-reduce first: keeps products in i64 far more often
                // and makes the result reduced by construction (a2⊥b2, a2⊥d2,
                // c2⊥d2, c2⊥b2 pairwise coprime).
                let g1 = gcd_u64(a.unsigned_abs(), d as u64) as i64;
                let g2 = gcd_u64(c.unsigned_abs(), b as u64) as i64;
                let (a2, d2) = (a / g1, d / g1);
                let (c2, b2) = (c / g2, b / g2);
                match (a2.checked_mul(c2), b2.checked_mul(d2)) {
                    (Some(n), Some(den)) => TRat::S(n, den),
                    _ => {
                        bump(3);
                        // Exact in i128 (each factor fits i64).
                        norm_m(a2 as i128 * c2 as i128, b2 as i128 * d2 as i128)
                    }
                }
            }
            (TRat::B(_), _) | (_, TRat::B(_)) => {
                bump(2);
                shrink_big(self.to_bigrational() * o.to_bigrational())
            }
            _ => {
                bump(1);
                let (a, b) = self.as_i128();
                let (c, d) = o.as_i128();
                if a == 0 || c == 0 {
                    return TRat::S(0, 1);
                }
                let g1 = gcd_u128(a.unsigned_abs(), d as u128) as i128;
                let g2 = gcd_u128(c.unsigned_abs(), b as u128) as i128;
                let (a2, d2) = (a / g1, d / g1);
                let (c2, b2) = (c / g2, b / g2);
                match (a2.checked_mul(c2), b2.checked_mul(d2)) {
                    // n == i128::MIN falls through to the Big path: the M
                    // tier must never hold i128::MIN (see shrink_big).
                    (Some(n), Some(den)) if n != i128::MIN => {
                        match (i64::try_from(n), i64::try_from(den)) {
                            (Ok(x), Ok(y)) => TRat::S(x, y),
                            _ => TRat::M(n, den),
                        }
                    }
                    _ => {
                        bump(4);
                        shrink_big(BigRational::new(
                            BigInt::from(a) * BigInt::from(c),
                            BigInt::from(b) * BigInt::from(d),
                        ))
                    }
                }
            }
        }
    }

    /// Division: multiply by the reciprocal (counted as one multiplicative op).
    pub fn div(&self, o: &TRat) -> TRat {
        assert!(!o.is_zero(), "TRat division by zero");
        self.mul(&o.recip())
    }

    fn recip(&self) -> TRat {
        match self {
            TRat::S(n, d) => {
                if *n > 0 {
                    TRat::S(*d, *n)
                } else {
                    match (d.checked_neg(), n.checked_neg()) {
                        (Some(dn), Some(nn)) => TRat::S(dn, nn),
                        _ => TRat::M(-(*d as i128), -(*n as i128)), // n = i64::MIN
                    }
                }
            }
            TRat::M(n, d) => {
                // M never stores i128::MIN, so negation is safe; the
                // reciprocal has the same component magnitudes, so it cannot
                // demote to S (else the original would have been S).
                if *n > 0 {
                    TRat::M(*d, *n)
                } else {
                    TRat::M(-d, -n)
                }
            }
            TRat::B(r) => shrink_big(r.recip()),
        }
    }

    pub fn cmp_val(&self, o: &TRat) -> Ordering {
        match (self, o) {
            (TRat::S(a, b), TRat::S(c, d)) => {
                // Exact: i64 products fit i128; denominators positive.
                (*a as i128 * *d as i128).cmp(&(*c as i128 * *b as i128))
            }
            (TRat::B(_), _) | (_, TRat::B(_)) => self.to_bigrational().cmp(&o.to_bigrational()),
            _ => {
                let (a, b) = self.as_i128();
                let (c, d) = o.as_i128();
                match (a.checked_mul(d), c.checked_mul(b)) {
                    (Some(x), Some(y)) => x.cmp(&y),
                    _ => (BigInt::from(a) * BigInt::from(d))
                        .cmp(&(BigInt::from(c) * BigInt::from(b))),
                }
            }
        }
    }
}

impl PartialEq for TRat {
    fn eq(&self, o: &Self) -> bool {
        self.cmp_val(o) == Ordering::Equal
    }
}

impl PartialOrd for TRat {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp_val(o))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::One;
    use std::str::FromStr;

    fn q(n: i128, d: i128) -> TRat {
        norm_m(n, d)
    }

    fn ground(t: &TRat) -> BigRational {
        t.to_bigrational()
    }

    #[test]
    fn arithmetic_matches_bigrational_across_tiers() {
        let big = TRat::from_bigint(
            &BigInt::from_str("123456789012345678901234567890123456789").unwrap(),
        );
        let vals = [
            q(0, 1),
            q(3, 7),
            q(-5, 9),
            q(1, 1),
            q(i64::MAX as i128, 1),
            q(i64::MIN as i128, 3),
            q((i64::MAX as i128) * 12345, 67891),
            q(-(i64::MAX as i128) * 999983, (i64::MAX as i128) - 4),
            big.clone(),
            big.mul(&q(-1, 7919)),
        ];
        for x in &vals {
            for y in &vals {
                let (gx, gy) = (ground(x), ground(y));
                assert_eq!(ground(&x.add(y)), &gx + &gy, "add {x:?} {y:?}");
                assert_eq!(ground(&x.sub(y)), &gx - &gy, "sub {x:?} {y:?}");
                assert_eq!(ground(&x.mul(y)), &gx * &gy, "mul {x:?} {y:?}");
                if !y.is_zero() {
                    assert_eq!(ground(&x.div(y)), &gx / &gy, "div {x:?} {y:?}");
                }
                assert_eq!(x.cmp_val(y), gx.cmp(&gy), "cmp {x:?} {y:?}");
            }
            assert_eq!(ground(&x.neg()), -ground(x), "neg {x:?}");
        }
    }

    #[test]
    fn overflow_promotes_then_demotes() {
        let before = tls_counters();
        let a = TRat::from_i64(1 << 62);
        let b = a.mul(&a); // 2^124: overflows i64, exact in i128
        assert_eq!(b.tier(), 1, "2^124 must land in the i128 tier");
        let c = b.mul(&b); // 2^248: overflows i128 -> Big
        assert_eq!(c.tier(), 2, "2^248 must land in the Big tier");
        assert_eq!(
            ground(&c),
            ground(&a) * ground(&a) * ground(&a) * ground(&a)
        );
        // demotion: dividing back down must return to the smallest tier
        let d = c.div(&b).div(&b);
        assert_eq!(d.tier(), 0);
        assert_eq!(d, TRat::one());
        let after = tls_counters();
        assert!(
            after.promo_to_i128 > before.promo_to_i128,
            "i64->i128 promotion recorded"
        );
        assert!(
            after.promo_to_big > before.promo_to_big,
            "i128->Big promotion recorded"
        );
    }

    #[test]
    fn canonical_form_invariants() {
        // reduction + sign normalization
        match q(-4, -6) {
            TRat::S(n, d) => {
                assert_eq!((n, d), (2, 3));
            }
            other => panic!("expected S, got {other:?}"),
        }
        // i64::MIN edge cases
        let m = TRat::from_i64(i64::MIN);
        assert_eq!(m.neg().tier(), 1); // 2^63 does not fit i64
        assert_eq!(ground(&m.neg()), -ground(&m));
        let r = TRat::one().div(&m);
        assert_eq!(ground(&r), ground(&m).recip());
        assert!(r.is_negative());
        // Big value that fits small tiers demotes on construction
        let one = TRat::B(Box::new(BigRational::one()));
        assert_eq!(one.add(&TRat::zero()).tier(), 0);
    }

    #[test]
    fn i128_min_never_enters_m_tier() {
        let two127 = BigRational::from(BigInt::one() << 127);
        // Construction site 1: from_bigint(-2^127) must not become M(i128::MIN).
        let m = TRat::from_bigint(&(-(BigInt::one() << 127i32)));
        assert_ne!(m.tier(), 1, "-2^127 must live in the Big tier, not M");
        assert_eq!(ground(&m.neg()), two127, "neg(-2^127) must be exact");
        assert_eq!(ground(&TRat::one().div(&m)), ground(&m).recip());
        // Construction site 2: a mixed-tier product landing exactly on -2^127.
        let p = TRat::from_bigint(&(BigInt::one() << 64)).mul(&TRat::from_i64(i64::MIN));
        assert_eq!(ground(&p), -&two127);
        assert_ne!(
            p.tier(),
            1,
            "product -2^127 must live in the Big tier, not M"
        );
        assert_eq!(ground(&p.neg()), two127, "neg of product must be exact");
        assert_eq!(ground(&TRat::one().div(&p)), ground(&p).recip());
        // Construction site 3: Big-tier arithmetic shrinking to exactly -2^127.
        let s = TRat::B(Box::new(-&two127 - BigRational::one())).add(&TRat::one());
        assert_eq!(ground(&s), -&two127);
        assert_ne!(s.tier(), 1, "shrink_big(-2^127) must stay Big");
        assert_eq!(ground(&s.neg()), two127);
    }
}
