//! Exact certificate verifier.
//!
//! Semantics pinned against Mathlib v4.31.0 source and validated against all
//! 4548 known-good corpus certificates (100% pass):
//!
//! A certificate `hypIdx -> c` (c a positive integer) refutes `hyps` iff
//!   1. every referenced index is in range and every coefficient is > 0,
//!   2. the weighted sum of the hyps' linear forms is identically zero over
//!      *all* atom indices — including index 0, the constant atom
//!      ("Index 0 is reserved for constants", Linarith/Datatypes.lean), and
//!   3. at least one positively-weighted hyp is strict (`lt`).
//!
//! Then the sum is the comparison `0 < 0` (`Comp.isContr`: empty coeffs and
//! strength `lt`; `Ineq.max` makes the combined strength `lt` as soon as one
//! `lt` participates).  Combinations summing to a nonzero constant (e.g.
//! `1 <= 0`) are *not* Mathlib certificates; completeness is preserved
//! because linarith always injects the trivial hypothesis `-1 < 0` which can
//! absorb constant slack.

use crate::types::{Hyp, Ineq};
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::HashMap;

pub fn verify_cert(hyps: &[Hyp], cert: &[(usize, BigInt)]) -> bool {
    if cert.is_empty() {
        return false;
    }
    let mut sum: HashMap<usize, BigInt> = HashMap::new();
    let mut strict = false;
    for (idx, c) in cert {
        if *idx >= hyps.len() || *c <= BigInt::zero() {
            return false;
        }
        let h = &hyps[*idx];
        if h.ineq == Ineq::Lt {
            strict = true;
        }
        for (var, a) in &h.coeffs {
            let e = sum.entry(*var).or_insert_with(BigInt::zero);
            *e += c * a;
        }
    }
    strict && sum.values().all(|v| v.is_zero())
}
