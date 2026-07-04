//! Engine "hybrid": FP64 basis identification + exact repair. Kept as the
//! measured counterfactual to the tiered engine (it LOSES on the heavy
//! tail — see the soundness note in lib.rs: FP64 evidence is a hint, never
//! an answer); not used by the daemon.
//!
//! Pipeline per instance:
//!   1. Build the certificate-space LP:
//!      one equality row per atom index present (incl. the constant atom 0),
//!      plus the normalization row  sum_{strict} mu_j = 1,  with exact
//!      per-column scaling mu_j = s_j * lambda_j, s_j = max |coeff| of hyp j,
//!      so every FP entry lies in [-1, 1] (corpus coefficients reach 607
//!      decimal digits, far beyond f64).  If any nonzero scaled coefficient
//!      is not representable as a finite nonzero f64 (overflow/underflow/
//!      conversion failure), the instance routes directly to 'tiered'.
//!   2. Solve with a small in-crate dense FP64 phase-1 simplex under Bland's
//!      rule (artificial basis; smallest-index entering among columns with
//!      negative reduced cost; min-ratio exit with smallest-basic-index
//!      tie-break).  No external LP dependency.
//!   3. Take the FP support (largest coordinates first), exact-re-solve the
//!      equality system restricted to the support with tiered-rational
//!      Gauss-Jordan elimination in the *unscaled* lambda space, pinning free
//!      columns to 0; check nonnegativity (strictness is forced by the
//!      normalization row and re-checked by the exact verifier).  On failure
//!      grow the support to the next-largest FP coordinates — max 3 support
//!      attempts — then FALL BACK to the exact 'tiered' engine.
//!
//! SOUNDNESS: a certificate is only returned after it passes the exact
//! BigRational verifier (`verify::verify_cert`); a "no certificate" answer is
//! *never* produced from FP64 information — an FP infeasibility signal is
//! only a hint, and every non-FP-certified path runs the exact tiered engine
//! for the actual answer.

use crate::rat::{self, TRat};
use crate::tiered::produce_certificate_tiered;
use crate::types::{Hyp, Ineq};
use crate::verify::verify_cert;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::HashMap;

/// How the hybrid engine answered one instance (for honest reporting).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Route {
    /// Certificate found via FP support + exact repair (attempt 1..=3).
    Fp { attempts: u32 },
    /// Scaled LP not representable in finite nonzero f64 (or no strict hyp):
    /// routed directly to the exact tiered engine.
    TieredDirect,
    /// FP found a point but all support attempts failed exact repair; the
    /// exact tiered engine produced the answer.
    TieredRepairFail { attempts: u32 },
    /// FP phase-1 reported infeasible — treated as a hint only; the exact
    /// tiered engine produced the answer.
    TieredFpInfeasible,
    /// FP simplex hit the iteration cap / numeric trouble; exact tiered
    /// engine produced the answer.
    TieredFpStalled,
}

impl Route {
    /// Test-support predicate (exercised by the fallback soundness tests).
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn is_fallback(&self) -> bool {
        matches!(
            self,
            Route::TieredRepairFail { .. } | Route::TieredFpStalled
        )
    }
}

const MAX_ATTEMPTS: usize = 3;
const EPS_COST: f64 = 1e-9; // entering-variable reduced-cost threshold
const EPS_PIV: f64 = 1e-11; // pivot-element threshold in the ratio test
const TOL_INFEAS: f64 = 1e-7; // phase-1 residual above this = infeasible hint
/// Relative support thresholds (vs the largest FP coordinate); one entry per
/// attempt.  0.0 = every strictly positive coordinate (last resort).
const SUPPORT_TAUS: [f64; MAX_ATTEMPTS] = [1e-6, 1e-9, 0.0];

// ---------------------------------------------------------------------------
// Step 1: exact column scaling -> dense FP LP
// ---------------------------------------------------------------------------

struct FpLp {
    /// rows = one per atom present + 1 normalization row
    nrows: usize,
    ncols: usize,
    /// row-major nrows x ncols constraint matrix (dense; entries in [-1,1])
    a: Vec<f64>,
    /// rhs: all zeros except the normalization row = 1
    b: Vec<f64>,
}

/// Exact BigInt-ratio -> f64.  Returns None unless the result is finite and
/// faithfully nonzero (a nonzero exact value that underflows to 0.0 loses the
/// constraint structure, so we refuse it and route to tiered).
fn exact_ratio_to_f64(num: &BigInt, den: &BigInt) -> Option<f64> {
    debug_assert!(den.is_positive());
    if num.is_zero() {
        return Some(0.0);
    }
    // Fast path: both fit i64 with exact f64 division for small magnitudes.
    if let (Some(n), Some(d)) = (num.to_i64(), den.to_i64())
        && n.unsigned_abs() <= (1 << 53)
        && d.unsigned_abs() <= (1 << 53)
    {
        return Some(n as f64 / d as f64);
    }
    let v = BigRational::new(num.clone(), den.clone()).to_f64()?;
    if v.is_finite() && v != 0.0 {
        Some(v)
    } else {
        None
    }
}

/// Build the column-scaled certificate-space LP.  Returns None if there is no
/// strict hypothesis (no certificate can exist — but the caller still routes
/// through the exact engine) or if some scaled coefficient is not
/// representable.
fn build_fp_lp(hyps: &[Hyp]) -> Option<FpLp> {
    let n = hyps.len();
    let strict: Vec<usize> = (0..n).filter(|&j| hyps[j].ineq == Ineq::Lt).collect();
    if strict.is_empty() {
        return None;
    }
    // s_j = max |coeff| of hyp j (>= 1)
    let scales: Vec<BigInt> = hyps
        .iter()
        .map(|h| {
            h.coeffs
                .iter()
                .map(|(_, a)| a.abs())
                .max()
                .filter(|m| !m.is_zero())
                .unwrap_or_else(BigInt::one)
        })
        .collect();
    let mut atoms: Vec<usize> = hyps
        .iter()
        .flat_map(|h| h.coeffs.iter().map(|(v, _)| *v))
        .collect();
    atoms.sort_unstable();
    atoms.dedup();
    let arow: HashMap<usize, usize> = atoms.iter().enumerate().map(|(r, &a)| (a, r)).collect();
    let nrows = atoms.len() + 1;
    let mut a = vec![0.0f64; nrows * n];
    for (j, h) in hyps.iter().enumerate() {
        for (var, c) in &h.coeffs {
            if c.is_zero() {
                continue;
            }
            let v = exact_ratio_to_f64(c, &scales[j])?;
            a[arow[var] * n + j] += v;
        }
    }
    let norm = atoms.len();
    for &j in &strict {
        a[norm * n + j] = 1.0;
    }
    let mut b = vec![0.0f64; nrows];
    b[norm] = 1.0;
    Some(FpLp {
        nrows,
        ncols: n,
        a,
        b,
    })
}

// ---------------------------------------------------------------------------
// Step 2: dense FP64 phase-1 simplex, Bland's rule
// ---------------------------------------------------------------------------

enum FpResult {
    /// Feasible point mu >= 0 in scaled space.
    Feasible(Vec<f64>),
    /// Phase-1 optimum leaves artificial residual: infeasibility *hint*.
    Infeasible,
    /// Iteration cap or numeric breakdown: no usable FP information.
    Stalled,
}

fn solve_fp(lp: &FpLp) -> FpResult {
    let (r, n) = (lp.nrows, lp.ncols);
    let width = n + r + 1; // structural | artificial | rhs
    let mut t = vec![0.0f64; r * width];
    let mut basis: Vec<usize> = (n..n + r).collect();
    for i in 0..r {
        for j in 0..n {
            t[i * width + j] = lp.a[i * n + j];
        }
        t[i * width + n + i] = 1.0;
        t[i * width + width - 1] = lp.b[i]; // b >= 0 by construction
    }
    // Phase-1 objective: minimize sum of artificials.  Canonical reduced-cost
    // row: z[j] = -(sum_i T[i][j]) over structural columns.
    let mut z = vec![0.0f64; width];
    for j in 0..n {
        let mut s = 0.0;
        for i in 0..r {
            s += t[i * width + j];
        }
        z[j] = -s;
    }
    // Iteration cap: Bland's rule terminates in exact arithmetic; in FP a cap
    // guards against tolerance-induced stalls.  Hitting it is a counted
    // fallback, never an answer.
    let cap = 2000 + 10 * (n + r);
    let mut scratch = vec![0.0f64; width];
    for _ in 0..cap {
        // Bland entering: smallest structural index with negative reduced
        // cost (artificials are never allowed to re-enter).
        let Some(enter) = (0..n).find(|&j| z[j] < -EPS_COST) else {
            // Optimal: measure the artificial residual.
            let mut infeas = 0.0f64;
            for i in 0..r {
                if basis[i] >= n {
                    infeas += t[i * width + width - 1].abs();
                }
            }
            if infeas > TOL_INFEAS {
                return FpResult::Infeasible;
            }
            let mut mu = vec![0.0f64; n];
            for i in 0..r {
                if basis[i] < n {
                    mu[basis[i]] = t[i * width + width - 1].max(0.0);
                }
            }
            return FpResult::Feasible(mu);
        };
        // Bland exiting: min ratio, ties by smallest basic index.
        let mut exit: Option<(f64, usize, usize)> = None; // (ratio, basis idx, row)
        for i in 0..r {
            let piv = t[i * width + enter];
            if piv > EPS_PIV {
                let ratio = t[i * width + width - 1] / piv;
                let better = match exit {
                    None => true,
                    Some((br, bb, _)) => {
                        ratio < br - 1e-12 || ((ratio - br).abs() <= 1e-12 && basis[i] < bb)
                    }
                };
                if better {
                    exit = Some((ratio, basis[i], i));
                }
            }
        }
        let Some((_, _, prow)) = exit else {
            // Phase-1 objective is bounded below by 0, so "unbounded" here
            // can only be numeric breakdown.
            return FpResult::Stalled;
        };
        // Pivot.
        let pv = t[prow * width + enter];
        scratch.copy_from_slice(&t[prow * width..(prow + 1) * width]);
        for v in scratch.iter_mut() {
            *v /= pv;
        }
        t[prow * width..(prow + 1) * width].copy_from_slice(&scratch);
        for i in 0..r {
            if i == prow {
                continue;
            }
            let f = t[i * width + enter];
            if f != 0.0 {
                for j in 0..width {
                    t[i * width + j] -= f * scratch[j];
                }
            }
        }
        let f = z[enter];
        if f != 0.0 {
            for j in 0..width {
                z[j] -= f * scratch[j];
            }
        }
        basis[prow] = enter;
    }
    FpResult::Stalled
}

// ---------------------------------------------------------------------------
// Step 3: support identification + exact tiered-rational repair
// ---------------------------------------------------------------------------

/// Exact Gauss-Jordan (tiered rationals) on the equality system restricted to
/// `support` columns in *unscaled* lambda space; free columns pinned to 0.
/// `support` must be ordered by descending FP magnitude so that the
/// large-magnitude (likely true-support) columns become basic and the
/// small/noise columns stay free at 0.  Returns a certificate candidate iff
/// the restricted system is consistent with a nonnegative solution; a
/// tampered or wrong support yields an inconsistent system or negative
/// coordinates and is rejected (None).
pub fn exact_repair(hyps: &[Hyp], support: &[usize]) -> Option<Vec<(usize, BigInt)>> {
    let m = support.len();
    let strict_cols: Vec<usize> = (0..m)
        .filter(|&k| hyps[support[k]].ineq == Ineq::Lt)
        .collect();
    if strict_cols.is_empty() {
        return None;
    }
    // Rows: one per atom touched by the support + the normalization row
    // sum_{strict in support} lambda = 1.  Width m+1 (last = rhs).
    let mut atom_rows: HashMap<usize, Vec<TRat>> = HashMap::new();
    for (k, &j) in support.iter().enumerate() {
        for (var, c) in &hyps[j].coeffs {
            if c.is_zero() {
                continue;
            }
            let row = atom_rows
                .entry(*var)
                .or_insert_with(|| vec![TRat::zero(); m + 1]);
            row[k] = row[k].add(&TRat::from_bigint(c));
        }
    }
    let mut mat: Vec<Vec<TRat>> = atom_rows.into_values().collect();
    let mut norm = vec![TRat::zero(); m + 1];
    for &k in &strict_cols {
        norm[k] = TRat::one();
    }
    norm[m] = TRat::one();
    mat.push(norm);

    let nrows = mat.len();
    let mut pivots: Vec<(usize, usize)> = Vec::new();
    let mut prow = 0usize;
    for col in 0..m {
        let Some(pr) = (prow..nrows).find(|&r| !mat[r][col].is_zero()) else {
            continue;
        };
        mat.swap(prow, pr);
        let pv = mat[prow][col].clone();
        for e in mat[prow].iter_mut() {
            if !e.is_zero() {
                *e = e.div(&pv);
            }
        }
        for r2 in 0..nrows {
            if r2 == prow || mat[r2][col].is_zero() {
                continue;
            }
            let f = mat[r2][col].clone();
            // index loop on purpose: reads mat[prow] while writing mat[r2]
            #[allow(clippy::needless_range_loop)]
            for c2 in 0..=m {
                if !mat[prow][c2].is_zero() {
                    let delta = f.mul(&mat[prow][c2]);
                    mat[r2][c2] = mat[r2][c2].sub(&delta);
                }
            }
        }
        pivots.push((prow, col));
        prow += 1;
        if prow == nrows {
            break;
        }
    }
    // Inconsistent restricted system (e.g. tampered/short support) -> reject.
    if mat[prow..nrows].iter().any(|row| !row[m].is_zero()) {
        return None;
    }
    let mut sol = vec![TRat::zero(); m];
    for &(r, c) in &pivots {
        sol[c] = mat[r][m].clone();
    }
    if sol.iter().any(|v| v.is_negative()) {
        return None;
    }
    // Clear denominators; keep positive entries mapped back to hyp indices.
    let vals: Vec<BigRational> = sol.iter().map(|v| v.to_bigrational()).collect();
    let mut den = BigInt::one();
    for v in &vals {
        den = den.lcm(v.denom());
    }
    let den = BigRational::from(den);
    let mut cert: Vec<(usize, BigInt)> = Vec::new();
    for (k, v) in vals.into_iter().enumerate() {
        let scaled = v * &den;
        debug_assert!(scaled.is_integer());
        let w = scaled.to_integer();
        if w.is_positive() {
            cert.push((support[k], w));
        }
    }
    cert.sort_unstable_by_key(|&(j, _)| j);
    if cert.is_empty() { None } else { Some(cert) }
}

/// Support for attempt `att`: coordinates above SUPPORT_TAUS[att] * max(mu),
/// ordered by descending magnitude (ties by index), always containing at
/// least one strict column (the largest-mu strict one).
fn support_for(hyps: &[Hyp], mu: &[f64], att: usize) -> Vec<usize> {
    let mu_max = mu.iter().cloned().fold(0.0f64, f64::max);
    let tau = SUPPORT_TAUS[att] * mu_max;
    let mut sup: Vec<usize> = (0..mu.len())
        .filter(|&j| mu[j] > tau && mu[j] > 0.0)
        .collect();
    if !sup.iter().any(|&j| hyps[j].ineq == Ineq::Lt)
        && let Some(best) = (0..mu.len())
            .filter(|&j| hyps[j].ineq == Ineq::Lt)
            .max_by(|&a, &b| mu[a].total_cmp(&mu[b]))
    {
        sup.push(best);
    }
    sup.sort_unstable_by(|&a, &b| mu[b].total_cmp(&mu[a]).then(a.cmp(&b)));
    sup
}

// ---------------------------------------------------------------------------
// Engine entry point
// ---------------------------------------------------------------------------

pub fn produce_certificate_hybrid(
    hyps: &[Hyp],
    max_var: usize,
) -> (Option<Vec<(usize, BigInt)>>, Route) {
    let result = (|| {
        let Some(lp) = build_fp_lp(hyps) else {
            return (
                produce_certificate_tiered(hyps, max_var),
                Route::TieredDirect,
            );
        };
        match solve_fp(&lp) {
            FpResult::Feasible(mu) => {
                let mut tried: Vec<Vec<usize>> = Vec::new();
                let mut attempts = 0u32;
                for att in 0..MAX_ATTEMPTS {
                    let sup = support_for(hyps, &mu, att);
                    if sup.is_empty() || tried.contains(&sup) {
                        continue;
                    }
                    attempts += 1;
                    if let Some(cert) = exact_repair(hyps, &sup) {
                        // SOUNDNESS GATE: exact BigRational verifier.
                        if verify_cert(hyps, &cert) {
                            return (Some(cert), Route::Fp { attempts });
                        }
                    }
                    tried.push(sup);
                }
                (
                    produce_certificate_tiered(hyps, max_var),
                    Route::TieredRepairFail { attempts },
                )
            }
            // FP infeasibility is only a hint: the exact engine answers.
            FpResult::Infeasible => (
                produce_certificate_tiered(hyps, max_var),
                Route::TieredFpInfeasible,
            ),
            FpResult::Stalled => (
                produce_certificate_tiered(hyps, max_var),
                Route::TieredFpStalled,
            ),
        }
    })();
    rat::flush_tls();
    result
}
