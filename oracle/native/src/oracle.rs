//! Exact-rational certificate search: a faithful Rust port of Mathlib's
//! default linarith oracle (`CertificateOracle.simplexAlgorithmSparse`,
//! Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/*, v4.31.0).
//!
//! Problem: given the (maxVar+1) x nHyps matrix `A` of hypothesis linear
//! forms (row 0 = the constant atom) and the set of strict (`lt`) hypothesis
//! indices, find `v >= 0` with `A v = 0` and `sum_{i in strict} v_i > 0`.
//!
//! Algorithm choice: **Gauss-seeded simplex with Bland's rule**, exactly like
//! Mathlib (`stateLP` -> `Gauss.getTableau` -> `runSimplexAlgorithm`), rather
//! than a generic phase-1 simplex with artificial variables.  Justification:
//! (a) the homogenized LP `stateLP` builds (auxiliary objective `f`, slack
//! `z` with x1+...+xm+z = y, homogenized unit `y`) is *feasible by
//! construction* at the point extracted by Gaussian elimination — the greedy
//! left-to-right pivot order makes `f` basic in row 0, `z` basic in row 1 and
//! leaves `y` as the last free column, so the initial basic values (the `y`
//! column) are nonnegative and no phase-1 is needed; (b) porting the exact
//! pivot rules (Bland's rule: smallest original index entering, min-ratio
//! with smallest-index tie-break exiting) makes the Rust oracle
//! decision-for-decision equivalent to the Mathlib baseline we benchmark
//! against, so the comparison measures implementation overhead (interpreted
//! Lean vs native) and not algorithmic luck.  Bland's rule guarantees
//! termination; all arithmetic is exact BigRational.

use crate::types::{Hyp, Ineq};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::HashMap;

pub type Rat = BigRational;

/// Sparse row-major matrix, mirroring Mathlib's `SparseMatrix`
/// (`Array (Std.HashMap Nat Rat)`). Absent entry = 0; entries are nonzero.
#[derive(Clone, Debug)]
struct SparseMat {
    rows: Vec<HashMap<usize, Rat>>,
}

impl SparseMat {
    fn new(n_rows: usize) -> Self {
        SparseMat {
            rows: vec![HashMap::new(); n_rows],
        }
    }

    fn get(&self, i: usize, j: usize) -> Rat {
        self.rows[i].get(&j).cloned().unwrap_or_else(Rat::zero)
    }

    fn is_zero_at(&self, i: usize, j: usize) -> bool {
        !self.rows[i].contains_key(&j)
    }

    fn set(&mut self, i: usize, j: usize, v: Rat) {
        if v.is_zero() {
            self.rows[i].remove(&j);
        } else {
            self.rows[i].insert(j, v);
        }
    }

    fn swap_rows(&mut self, i: usize, j: usize) {
        self.rows.swap(i, j);
    }

    /// row[i] /= coef  (coef != 0)
    fn divide_row(&mut self, i: usize, coef: &Rat) {
        for v in self.rows[i].values_mut() {
            *v /= coef;
        }
    }

    /// row[dst] -= coef * row[src]
    fn subtract_row(&mut self, src: usize, dst: usize, coef: &Rat) {
        if coef.is_zero() {
            return;
        }
        let src_row: Vec<(usize, Rat)> = self.rows[src]
            .iter()
            .map(|(j, v)| (*j, v.clone()))
            .collect();
        for (j, v) in src_row {
            let delta = &v * coef;
            match self.rows[dst].get_mut(&j) {
                Some(e) => {
                    *e -= delta;
                    if e.is_zero() {
                        self.rows[dst].remove(&j);
                    }
                }
                None => {
                    self.rows[dst].insert(j, -delta);
                }
            }
        }
    }
}

/// Mathlib's `Tableau`: basic variables (one per row, `basic[i]` is the
/// original column index), free variables (`free[j]`), and `mat` such that
/// `basic[i] = sum_j mat[i][j] * free[j]`.
struct Tableau {
    basic: Vec<usize>,
    free: Vec<usize>,
    mat: SparseMat,
}

/// Port of `stateLP`: (n+2) x (m+3) matrix. Columns: 0 = objective `f`,
/// 1 = slack `z`, 2..m+2 = the certificate coordinates, m+2 = unit `y`.
/// Row 0: -f + sum_{strict} x = 0. Row 1: z - y + sum x = 0. Rows 2..: A.
fn state_lp(hyps: &[Hyp], max_var: usize) -> SparseMat {
    let n = max_var + 1;
    let m = hyps.len();
    let mut b = SparseMat::new(n + 2);
    b.set(0, 0, -Rat::one());
    for (idx, h) in hyps.iter().enumerate() {
        if h.ineq == Ineq::Lt {
            b.set(0, idx + 2, Rat::one());
        }
    }
    b.set(1, 1, Rat::one());
    b.set(1, m + 2, -Rat::one());
    for i in 0..m {
        b.set(1, i + 2, Rat::one());
    }
    for (idx, h) in hyps.iter().enumerate() {
        for (var, c) in &h.coeffs {
            if !c.is_zero() {
                // accumulate: duplicate atom indices in one hypothesis are
                // additive (matching verify_cert), not last-wins
                let cur = b.get(var + 2, idx + 2);
                b.set(var + 2, idx + 2, cur + Rat::from(c.clone()));
            }
        }
    }
    b
}

/// Port of `Gauss.getTableau`: greedy left-to-right Gaussian elimination
/// splitting columns into basic and free; returns the tableau expressing the
/// basic variables through the free ones (entries negated, pivot columns
/// dropped).
fn gauss_tableau(mut mat: SparseMat, n: usize, m: usize) -> Tableau {
    let mut free: Vec<usize> = Vec::new();
    let mut basic: Vec<usize> = Vec::new();
    let mut row = 0usize;
    let mut col = 0usize;
    while row < n && col < m {
        let pivot = (row..n).find(|&i| !mat.is_zero_at(i, col));
        let Some(row_to_swap) = pivot else {
            free.push(col);
            col += 1;
            continue;
        };
        mat.swap_rows(row, row_to_swap);
        let d = mat.get(row, col);
        mat.divide_row(row, &d);
        for i in 0..n {
            if i == row {
                continue;
            }
            let coef = mat.get(i, col);
            if !coef.is_zero() {
                mat.subtract_row(row, i, &coef);
            }
        }
        basic.push(col);
        row += 1;
        col += 1;
    }
    for j in col..m {
        free.push(j);
    }
    let free_idx: HashMap<usize, usize> = free.iter().enumerate().map(|(k, &j)| (j, k)).collect();
    let mut ans = SparseMat::new(basic.len());
    for (i, r) in mat.rows.iter().enumerate().take(basic.len()) {
        for (j, v) in r {
            if *j == basic[i] {
                continue;
            }
            ans.set(i, free_idx[j], -v.clone());
        }
    }
    Tableau {
        basic,
        free,
        mat: ans,
    }
}

/// Port of `doPivotOperation`.
fn do_pivot(t: &mut Tableau, exit_idx: usize, enter_idx: usize) {
    let intersect = t.mat.get(exit_idx, enter_idx);
    for i in 0..t.basic.len() {
        if i == exit_idx {
            continue;
        }
        let coef = t.mat.get(i, enter_idx) / &intersect;
        if !coef.is_zero() {
            t.mat.subtract_row(exit_idx, i, &coef);
        }
        t.mat.set(i, enter_idx, coef);
    }
    t.mat.set(exit_idx, enter_idx, -Rat::one());
    t.mat.divide_row(exit_idx, &-intersect);
    std::mem::swap(&mut t.basic[exit_idx], &mut t.free[enter_idx]);
}

/// Port of `checkSuccess`: objective positive and all basic values (last
/// column, i.e. the coefficient of the free unit `y`) nonnegative.
fn check_success(t: &Tableau) -> bool {
    let last = t.free.len() - 1;
    t.mat.get(0, last).is_positive()
        && (0..t.basic.len()).all(|i| !t.mat.get(i, last).is_negative())
}

/// Port of `chooseEnteringVar` (Bland: smallest original index among free
/// columns with positive objective coefficient; `y` — the last free column —
/// is excluded). Returns None <=> infeasible.
fn choose_entering(t: &Tableau) -> Option<usize> {
    let mut enter: Option<usize> = None;
    let mut min_idx = 0usize;
    for i in 0..t.free.len() - 1 {
        if t.mat.get(0, i).is_positive() && (enter.is_none() || t.free[i] < min_idx) {
            enter = Some(i);
            min_idx = t.free[i];
        }
    }
    enter
}

/// Port of `chooseExitingVar` (min ratio, ties by smallest basic index; row 0
/// — the objective `f` — never exits). Mathlib asserts a candidate always
/// exists because the LP is bounded; we surface failure instead of panicking.
fn choose_exiting(t: &Tableau, enter_idx: usize) -> Option<usize> {
    let last = t.free.len() - 1;
    let mut exit: Option<usize> = None;
    let mut min_coef = Rat::zero();
    let mut min_idx = 0usize;
    for i in 1..t.basic.len() {
        let a = t.mat.get(i, enter_idx);
        if !a.is_negative() {
            continue;
        }
        let coef = -t.mat.get(i, last) / a;
        if exit.is_none() || coef < min_coef || (coef == min_coef && t.basic[i] < min_idx) {
            exit = Some(i);
            min_coef = coef;
            min_idx = t.basic[i];
        }
    }
    exit
}

/// Port of `runSimplexAlgorithm` + `extractSolution` + `postprocess`.
/// Returns the certificate as (hypIdx, positive integer coefficient) pairs,
/// or None if no certificate exists (the hypotheses are satisfiable over Q,
/// or no strict combination sums to zero).
pub fn produce_certificate(hyps: &[Hyp], max_var: usize) -> Option<Vec<(usize, BigInt)>> {
    let m = hyps.len();
    if m == 0 {
        return None;
    }
    let b = state_lp(hyps, max_var);
    let mut t = gauss_tableau(b, max_var + 3, m + 3);
    if t.basic.is_empty() || t.free.is_empty() {
        return None;
    }
    // By construction f = basic[0] and y = free[last] (see module comment);
    // bail out defensively if the invariant is ever violated.
    if t.basic[0] != 0 || *t.free.last().unwrap() != m + 2 {
        return None;
    }
    while !check_success(&t) {
        let enter = choose_entering(&t)?;
        let exit = choose_exiting(&t, enter)?;
        do_pivot(&mut t, exit, enter);
    }
    // extractSolution: free vars are 0 (except y = 1), basic vars take the
    // value in the y column. Only columns 2..m+2 are certificate coordinates.
    // (Mathlib's extractSolution writes `ans[basic[i] - 2]` with Nat
    // subtraction, which would misfile `z` (column 1) into slot 0 if `z` is
    // basic; we index correctly instead — our result is self-verified.)
    let last = t.free.len() - 1;
    let mut vec: Vec<Rat> = vec![Rat::zero(); m];
    for i in 1..t.basic.len() {
        let c = t.basic[i];
        if (2..m + 2).contains(&c) {
            vec[c - 2] = t.mat.get(i, last);
        }
    }
    // postprocess: clear denominators with the lcm, keep nonzero entries.
    let mut den = BigInt::one();
    for v in &vec {
        den = den.lcm(v.denom());
    }
    let den = Rat::from(den);
    let mut cert: Vec<(usize, BigInt)> = Vec::new();
    for (idx, v) in vec.into_iter().enumerate() {
        let scaled = v * &den;
        debug_assert!(scaled.is_integer());
        let n = scaled.to_integer();
        if !n.is_zero() {
            cert.push((idx, n));
        }
    }
    if cert.is_empty() {
        return None;
    }
    Some(cert)
}
