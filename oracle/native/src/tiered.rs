//! Engine "tiered": the *same* Gauss-seeded Bland simplex as the faithful
//! engine (`oracle.rs`, itself a decision-for-decision port of Mathlib's
//! `linarith` oracle), with the exact arithmetic swapped from BigRational to
//! the tiered representation in `rat.rs` (i64 -> i128 -> BigRational with
//! checked promotion).  Pivot rules, tie-breaks and the extraction /
//! postprocess steps are identical, so this engine makes exactly the same
//! pivot decisions and produces the same certificates as the faithful engine;
//! only the cost of each exact ring op changes.

use crate::rat::{self, TRat};
use crate::types::{Hyp, Ineq};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::HashMap;

/// Sparse row-major matrix over TRat (absent entry = 0; entries nonzero).
#[derive(Clone, Debug)]
struct SparseMat {
    rows: Vec<HashMap<usize, TRat>>,
}

impl SparseMat {
    fn new(n_rows: usize) -> Self {
        SparseMat {
            rows: vec![HashMap::new(); n_rows],
        }
    }

    fn get(&self, i: usize, j: usize) -> TRat {
        self.rows[i].get(&j).cloned().unwrap_or_else(TRat::zero)
    }

    fn is_zero_at(&self, i: usize, j: usize) -> bool {
        !self.rows[i].contains_key(&j)
    }

    fn set(&mut self, i: usize, j: usize, v: TRat) {
        if v.is_zero() {
            self.rows[i].remove(&j);
        } else {
            self.rows[i].insert(j, v);
        }
    }

    fn swap_rows(&mut self, i: usize, j: usize) {
        self.rows.swap(i, j);
    }

    fn divide_row(&mut self, i: usize, coef: &TRat) {
        for v in self.rows[i].values_mut() {
            *v = v.div(coef);
        }
    }

    /// row[dst] -= coef * row[src]
    fn subtract_row(&mut self, src: usize, dst: usize, coef: &TRat) {
        if coef.is_zero() {
            return;
        }
        let src_row: Vec<(usize, TRat)> = self.rows[src]
            .iter()
            .map(|(j, v)| (*j, v.clone()))
            .collect();
        for (j, v) in src_row {
            let delta = v.mul(coef);
            match self.rows[dst].get_mut(&j) {
                Some(e) => {
                    let nv = e.sub(&delta);
                    if nv.is_zero() {
                        self.rows[dst].remove(&j);
                    } else {
                        *e = nv;
                    }
                }
                None => {
                    self.rows[dst].insert(j, delta.neg());
                }
            }
        }
    }
}

struct Tableau {
    basic: Vec<usize>,
    free: Vec<usize>,
    mat: SparseMat,
}

/// Identical layout to the faithful `state_lp` (see oracle.rs).
fn state_lp(hyps: &[Hyp], max_var: usize) -> SparseMat {
    let m = hyps.len();
    let mut b = SparseMat::new(max_var + 3);
    b.set(0, 0, TRat::one().neg());
    for (idx, h) in hyps.iter().enumerate() {
        if h.ineq == Ineq::Lt {
            b.set(0, idx + 2, TRat::one());
        }
    }
    b.set(1, 1, TRat::one());
    b.set(1, m + 2, TRat::one().neg());
    for i in 0..m {
        b.set(1, i + 2, TRat::one());
    }
    for (idx, h) in hyps.iter().enumerate() {
        for (var, c) in &h.coeffs {
            if !c.is_zero() {
                // accumulate: duplicate atom indices in one hypothesis are
                // additive (matching verify_cert), not last-wins
                let cur = b.get(var + 2, idx + 2);
                b.set(var + 2, idx + 2, cur.add(&TRat::from_bigint(c)));
            }
        }
    }
    b
}

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
            ans.set(i, free_idx[j], v.neg());
        }
    }
    Tableau {
        basic,
        free,
        mat: ans,
    }
}

fn do_pivot(t: &mut Tableau, exit_idx: usize, enter_idx: usize) {
    let intersect = t.mat.get(exit_idx, enter_idx);
    for i in 0..t.basic.len() {
        if i == exit_idx {
            continue;
        }
        let coef = t.mat.get(i, enter_idx).div(&intersect);
        if !coef.is_zero() {
            t.mat.subtract_row(exit_idx, i, &coef);
        }
        t.mat.set(i, enter_idx, coef);
    }
    t.mat.set(exit_idx, enter_idx, TRat::one().neg());
    t.mat.divide_row(exit_idx, &intersect.neg());
    std::mem::swap(&mut t.basic[exit_idx], &mut t.free[enter_idx]);
}

fn check_success(t: &Tableau) -> bool {
    let last = t.free.len() - 1;
    t.mat.get(0, last).is_positive()
        && (0..t.basic.len()).all(|i| !t.mat.get(i, last).is_negative())
}

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

fn choose_exiting(t: &Tableau, enter_idx: usize) -> Option<usize> {
    let last = t.free.len() - 1;
    let mut exit: Option<usize> = None;
    let mut min_coef = TRat::zero();
    let mut min_idx = 0usize;
    for i in 1..t.basic.len() {
        let a = t.mat.get(i, enter_idx);
        if !a.is_negative() {
            continue;
        }
        let coef = t.mat.get(i, last).neg().div(&a);
        if exit.is_none() || coef < min_coef || (coef == min_coef && t.basic[i] < min_idx) {
            exit = Some(i);
            min_coef = coef;
            min_idx = t.basic[i];
        }
    }
    exit
}

fn produce_inner(hyps: &[Hyp], max_var: usize) -> Option<Vec<(usize, BigInt)>> {
    let m = hyps.len();
    if m == 0 {
        return None;
    }
    let b = state_lp(hyps, max_var);
    let mut t = gauss_tableau(b, max_var + 3, m + 3);
    if t.basic.is_empty() || t.free.is_empty() {
        return None;
    }
    if t.basic[0] != 0 || *t.free.last().unwrap() != m + 2 {
        return None;
    }
    while !check_success(&t) {
        let enter = choose_entering(&t)?;
        let exit = choose_exiting(&t, enter)?;
        do_pivot(&mut t, exit, enter);
    }
    let last = t.free.len() - 1;
    let mut vec: Vec<BigRational> = vec![BigRational::zero(); m];
    for i in 1..t.basic.len() {
        let c = t.basic[i];
        if (2..m + 2).contains(&c) {
            vec[c - 2] = t.mat.get(i, last).to_bigrational();
        }
    }
    rationals_to_cert(vec)
}

/// Clear denominators with the lcm and keep the nonzero entries (identical to
/// the faithful postprocess).
pub fn rationals_to_cert(vec: Vec<BigRational>) -> Option<Vec<(usize, BigInt)>> {
    let mut den = BigInt::one();
    for v in &vec {
        den = den.lcm(v.denom());
    }
    let den = BigRational::from(den);
    let mut cert: Vec<(usize, BigInt)> = Vec::new();
    for (idx, v) in vec.into_iter().enumerate() {
        let scaled = v * &den;
        debug_assert!(scaled.is_integer());
        let n = scaled.to_integer();
        if !n.is_zero() {
            cert.push((idx, n));
        }
    }
    if cert.is_empty() { None } else { Some(cert) }
}

/// Tiered-exact certificate search.  Same algorithm and answers as the
/// faithful engine; flushes the tier counters once per instance.
pub fn produce_certificate_tiered(hyps: &[Hyp], max_var: usize) -> Option<Vec<(usize, BigInt)>> {
    let r = produce_inner(hyps, max_var);
    rat::flush_tls();
    r
}
