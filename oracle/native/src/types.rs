//! Problem types and parsing, shared by serve-mode requests (farkas-oracled)
//! and corpus JSONL rows (farkas-bench).
//!
//! The request path (`parse_request`/`parse_hyps`) must never panic: the
//! daemon answers input from outside the process boundary (see the fuzz
//! suite in tests/daemon_fuzz.rs).
//!
//! Each corpus `ty:"oracle"` row records one call to Mathlib's linarith
//! oracle (`CertificateOracle.produceCertificate hyps maxVar`).  A hypothesis
//! is a Mathlib `Linarith.Comp`, i.e. a comparison `e R 0` where `e` is a
//! sparse linear form over atom indices `0..=maxVar` and — crucially — **atom
//! index 0 is reserved for the constant term** (the coefficient of `1`); see
//! Mathlib/Tactic/Linarith/Datatypes.lean.  Integer coefficients in the corpus
//! can be hundreds of digits (nlinarith products), so we parse them as BigInt
//! via serde_json's `arbitrary_precision` feature.

use num_bigint::BigInt;
use serde_json::Value;
use std::str::FromStr;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ineq {
    Eq,
    Le,
    Lt,
}

#[derive(Clone, Debug)]
pub struct Hyp {
    pub ineq: Ineq,
    /// Sparse linear form: (atom index, coefficient). Index 0 = constant.
    pub coeffs: Vec<(usize, BigInt)>,
}

#[derive(Clone, Debug)]
pub struct Instance {
    pub src: String,
    pub call: u64,
    pub max_var: usize,
    pub hyps: Vec<Hyp>,
    /// Mathlib (Lean interpreter) oracle time in nanoseconds.
    pub ns: u128,
    /// Did Mathlib's oracle find a certificate?
    pub ok: bool,
    /// Mathlib's certificate, if any: hypIdx -> positive coefficient.
    pub cert: Option<Vec<(usize, BigInt)>>,
}

impl Instance {
    /// Total number of nonzeros across all hypotheses' linear forms.
    pub fn nnz(&self) -> usize {
        self.hyps.iter().map(|h| h.coeffs.len()).sum()
    }
}

fn big(v: &Value) -> Option<BigInt> {
    // With arbitrary_precision, Number::to_string reproduces the exact digits.
    match v {
        Value::Number(n) => BigInt::from_str(&n.to_string()).ok(),
        _ => None,
    }
}

fn usz(v: &Value) -> Option<usize> {
    usize::try_from(v.as_u64()?).ok()
}

/// Parse the `hyps` array shared by corpus rows and serve-mode requests.
/// Total on any malformed shape: the daemon answers requests from outside the
/// process boundary, so this path must never panic (a panic here would kill
/// the daemon and put the Lean client into a respawn/crash loop).
pub fn parse_hyps(v: &Value) -> Option<Vec<Hyp>> {
    v.as_array()?
        .iter()
        .map(|h| {
            let a = h.as_array()?;
            let ineq = match a.first()?.as_str()? {
                "eq" => Ineq::Eq,
                "le" => Ineq::Le,
                "lt" => Ineq::Lt,
                _ => return None,
            };
            let coeffs = a
                .get(1)?
                .as_array()?
                .iter()
                .map(|p| {
                    let p = p.as_array()?;
                    Some((usz(p.first()?)?, big(p.get(1)?)?))
                })
                .collect::<Option<Vec<_>>>()?;
            Some(Hyp { ineq, coeffs })
        })
        .collect()
}

/// Parse a serve-mode request line: `{"maxVar":M,"hyps":[...]}`.
pub fn parse_request(line: &str) -> Option<(usize, Vec<Hyp>)> {
    let v: Value = serde_json::from_str(line.trim()).ok()?;
    let max_var = usz(v.get("maxVar")?)?;
    let hyps = parse_hyps(v.get("hyps")?)?;
    Some((max_var, hyps))
}

/// Parse one JSONL line; returns None for non-oracle rows (e.g. ty:"tactic").
pub fn parse_line(line: &str) -> Option<Instance> {
    let line = line.trim();
    if line.is_empty() {
        return None;
    }
    let v: Value = serde_json::from_str(line).ok()?;
    if v.get("ty")?.as_str()? != "oracle" {
        return None;
    }
    let hyps = parse_hyps(&v["hyps"])?;
    let cert = match &v["cert"] {
        Value::Null => None,
        Value::Array(entries) => Some(
            entries
                .iter()
                .map(|p| {
                    let p = p.as_array()?;
                    Some((usz(p.first()?)?, big(p.get(1)?)?))
                })
                .collect::<Option<Vec<_>>>()?,
        ),
        _ => return None,
    };
    Some(Instance {
        src: v["src"].as_str().unwrap_or("").to_string(),
        call: v["call"].as_u64().unwrap_or(0),
        max_var: usz(&v["maxVar"])?,
        hyps,
        ns: v["ns"].as_u64().unwrap_or(0) as u128,
        ok: v["ok"].as_bool().unwrap_or(false),
        cert,
    })
}

/// Load every oracle instance from all `oracle.*.jsonl` files in a directory.
pub fn load_corpus(dir: &std::path::Path) -> std::io::Result<Vec<Instance>> {
    let mut files: Vec<_> = std::fs::read_dir(dir)?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .map(|n| n.starts_with("oracle.") && n.ends_with(".jsonl"))
                .unwrap_or(false)
        })
        .collect();
    files.sort();
    let mut out = Vec::new();
    for f in files {
        let text = std::fs::read_to_string(&f)?;
        out.extend(text.lines().filter_map(parse_line));
    }
    Ok(out)
}
