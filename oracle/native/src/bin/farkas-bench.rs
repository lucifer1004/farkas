//! farkas-bench: exact CPU oracle engines benchmarked over a corpus
//! problem, benchmarked against Mathlib's Lean-interpreter times recorded in
//! the corpus.
//!
//! Usage:
//!   farkas-bench [--engine faithful|tiered|hybrid|all] [--corpus DIR]
//!                        [--bench] [--par] [--report FILE]
//!
//!   Engines (default: hybrid):
//!     faithful — BigRational port of Mathlib's simplex oracle (unchanged
//!                baseline engine);
//!     tiered   — same algorithm over tiered i64/i128/BigRational rationals;
//!     hybrid   — FP64 basis identification + exact repair, falling back to
//!                'tiered' (soundness: certs pass the exact verifier, and a
//!                'no certificate' answer only ever comes from an exact
//!                engine);
//!     all      — run every engine and write the combined comparison report.
//!
//!   default : run the corpus with the selected engine(s), self-check every
//!             produced certificate, print the agreement summary.
//!   --bench : additionally write the timing comparison report.
//!   --par   : additionally measure 16-thread rayon throughput per engine.

use farkas_core::hybrid::{Route, produce_certificate_hybrid};
use farkas_core::oracle::produce_certificate;
use farkas_core::rat;
use farkas_core::tiered::produce_certificate_tiered;
use farkas_core::types::{Instance, load_corpus};
use farkas_core::verify::verify_cert;
use std::fmt::Write as _;
use std::time::Instant;

const PAR_THREADS: usize = 16;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Engine {
    Faithful,
    Tiered,
    Hybrid,
}

impl Engine {
    fn name(self) -> &'static str {
        match self {
            Engine::Faithful => "faithful",
            Engine::Tiered => "tiered",
            Engine::Hybrid => "hybrid",
        }
    }
}

fn solve(
    engine: Engine,
    inst: &Instance,
) -> (Option<Vec<(usize, num_bigint::BigInt)>>, Option<Route>) {
    match engine {
        Engine::Faithful => (produce_certificate(&inst.hyps, inst.max_var), None),
        Engine::Tiered => (produce_certificate_tiered(&inst.hyps, inst.max_var), None),
        Engine::Hybrid => {
            let (c, r) = produce_certificate_hybrid(&inst.hyps, inst.max_var);
            (c, Some(r))
        }
    }
}

struct RowResult {
    src: String,
    call: u64,
    nnz: usize,
    corpus_ns: u128,
    native_ns: u128,
    corpus_ok: bool,
    native_ok: bool,
    self_check_ok: bool, // true iff no cert produced or produced cert verifies
    route: Option<Route>,
}

struct EngineRun {
    engine: Engine,
    rows: Vec<RowResult>,
    counters: rat::Counters,
    par_line: String,
}

fn run_single(insts: &[Instance], engine: Engine) -> (Vec<RowResult>, rat::Counters) {
    rat::reset_counters();
    let rows = insts
        .iter()
        .map(|inst| {
            let t0 = Instant::now();
            let (cert, route) = solve(engine, inst);
            let native_ns = t0.elapsed().as_nanos();
            let (native_ok, self_check_ok) = match &cert {
                Some(c) => {
                    let v = verify_cert(&inst.hyps, c);
                    (v, v)
                }
                None => (false, true),
            };
            RowResult {
                src: inst.src.clone(),
                call: inst.call,
                nnz: inst.nnz(),
                corpus_ns: inst.ns,
                native_ns,
                corpus_ok: inst.ok,
                native_ok,
                self_check_ok,
                route,
            }
        })
        .collect();
    (rows, rat::counters())
}

fn run_par(insts: &[Instance], engine: Engine) -> String {
    use rayon::prelude::*;
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(PAR_THREADS)
        .build()
        .expect("rayon pool");
    let t0 = Instant::now();
    let certs: usize = pool.install(|| {
        insts
            .par_iter()
            .map(|inst| match solve(engine, inst).0 {
                Some(c) => verify_cert(&inst.hyps, &c) as usize,
                None => 0,
            })
            .sum()
    });
    let wall = t0.elapsed().as_secs_f64();
    format!(
        "{:>9}: {} instances in {:>7.3} s wall -> {:>5.0} instances/sec, {} certs -> {:>5.0} certs/sec",
        engine.name(),
        insts.len(),
        wall,
        insts.len() as f64 / wall,
        certs,
        certs as f64 / wall
    )
}

// ---------------------------------------------------------------------------
// Stats helpers
// ---------------------------------------------------------------------------

fn median(mut v: Vec<f64>) -> f64 {
    if v.is_empty() {
        return f64::NAN;
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = v.len();
    if n % 2 == 1 {
        v[n / 2]
    } else {
        0.5 * (v[n / 2 - 1] + v[n / 2])
    }
}

/// p in (0,1]; nearest-rank percentile.
fn percentile(mut v: Vec<f64>, p: f64) -> f64 {
    if v.is_empty() {
        return f64::NAN;
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let idx = ((v.len() as f64 * p).ceil() as usize).clamp(1, v.len());
    v[idx - 1]
}

fn bucket_name(nnz: usize) -> &'static str {
    if nnz < 100 {
        "nnz < 100"
    } else if nnz <= 1000 {
        "nnz 100-1k"
    } else {
        "nnz > 1k"
    }
}

const BUCKETS: [&str; 3] = ["nnz < 100", "nnz 100-1k", "nnz > 1k"];

// ---------------------------------------------------------------------------
// Reports
// ---------------------------------------------------------------------------

/// Single-engine report (kept for --engine <one> --bench).
fn write_report(
    engine: Engine,
    rows: &[RowResult],
    corpus_cert_stats: (usize, usize),
    par_line: &str,
    path: &str,
) -> std::io::Result<()> {
    let mut s = String::new();
    let n = rows.len();
    let agree = rows.iter().filter(|r| r.corpus_ok == r.native_ok).count();
    let native_certs = rows.iter().filter(|r| r.native_ok).count();
    let corpus_certs = rows.iter().filter(|r| r.corpus_ok).count();
    let sum_corpus: u128 = rows.iter().map(|r| r.corpus_ns).sum();
    let sum_native: u128 = rows.iter().map(|r| r.native_ns).sum();
    let ratios: Vec<f64> = rows
        .iter()
        .map(|r| r.corpus_ns as f64 / (r.native_ns.max(1)) as f64)
        .collect();

    writeln!(s, "farkas-bench report (engine: {})", engine.name()).unwrap();
    writeln!(s, "=====================================").unwrap();
    writeln!(s).unwrap();
    writeln!(
        s,
        "IMPORTANT BASELINE NOTE: the corpus 'ns' times are Lean-INTERPRETER times\n\
         (Mathlib tactic code, including the simplex oracle, runs interpreted when\n\
         Mathlib is used downstream). That interpreted time is the realistic\n\
         deployment baseline a native oracle would displace."
    )
    .unwrap();
    writeln!(s).unwrap();
    writeln!(s, "Instances:                    {n}").unwrap();
    writeln!(s, "Corpus certs (ok=true):       {corpus_certs}").unwrap();
    writeln!(s, "Native certs found:           {native_certs}").unwrap();
    writeln!(
        s,
        "Agreement with corpus ok:     {agree}/{n} ({:.4}%)",
        100.0 * agree as f64 / n as f64
    )
    .unwrap();
    writeln!(
        s,
        "Self-check (exact verifier):  all {native_certs} produced certs verified: {}",
        rows.iter().filter(|r| r.native_ok).all(|r| r.self_check_ok)
    )
    .unwrap();
    writeln!(
        s,
        "Corpus certs re-verified:     {}/{} ({:.4}%) under the pinned semantics",
        corpus_cert_stats.0,
        corpus_cert_stats.1,
        100.0 * corpus_cert_stats.0 as f64 / corpus_cert_stats.1.max(1) as f64
    )
    .unwrap();
    writeln!(s).unwrap();
    writeln!(
        s,
        "Sum of Mathlib oracle time:   {:>14.3} ms",
        sum_corpus as f64 / 1e6
    )
    .unwrap();
    writeln!(
        s,
        "Sum of native oracle time:    {:>14.3} ms",
        sum_native as f64 / 1e6
    )
    .unwrap();
    writeln!(
        s,
        "Overall speedup (sum ratio):  {:>14.1}x",
        sum_corpus as f64 / sum_native as f64
    )
    .unwrap();
    writeln!(
        s,
        "Median per-instance speedup:  {:>14.1}x",
        median(ratios.clone())
    )
    .unwrap();
    for bucket in BUCKETS {
        let idx: Vec<usize> = (0..n)
            .filter(|&i| bucket_name(rows[i].nnz) == bucket)
            .collect();
        if idx.is_empty() {
            continue;
        }
        let sc: u128 = idx.iter().map(|&i| rows[i].corpus_ns).sum();
        let sn: u128 = idx.iter().map(|&i| rows[i].native_ns).sum();
        let med = median(idx.iter().map(|&i| ratios[i]).collect());
        writeln!(
            s,
            "{bucket:>12}: {:>5} instances | sum speedup {:>9.1}x | median speedup {:>9.1}x",
            idx.len(),
            sc as f64 / sn as f64,
            med
        )
        .unwrap();
    }
    if !par_line.is_empty() {
        writeln!(s).unwrap();
        writeln!(s, "Parallel throughput ({PAR_THREADS} rayon threads):").unwrap();
        writeln!(s, "{par_line}").unwrap();
    }
    std::fs::write(path, &s)?;
    Ok(())
}

/// Combined report: all engines, tier residency, hybrid routing, parallel.
fn write_b35_report(
    runs: &[EngineRun],
    corpus_cert_stats: (usize, usize),
    unique_infeasible: usize,
    path: &str,
) -> std::io::Result<()> {
    let mut s = String::new();
    let faithful = runs
        .iter()
        .find(|r| r.engine == Engine::Faithful)
        .expect("faithful run");
    let n = faithful.rows.len();
    let sum_lean: u128 = faithful.rows.iter().map(|r| r.corpus_ns).sum();
    let infeas_rows = faithful.rows.iter().filter(|r| !r.corpus_ok).count();

    writeln!(s, "farkas-bench all-engine report").unwrap();
    writeln!(s, "========================================").unwrap();
    writeln!(s).unwrap();
    writeln!(
        s,
        "Baseline: corpus 'ns' = Lean-INTERPRETER oracle times (the realistic\n\
         deployment baseline a native oracle displaces). Lean sum = {:.3} ms.\n\
         'vs faithful' compares against this crate's BigRational port of the\n\
         Mathlib simplex oracle, measured in the same process on the same rows.",
        sum_lean as f64 / 1e6
    )
    .unwrap();
    writeln!(s).unwrap();
    writeln!(
        s,
        "Corpus: {n} oracle rows | ok=true {} | ok=false {} rows ({} unique infeasible instances)",
        faithful.rows.iter().filter(|r| r.corpus_ok).count(),
        infeas_rows,
        unique_infeasible
    )
    .unwrap();
    writeln!(
        s,
        "Startup validation: {}/{} Mathlib-produced corpus certs re-verified by the\n\
         exact BigRational verifier ({:.4}%) [gate, asserted at startup]",
        corpus_cert_stats.0,
        corpus_cert_stats.1,
        100.0 * corpus_cert_stats.0 as f64 / corpus_cert_stats.1.max(1) as f64
    )
    .unwrap();
    writeln!(s).unwrap();

    // ---------------- per-engine timing ----------------
    writeln!(
        s,
        "Single-thread timing per engine (full corpus, per-instance oracle time;"
    )
    .unwrap();
    writeln!(
        s,
        "hybrid times INCLUDE its internal exact repair + verification and any"
    )
    .unwrap();
    writeln!(s, "tiered fallback work)").unwrap();
    writeln!(
        s,
        "-----------------------------------------------------------------------"
    )
    .unwrap();
    for run in runs {
        let rows = &run.rows;
        let sum_native: u128 = rows.iter().map(|r| r.native_ns).sum();
        let times_us: Vec<f64> = rows.iter().map(|r| r.native_ns as f64 / 1e3).collect();
        let lean_ratio: Vec<f64> = rows
            .iter()
            .map(|r| r.corpus_ns as f64 / r.native_ns.max(1) as f64)
            .collect();
        let faith_ratio: Vec<f64> = rows
            .iter()
            .zip(&faithful.rows)
            .map(|(r, f)| f.native_ns as f64 / r.native_ns.max(1) as f64)
            .collect();
        let sum_faith: u128 = faithful.rows.iter().map(|r| r.native_ns).sum();
        writeln!(s).unwrap();
        writeln!(
            s,
            "engine {:>8}: sum {:>10.3} ms",
            run.engine.name(),
            sum_native as f64 / 1e6
        )
        .unwrap();
        writeln!(
            s,
            "  per-instance us: median {:>9.1} | p90 {:>9.1} | p99 {:>10.1}",
            percentile(times_us.clone(), 0.5),
            percentile(times_us.clone(), 0.9),
            percentile(times_us.clone(), 0.99)
        )
        .unwrap();
        writeln!(
            s,
            "  speedup vs Lean interpreter: sum {:>7.1}x | median per-instance {:>7.1}x",
            sum_lean as f64 / sum_native as f64,
            median(lean_ratio.clone())
        )
        .unwrap();
        writeln!(
            s,
            "  speedup vs faithful engine:  sum {:>7.2}x | median per-instance {:>7.2}x",
            sum_faith as f64 / sum_native as f64,
            median(faith_ratio.clone())
        )
        .unwrap();
        writeln!(
            s,
            "  {:>11} | {:>5} | {:>10} | {:>8} {:>8} {:>10} | {:>8} | {:>8}",
            "bucket", "n", "sum ms", "med us", "p90 us", "p99 us", "vsLean", "vsFaith"
        )
        .unwrap();
        for bucket in BUCKETS {
            let idx: Vec<usize> = (0..n)
                .filter(|&i| bucket_name(rows[i].nnz) == bucket)
                .collect();
            if idx.is_empty() {
                continue;
            }
            let sn: u128 = idx.iter().map(|&i| rows[i].native_ns).sum();
            let sl: u128 = idx.iter().map(|&i| rows[i].corpus_ns).sum();
            let sf: u128 = idx.iter().map(|&i| faithful.rows[i].native_ns).sum();
            let t: Vec<f64> = idx.iter().map(|&i| times_us[i]).collect();
            writeln!(
                s,
                "  {:>11} | {:>5} | {:>10.3} | {:>8.1} {:>8.1} {:>10.1} | {:>7.1}x | {:>7.2}x",
                bucket,
                idx.len(),
                sn as f64 / 1e6,
                percentile(t.clone(), 0.5),
                percentile(t.clone(), 0.9),
                percentile(t, 0.99),
                sl as f64 / sn as f64,
                sf as f64 / sn as f64
            )
            .unwrap();
        }
    }

    // ---------------- tiered specifics ----------------
    if let Some(run) = runs.iter().find(|r| r.engine == Engine::Tiered) {
        let c = run.counters;
        let tot: u64 = c.ops.iter().sum();
        writeln!(s).unwrap();
        writeln!(
            s,
            "Tiered engine: tier residency (exact ring ops +,-,*,/ per tier over the"
        )
        .unwrap();
        writeln!(
            s,
            "full single-thread corpus run; an op is attributed to its widest operand's"
        )
        .unwrap();
        writeln!(
            s,
            "tier, promotion events are counted at the moment a checked op overflows)"
        )
        .unwrap();
        writeln!(
            s,
            "-----------------------------------------------------------------------"
        )
        .unwrap();
        for (name, ops) in [
            ("i64", c.ops[0]),
            ("i128", c.ops[1]),
            ("BigRational", c.ops[2]),
        ] {
            writeln!(
                s,
                "  {:>12}: {:>13} ops ({:.4}%)",
                name,
                ops,
                100.0 * ops as f64 / tot.max(1) as f64
            )
            .unwrap();
        }
        writeln!(s, "  promotions i64 -> i128: {}", c.promo_to_i128).unwrap();
        writeln!(s, "  promotions i128 -> Big: {}", c.promo_to_big).unwrap();
    }

    // ---------------- hybrid specifics ----------------
    if let Some(run) = runs.iter().find(|r| r.engine == Engine::Hybrid) {
        let rows = &run.rows;
        let mut fp = 0usize;
        let mut retries = [0usize; 3]; // attempts 1,2,3 among FP successes
        let mut direct = 0usize;
        let mut repair_fail = 0usize;
        let mut stalled = 0usize;
        let mut fp_infeas = 0usize;
        let mut fallback_rows: Vec<&RowResult> = Vec::new();
        for r in rows {
            match r.route.expect("hybrid route") {
                Route::Fp { attempts } => {
                    fp += 1;
                    retries[(attempts as usize).clamp(1, 3) - 1] += 1;
                }
                Route::TieredDirect => direct += 1,
                Route::TieredRepairFail { .. } => {
                    repair_fail += 1;
                    fallback_rows.push(r);
                }
                Route::TieredFpStalled => {
                    stalled += 1;
                    fallback_rows.push(r);
                }
                Route::TieredFpInfeasible => fp_infeas += 1,
            }
        }
        writeln!(s).unwrap();
        writeln!(
            s,
            "Hybrid engine routing (soundness: certificates only after passing the"
        )
        .unwrap();
        writeln!(
            s,
            "exact verifier; every non-FP-certified answer comes from the exact"
        )
        .unwrap();
        writeln!(
            s,
            "tiered engine — FP infeasibility is never reported directly)"
        )
        .unwrap();
        writeln!(
            s,
            "-----------------------------------------------------------------------"
        )
        .unwrap();
        writeln!(
            s,
            "  FP64-path certificates:       {:>5} / {} ({:.2}% hit rate)",
            fp,
            rows.len(),
            100.0 * fp as f64 / rows.len() as f64
        )
        .unwrap();
        writeln!(
            s,
            "  support attempts among hits:  1st try {} | 2nd {} | 3rd {} (support-growth retries: {})",
            retries[0],
            retries[1],
            retries[2],
            retries[1] + retries[2]
        )
        .unwrap();
        writeln!(
            s,
            "  direct-to-tiered (unrepresentable scaled f64 / no strict hyp): {direct}"
        )
        .unwrap();
        writeln!(
            s,
            "  FP-infeasible hints (exact tiered confirmation run):           {fp_infeas}"
        )
        .unwrap();
        writeln!(
            s,
            "  fallbacks to tiered:          {:>5}  (repair-failed {}, FP stalled {})",
            repair_fail + stalled,
            repair_fail,
            stalled
        )
        .unwrap();
        if fallback_rows.is_empty() {
            writeln!(s, "  fallback clustering: none (no fallbacks)").unwrap();
        } else {
            writeln!(s, "  fallback clustering by nnz bucket:").unwrap();
            for bucket in BUCKETS {
                let k = fallback_rows
                    .iter()
                    .filter(|r| bucket_name(r.nnz) == bucket)
                    .count();
                writeln!(s, "    {bucket:>11}: {k}").unwrap();
            }
            let mut by_src: std::collections::HashMap<&str, usize> =
                std::collections::HashMap::new();
            for r in &fallback_rows {
                *by_src.entry(r.src.as_str()).or_default() += 1;
            }
            let mut srcs: Vec<(&str, usize)> = by_src.into_iter().collect();
            srcs.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
            writeln!(
                s,
                "  fallback clustering by src (top {}):",
                srcs.len().min(10)
            )
            .unwrap();
            for (src, k) in srcs.iter().take(10) {
                writeln!(s, "    {src}: {k}").unwrap();
            }
        }
    }

    // ---------------- parallel throughput ----------------
    if runs.iter().any(|r| !r.par_line.is_empty()) {
        writeln!(s).unwrap();
        writeln!(
            s,
            "Parallel throughput ({PAR_THREADS} rayon threads, one CPU node)"
        )
        .unwrap();
        writeln!(
            s,
            "-----------------------------------------------------------------------"
        )
        .unwrap();
        for run in runs {
            if !run.par_line.is_empty() {
                writeln!(s, "{}", run.par_line).unwrap();
            }
        }
    }

    // ---------------- agreement ----------------
    writeln!(s).unwrap();
    writeln!(
        s,
        "Agreement (required: every engine reproduces all corpus labels)"
    )
    .unwrap();
    writeln!(
        s,
        "-----------------------------------------------------------------------"
    )
    .unwrap();
    for run in runs {
        let rows = &run.rows;
        let agree = rows.iter().filter(|r| r.corpus_ok == r.native_ok).count();
        let certs = rows.iter().filter(|r| r.native_ok).count();
        let no_cert = rows.iter().filter(|r| !r.native_ok).count();
        let verified = rows.iter().filter(|r| r.native_ok).all(|r| r.self_check_ok);
        writeln!(
            s,
            "  {:>8}: certs {certs} | no-cert rows {no_cert} ({unique_infeasible} unique infeasible \
             instances) | label agreement {agree}/{n} ({:.4}%) | all certs exact-verified: {verified}",
            run.engine.name(),
            100.0 * agree as f64 / n as f64
        )
        .unwrap();
    }
    std::fs::write(path, &s)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

/// Count unique infeasible instances (dedup by (maxVar, hyps), like the G2
/// pipeline's dedup) among corpus rows with ok=false.
fn unique_infeasible(insts: &[Instance]) -> usize {
    let mut seen = std::collections::HashSet::new();
    for inst in insts.iter().filter(|i| !i.ok) {
        let mut key = format!("{}|", inst.max_var);
        for h in &inst.hyps {
            write!(key, "{:?}{:?};", h.ineq, h.coeffs).unwrap();
        }
        seen.insert(key);
    }
    seen.len()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut corpus_dir: Option<String> = None;
    let mut report_path: Option<String> = None;
    let mut bench = false;
    let mut par = false;
    let mut engine_arg = "hybrid".to_string();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--bench" => bench = true,
            "--par" => par = true,
            "--corpus" => {
                i += 1;
                corpus_dir = Some(args[i].clone());
            }
            "--report" => {
                i += 1;
                report_path = Some(args[i].clone());
            }
            "--engine" => {
                i += 1;
                engine_arg = args[i].clone();
            }
            a => {
                eprintln!("unknown arg {a}");
                std::process::exit(2);
            }
        }
        i += 1;
    }
    let engines: Vec<Engine> = match engine_arg.as_str() {
        "faithful" => vec![Engine::Faithful],
        "tiered" => vec![Engine::Tiered],
        "hybrid" => vec![Engine::Hybrid],
        "all" => vec![Engine::Faithful, Engine::Tiered, Engine::Hybrid],
        other => {
            eprintln!("unknown engine '{other}' (expected faithful|tiered|hybrid|all)");
            std::process::exit(2);
        }
    };
    let Some(corpus_dir) = corpus_dir else {
        eprintln!("--corpus DIR is required");
        std::process::exit(2);
    };
    if bench && report_path.is_none() {
        eprintln!("--bench requires --report PATH");
        std::process::exit(2);
    }
    let report_path = report_path.unwrap_or_default();

    let insts = load_corpus(std::path::Path::new(&corpus_dir)).expect("load corpus");
    eprintln!(
        "loaded {} oracle instances from {}",
        insts.len(),
        corpus_dir
    );

    // Startup gate (SOUNDNESS INVARIANT, unchanged): re-verify every
    // corpus-recorded Mathlib certificate with the exact verifier.
    let with_cert: Vec<&Instance> = insts.iter().filter(|i| i.cert.is_some()).collect();
    let cert_valid = with_cert
        .iter()
        .filter(|i| verify_cert(&i.hyps, i.cert.as_ref().unwrap()))
        .count();
    println!(
        "corpus cert re-verification: {}/{} ({:.4}%)",
        cert_valid,
        with_cert.len(),
        100.0 * cert_valid as f64 / with_cert.len().max(1) as f64
    );
    assert!(
        cert_valid as f64 >= 0.999 * with_cert.len() as f64,
        "semantic interpretation failed corpus validation"
    );
    let uniq_infeas = unique_infeasible(&insts);
    println!(
        "corpus: {} rows, {} certs, {} infeasible rows ({} unique infeasible instances)",
        insts.len(),
        with_cert.len(),
        insts.iter().filter(|i| !i.ok).count(),
        uniq_infeas
    );

    let mut runs: Vec<EngineRun> = Vec::new();
    for &engine in &engines {
        eprintln!("running engine '{}' single-threaded ...", engine.name());
        let (rows, counters) = run_single(&insts, engine);
        let n = rows.len();
        let agree = rows.iter().filter(|r| r.corpus_ok == r.native_ok).count();
        let native_certs = rows.iter().filter(|r| r.native_ok).count();
        let sum_corpus: u128 = rows.iter().map(|r| r.corpus_ns).sum();
        let sum_native: u128 = rows.iter().map(|r| r.native_ns).sum();
        println!(
            "[{}] {} certs, agreement {agree}/{n} ({:.4}%), self-verified: {}, \
             sum {:.3} ms (vs Lean {:.3} ms -> {:.1}x)",
            engine.name(),
            native_certs,
            100.0 * agree as f64 / n as f64,
            rows.iter().filter(|r| r.native_ok).all(|r| r.self_check_ok),
            sum_native as f64 / 1e6,
            sum_corpus as f64 / 1e6,
            sum_corpus as f64 / sum_native as f64
        );
        for r in &rows {
            if r.corpus_ok != r.native_ok {
                println!(
                    "  DISAGREE [{}] {} call {}: corpus ok={} native ok={}",
                    engine.name(),
                    r.src,
                    r.call,
                    r.corpus_ok,
                    r.native_ok
                );
            }
        }
        let par_line = if par {
            eprintln!(
                "running engine '{}' with {PAR_THREADS} threads ...",
                engine.name()
            );
            let line = run_par(&insts, engine);
            println!("{line}");
            line
        } else {
            String::new()
        };
        runs.push(EngineRun {
            engine,
            rows,
            counters,
            par_line,
        });
    }

    if bench {
        if runs.len() > 1 {
            write_b35_report(
                &runs,
                (cert_valid, with_cert.len()),
                uniq_infeas,
                &report_path,
            )
            .expect("write report");
        } else {
            let run = &runs[0];
            write_report(
                run.engine,
                &run.rows,
                (cert_valid, with_cert.len()),
                &run.par_line,
                &report_path,
            )
            .expect("write report");
        }
        println!("report written to {report_path}");
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use farkas_core::hybrid;
    use farkas_core::types::{Hyp, Ineq, parse_line};
    use num_bigint::BigInt;

    fn bi(x: i64) -> BigInt {
        BigInt::from(x)
    }

    // Three hand-checked corpus rows (verbatim from a replay run).
    //
    // Row 1 (test/aime_1983_p1.lean call 1), cert {9:1, 5:1, 0:1}:
    //   hyp9 = le [x1 - 1*c],  hyp5 = le [-x1 + 2c],  hyp0 = lt [-1*c]
    //   sum: atom1: 1-1 = 0; atom0(c): -1+2-1 = 0; hyp0 is lt  => valid.
    const ROW1: &str = r#"{"ty":"oracle","call":1,"t":80736211447781,"src":"test/aime_1983_p1.lean","maxVar":4,"nHyps":13,"hyps":[["lt",[[0,-1]]],["le",[[1,-1]]],["le",[[2,-1]]],["le",[[3,-1]]],["le",[[4,-1]]],["le",[[1,-1],[0,2]]],["le",[[2,-1],[0,2]]],["le",[[3,-1],[0,2]]],["le",[[4,-1]]],["le",[[1,1],[0,-1]]],["le",[[1,-1],[0,2]]],["le",[[2,-1],[0,2]]],["le",[[3,-1],[0,2]]]],"ns":2416303,"ok":true,"cert":[[9,1],[5,1],[0,1]]}"#;

    // Row 2 (test/aime_1983_p2.lean call 1), cert {8:1, 3:1}:
    //   hyp8 = lt [x2 - x1],  hyp3 = le [-x2 + x1]
    //   sum: atom2: 1-1 = 0; atom1: -1+1 = 0; hyp8 is lt  => valid.
    const ROW2: &str = r#"{"ty":"oracle","call":1,"t":80736034095310,"src":"test/aime_1983_p2.lean","maxVar":6,"nHyps":9,"hyps":[["lt",[[0,-1]]],["lt",[[1,-1]]],["lt",[[1,1],[0,-15]]],["le",[[2,-1],[1,1]]],["le",[[2,1],[0,-15]]],["eq",[[6,-1],[5,1],[4,1],[3,1]]],["eq",[[6,1],[5,-1],[4,-1],[3,-1]]],["le",[[2,-1],[1,1]]],["lt",[[2,1],[1,-1]]]],"ns":1802009,"ok":true,"cert":[[8,1],[3,1]]}"#;

    // Row 3 (test/amc12_2000_p6.lean call 1), cert {7:1, 4:1, 0:1}:
    //   hyp7 = le [-x1 + 19c],  hyp4 = le [x1 - 18c],  hyp0 = lt [-1c]
    //   sum: atom1: -1+1 = 0; atom0: 19-18-1 = 0; hyp0 is lt  => valid.
    const ROW3: &str = r#"{"ty":"oracle","call":1,"t":80924942757555,"src":"test/amc12_2000_p6.lean","maxVar":2,"nHyps":8,"hyps":[["lt",[[0,-1]]],["le",[[1,-1]]],["le",[[2,-1]]],["le",[[1,-1],[0,4]]],["le",[[1,1],[0,-18]]],["le",[[2,-1],[0,4]]],["le",[[2,1],[0,-18]]],["le",[[1,-1],[0,19]]]],"ns":1910609,"ok":true,"cert":[[7,1],[4,1],[0,1]]}"#;

    #[test]
    fn verifier_accepts_hand_checked_corpus_certs() {
        for row in [ROW1, ROW2, ROW3] {
            let inst = parse_line(row).expect("parse");
            let cert = inst.cert.clone().expect("cert");
            assert!(
                verify_cert(&inst.hyps, &cert),
                "known-good cert must verify"
            );
        }
    }

    #[test]
    fn verifier_rejects_tampered_certs() {
        let inst = parse_line(ROW1).unwrap();
        // wrong weight breaks the zero-sum
        assert!(!verify_cert(
            &inst.hyps,
            &[(9, bi(2)), (5, bi(1)), (0, bi(1))]
        ));
        // dropping the strict hyp: sum = (x1-1) + (-x1+2) = 1 != 0 -> reject
        assert!(!verify_cert(&inst.hyps, &[(9, bi(1)), (5, bi(1))]));
        let inst2 = parse_line(ROW2).unwrap();
        // nonpositive / out-of-range coefficients must be rejected outright.
        assert!(!verify_cert(&inst2.hyps, &[(3, bi(0))]));
        assert!(!verify_cert(&inst2.hyps, &[(3, bi(-1))]));
        assert!(!verify_cert(&inst2.hyps, &[(99, bi(1))]));
        assert!(!verify_cert(&inst2.hyps, &[]));
    }

    #[test]
    fn oracle_solves_hand_checked_rows() {
        for row in [ROW1, ROW2, ROW3] {
            let inst = parse_line(row).unwrap();
            let cert = produce_certificate(&inst.hyps, inst.max_var)
                .expect("oracle must find a certificate");
            assert!(
                verify_cert(&inst.hyps, &cert),
                "produced cert must self-verify"
            );
        }
    }

    #[test]
    fn all_eq_corner_case_has_no_certificate() {
        // x = 0 and -x = 0: the weighted sum can vanish (1,1) but no hyp is
        // strict, so "0 = 0" is not a contradiction -> no certificate.
        let hyps = vec![
            Hyp {
                ineq: Ineq::Eq,
                coeffs: vec![(1, bi(1))],
            },
            Hyp {
                ineq: Ineq::Eq,
                coeffs: vec![(1, bi(-1))],
            },
        ];
        assert!(produce_certificate(&hyps, 1).is_none());
        assert!(produce_certificate_tiered(&hyps, 1).is_none());
        let (c, _) = produce_certificate_hybrid(&hyps, 1);
        assert!(c.is_none());
        // ...and the verifier agrees that the eq-only combination is no cert.
        assert!(!verify_cert(&hyps, &[(0, bi(1)), (1, bi(1))]));
    }

    #[test]
    fn satisfiable_system_is_infeasible_for_cert_search() {
        // -1 < 0 (linarith's trivial hyp) and x > 0: jointly satisfiable,
        // so no nonneg combination sums to zero with a strict participant.
        let hyps = vec![
            Hyp {
                ineq: Ineq::Lt,
                coeffs: vec![(0, bi(-1))],
            },
            Hyp {
                ineq: Ineq::Lt,
                coeffs: vec![(1, bi(-1))],
            },
        ];
        assert!(produce_certificate(&hyps, 1).is_none());
        assert!(produce_certificate_tiered(&hyps, 1).is_none());
        let (c, route) = produce_certificate_hybrid(&hyps, 1);
        assert!(c.is_none());
        // SOUNDNESS: the hybrid 'no certificate' must have come from an exact
        // engine, never from the FP path.
        assert!(!matches!(route, Route::Fp { .. }));
    }

    // -------------------- tiered engine --------------------

    #[test]
    fn tiered_engine_matches_faithful_on_hand_rows() {
        for row in [ROW1, ROW2, ROW3] {
            let inst = parse_line(row).unwrap();
            let cert = produce_certificate_tiered(&inst.hyps, inst.max_var)
                .expect("tiered oracle must find a certificate");
            assert!(
                verify_cert(&inst.hyps, &cert),
                "tiered cert must self-verify"
            );
            // identical algorithm -> identical certificate as faithful
            let faithful = produce_certificate(&inst.hyps, inst.max_var).unwrap();
            assert_eq!(cert, faithful, "tiered must make the same pivot decisions");
        }
    }

    #[test]
    fn tier_promotion_mid_pivot_overflows_i64() {
        // x > A/B and x <= C/D with A/B > C/D: infeasible, and the pivot
        // arithmetic multiplies ~1e15-scale coprime values, whose ~1e30
        // products overflow i64 mid-solve and must promote to i128.
        let a: i64 = 1_000_000_000_000_001; // A = 1e15 + 1
        let b: i64 = 1_000_000_000_000_000; // B = 1e15
        let hyps = vec![
            Hyp {
                ineq: Ineq::Lt,
                coeffs: vec![(0, bi(-1))],
            }, // -1 < 0
            Hyp {
                ineq: Ineq::Lt,
                coeffs: vec![(1, bi(-b)), (0, bi(a))],
            }, // A - Bx < 0
            Hyp {
                ineq: Ineq::Le,
                coeffs: vec![(1, bi(a)), (0, bi(-b))],
            }, // Ax - B <= 0
        ];
        let before = rat::tls_counters();
        let cert = produce_certificate_tiered(&hyps, 1).expect("must find certificate");
        let after = rat::tls_counters();
        assert!(
            verify_cert(&hyps, &cert),
            "cert must pass the exact verifier"
        );
        assert!(
            after.promo_to_i128 > before.promo_to_i128,
            "solve must have promoted i64 -> i128 at least once \
             (promotions before {} after {})",
            before.promo_to_i128,
            after.promo_to_i128
        );
        // agreement with the faithful engine
        let faithful = produce_certificate(&hyps, 1).expect("faithful agrees");
        assert_eq!(cert, faithful);
    }

    // -------------------- hybrid engine --------------------

    #[test]
    fn hybrid_engine_solves_hand_rows() {
        for row in [ROW1, ROW2, ROW3] {
            let inst = parse_line(row).unwrap();
            let (cert, _route) = produce_certificate_hybrid(&inst.hyps, inst.max_var);
            let cert = cert.expect("hybrid must find a certificate");
            assert!(
                verify_cert(&inst.hyps, &cert),
                "hybrid cert must self-verify"
            );
        }
    }

    #[test]
    fn hybrid_falls_back_when_fp_feasible_but_exactly_infeasible() {
        // Column scaling maps the coefficients {2^60, 2^60+1} of hyp 1 to
        // {-2^60/(2^60+1), -1}, and -2^60/(2^60+1) rounds to -1.0 in f64
        // (the difference is below half an ulp).  The FP LP is therefore
        // feasible (mu = (1,1)), but the exact lambda-space system is
        // inconsistent, so every exact-repair attempt must be rejected and
        // the engine must fall back to tiered — which proves there is no
        // certificate.  This is exactly the "FP64 is a hint, never an
        // answer" soundness invariant.
        let n: i64 = 1 << 60;
        let hyps = vec![
            Hyp {
                ineq: Ineq::Lt,
                coeffs: vec![(1, bi(n)), (2, bi(n))],
            },
            Hyp {
                ineq: Ineq::Le,
                coeffs: vec![(1, bi(-(n + 1))), (2, bi(-n))],
            },
        ];
        let (cert, route) = produce_certificate_hybrid(&hyps, 2);
        assert!(
            cert.is_none(),
            "exactly infeasible: no certificate may be produced"
        );
        assert!(
            route.is_fallback(),
            "expected a fallback-to-tiered route, got {route:?}"
        );
        // exact engines agree
        assert!(produce_certificate(&hyps, 2).is_none());
        assert!(produce_certificate_tiered(&hyps, 2).is_none());
    }

    #[test]
    fn hybrid_handles_607_digit_corpus_row() {
        // test/amc12a_2013_p4.lean call 1 carries the corpus-max 607-digit
        // coefficients.  The exact column scaling must keep the FP LP finite,
        // and whatever route the hybrid takes, the answer must agree with the
        // corpus label and pass the exact verifier (the exact-repair /
        // fallback machinery runs Big-tier arithmetic here).
        let text = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/fixtures/amc12a_2013_p4_call1.jsonl"
        ));
        let inst = text
            .lines()
            .filter_map(parse_line)
            .find(|i| i.call == 1)
            .expect("call 1 present");
        let max_digits = inst
            .hyps
            .iter()
            .flat_map(|h| h.coeffs.iter())
            .map(|(_, c)| c.magnitude().to_string().len())
            .max()
            .unwrap();
        assert!(
            max_digits >= 600,
            "expected the 607-digit row, got {max_digits} digits"
        );
        let (cert, _route) = produce_certificate_hybrid(&inst.hyps, inst.max_var);
        assert_eq!(
            cert.is_some(),
            inst.ok,
            "hybrid must agree with the corpus label"
        );
        if let Some(c) = &cert {
            assert!(
                verify_cert(&inst.hyps, c),
                "hybrid cert must pass the exact verifier"
            );
        }
        // tiered agrees too
        assert_eq!(
            produce_certificate_tiered(&inst.hyps, inst.max_var).is_some(),
            inst.ok
        );
    }

    #[test]
    fn tampered_support_rejected_by_exact_repair() {
        let inst = parse_line(ROW1).unwrap();
        // The true support {9, 5, 0} repairs to the known certificate.
        let cert = hybrid::exact_repair(&inst.hyps, &[9, 5, 0]).expect("true support must repair");
        assert!(verify_cert(&inst.hyps, &cert));
        assert_eq!(cert, vec![(0usize, bi(1)), (5, bi(1)), (9, bi(1))]);
        // Tampered supports: dropping any needed column makes the restricted
        // system strict-free or inconsistent, and exact repair must reject.
        assert!(
            hybrid::exact_repair(&inst.hyps, &[9, 5]).is_none(),
            "no strict hyp"
        );
        assert!(
            hybrid::exact_repair(&inst.hyps, &[5, 0]).is_none(),
            "inconsistent"
        );
        assert!(
            hybrid::exact_repair(&inst.hyps, &[9, 0]).is_none(),
            "inconsistent"
        );
        assert!(
            hybrid::exact_repair(&inst.hyps, &[0]).is_none(),
            "inconsistent"
        );
        // An irrelevant extra column cannot smuggle in a bad certificate:
        // whatever repair returns must still pass the exact verifier.
        if let Some(c) = hybrid::exact_repair(&inst.hyps, &[9, 5, 0, 1]) {
            assert!(verify_cert(&inst.hyps, &c));
        }
    }
}
