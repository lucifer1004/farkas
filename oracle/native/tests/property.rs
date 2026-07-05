//! Corpus-independent property tests.
//!
//! Deterministic random LP instances (inline xorshift, no `rand` dep, no
//! wall-clock seeds) → certificate search → exact verification, plus
//! agreement between the tiered engine and the BigRational reference engine,
//! plus tampered-certificate rejection on a hand-built instance.

mod common;

use common::XorShift;
use farkas_core::oracle::produce_certificate;
use farkas_core::tiered::produce_certificate_tiered;
use farkas_core::types::{Hyp, Ineq};
use farkas_core::verify::verify_cert;
use num_bigint::BigInt;

/// A random instance in linarith's shape: atom 0 is the constant, the seed
/// hypothesis `-1 < 0` is present, and eq hypotheses are mirrored in both
/// orientations (Mathlib's `addNegEqProofs` does the same before the oracle
/// ever sees the problem).
fn random_instance(rng: &mut XorShift) -> (Vec<Hyp>, usize) {
    let max_var = 1 + rng.below(6) as usize;
    let n_hyps = 1 + rng.below(8) as usize;
    let mut hyps = vec![Hyp {
        ineq: Ineq::Lt,
        coeffs: vec![(0, BigInt::from(-1))],
    }];
    for _ in 0..n_hyps {
        let ineq = match rng.below(3) {
            0 => Ineq::Eq,
            1 => Ineq::Le,
            _ => Ineq::Lt,
        };
        let n_terms = 1 + rng.below(4) as usize;
        let mut coeffs: Vec<(usize, BigInt)> = Vec::new();
        for _ in 0..n_terms {
            let var = rng.below(max_var as u64 + 1) as usize;
            if !coeffs.iter().any(|(v, _)| *v == var) {
                coeffs.push((var, BigInt::from(rng.coeff())));
            }
        }
        hyps.push(Hyp {
            ineq,
            coeffs: coeffs.clone(),
        });
        if ineq == Ineq::Eq {
            let neg = coeffs.iter().map(|(v, c)| (*v, -c)).collect();
            hyps.push(Hyp {
                ineq: Ineq::Eq,
                coeffs: neg,
            });
        }
    }
    (hyps, max_var)
}

/// Every certificate either engine produces must pass the exact verifier,
/// and the two exact engines must agree on certificate *existence*.
#[test]
fn random_roundtrip_and_engine_agreement() {
    let mut rng = XorShift(0x9E3779B97F4A7C15);
    let mut found = 0usize;
    for i in 0..500 {
        let (hyps, max_var) = random_instance(&mut rng);
        let tiered = produce_certificate_tiered(&hyps, max_var);
        let reference = produce_certificate(&hyps, max_var);
        if let Some(cert) = &tiered {
            assert!(
                verify_cert(&hyps, cert),
                "unverified tiered cert on instance {i}"
            );
            found += 1;
        }
        if let Some(cert) = &reference {
            assert!(
                verify_cert(&hyps, cert),
                "unverified reference cert on instance {i}"
            );
        }
        assert_eq!(
            tiered.is_some(),
            reference.is_some(),
            "engines disagree on certificate existence, instance {i}: {hyps:?}"
        );
    }
    // the distribution must actually exercise the interesting branch
    assert!(found > 50, "only {found}/500 instances had certificates");
}

/// Same round-trip with ~10^40-scale coefficients: forces promotion out of
/// the i64 tier (a real i128::MIN tier-routing bug once lived on this path;
/// see rat.rs `i128_min_never_enters_m_tier`).
#[test]
fn random_roundtrip_big_coefficients() {
    let mut rng = XorShift(0xD1B54A32D192ED03);
    for i in 0..60 {
        let (mut hyps, max_var) = random_instance(&mut rng);
        for h in hyps.iter_mut().skip(1) {
            for (_, c) in h.coeffs.iter_mut() {
                let scale = BigInt::from(10u8).pow(20 + rng.below(20) as u32);
                *c = &*c * &scale + BigInt::from(rng.coeff());
            }
        }
        let tiered = produce_certificate_tiered(&hyps, max_var);
        let reference = produce_certificate(&hyps, max_var);
        if let Some(cert) = &tiered {
            assert!(
                verify_cert(&hyps, cert),
                "unverified big-coeff cert on instance {i}"
            );
        }
        assert_eq!(
            tiered.is_some(),
            reference.is_some(),
            "big-coeff disagreement, instance {i}"
        );
    }
}

/// Hand-built instance with a known certificate, then every class of
/// tampering must be rejected: perturbed coefficient, dropped strict
/// hypothesis, non-positive weight, out-of-range index, empty cert.
#[test]
fn tampered_certificates_are_rejected() {
    // h0: -1 < 0 (seed), h1: x + 1 <= 0, h2: -x < 0; 1*h0 + 1*h1 + 1*h2 = 0<0
    let hyps = vec![
        Hyp {
            ineq: Ineq::Lt,
            coeffs: vec![(0, BigInt::from(-1))],
        },
        Hyp {
            ineq: Ineq::Le,
            coeffs: vec![(1, BigInt::from(1)), (0, BigInt::from(1))],
        },
        Hyp {
            ineq: Ineq::Lt,
            coeffs: vec![(1, BigInt::from(-1))],
        },
    ];
    let good: Vec<(usize, BigInt)> = vec![(0, 1.into()), (1, 1.into()), (2, 1.into())];
    assert!(
        verify_cert(&hyps, &good),
        "the untampered certificate must verify"
    );

    let perturbed = vec![(0, 1.into()), (1, 2.into()), (2, 1.into())];
    assert!(
        !verify_cert(&hyps, &perturbed),
        "perturbed weight must fail"
    );

    // only le hyps weighted: sums to zero but nothing strict
    let h_no_strict = vec![
        Hyp {
            ineq: Ineq::Le,
            coeffs: vec![(1, BigInt::from(1))],
        },
        Hyp {
            ineq: Ineq::Le,
            coeffs: vec![(1, BigInt::from(-1))],
        },
    ];
    let no_strict: Vec<(usize, BigInt)> = vec![(0, 1.into()), (1, 1.into())];
    assert!(
        !verify_cert(&h_no_strict, &no_strict),
        "strictness-free cert must fail"
    );

    let zero_weight = vec![(0, 0.into()), (1, 1.into()), (2, 1.into())];
    assert!(!verify_cert(&hyps, &zero_weight), "zero weight must fail");
    let neg_weight = vec![(0, BigInt::from(-1)), (1, 1.into()), (2, 1.into())];
    assert!(
        !verify_cert(&hyps, &neg_weight),
        "negative weight must fail"
    );

    let out_of_range = vec![(0, 1.into()), (7, 1.into())];
    assert!(
        !verify_cert(&hyps, &out_of_range),
        "out-of-range index must fail"
    );

    assert!(!verify_cert(&hyps, &[]), "empty cert must fail");
}
