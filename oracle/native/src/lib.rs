//! farkas-core: exact tiered-rational Farkas-certificate engines for Lean's
//! `linarith`, plus the corpus types and the exact certificate verifier.
//!
//! Soundness invariants (see docs/protocol.md and the Lean side):
//!   * every certificate is checked by [`verify::verify_cert`] (exact
//!     BigRational arithmetic) before it is reported anywhere;
//!   * a "no certificate" answer only ever comes from an exact engine
//!     ([`tiered`] or [`oracle`]); FP64 evidence ([`hybrid`]'s phase 1) is a
//!     hint, never an answer.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

pub mod hybrid;
pub mod oracle;
pub mod rat;
pub mod tiered;
pub mod types;
pub mod verify;
