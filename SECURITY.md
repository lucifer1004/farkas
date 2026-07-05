# Security policy

farkas's trust model is designed so that the daemon is *untrusted*: a
compromised or buggy `farkas-oracled` can cause tactic failures, never a
wrong proof (every certificate is re-checked by stock linarith's proof
reconstruction and the Lean kernel). The daemon binds no network sockets —
it is a local child process on a stdin/stdout pipe.

Still worth reporting: anything that breaks that model (a way to make the
Lean side accept an unchecked answer), robustness failures (input that
wedges or crashes the daemon in a loop — see the fuzz suite in
`oracle/native/tests/daemon_fuzz.rs`), or supply-chain issues in the
release pipeline (`farkas-fetch` verifies SHA256SUMS from the same GitHub
release it downloads from; the checksums authenticate the artifact against
corruption, not against a compromised release account).

Report via GitHub Security Advisories ("Report a vulnerability" on the
repository's Security tab) or to the maintainer listed in CODEOWNERS.
