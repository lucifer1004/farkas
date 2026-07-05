//! Protocol fuzz against the real daemon binary.
//!
//! The invariant under test: **the daemon never wedges the Lean process.**
//! Whatever arrives on a line — random bytes, malformed JSON, wrong shapes,
//! absurd sizes — the daemon answers exactly one JSON line and stays alive
//! for the next request; on EOF (even mid-stream) it exits cleanly.
//!
//! Deterministic (inline xorshift, fixed seeds): failures reproduce.

mod common;

use common::XorShift;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdout, Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

struct Daemon {
    child: Child,
    lines: mpsc::Receiver<String>,
}

impl Daemon {
    fn spawn() -> Daemon {
        let mut child = Command::new(env!("CARGO_BIN_EXE_farkas-oracled"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn daemon");
        let stdout: ChildStdout = child.stdout.take().unwrap();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            for line in BufReader::new(stdout).lines() {
                match line {
                    Ok(l) => {
                        if tx.send(l).is_err() {
                            break;
                        }
                    }
                    Err(_) => break,
                }
            }
        });
        Daemon { child, lines: rx }
    }

    /// Send one line; the daemon must answer one JSON line within 10s.
    fn ask(&mut self, line: &str) -> String {
        let stdin = self.child.stdin.as_mut().unwrap();
        stdin.write_all(line.as_bytes()).expect("write");
        stdin.write_all(b"\n").expect("write newline");
        stdin.flush().expect("flush");
        self.lines
            .recv_timeout(Duration::from_secs(10))
            .unwrap_or_else(|_| panic!("daemon wedged (no answer within 10s) on: {line:.120}"))
    }

    fn shutdown(mut self) {
        drop(self.child.stdin.take()); // EOF
        let status = self.child.wait().expect("wait");
        assert!(
            status.success(),
            "daemon exited non-zero after EOF: {status}"
        );
    }
}

fn assert_protocol_answer(input: &str, answer: &str) {
    let v: serde_json::Value = serde_json::from_str(answer)
        .unwrap_or_else(|_| panic!("non-JSON answer {answer:.120} to input {input:.120}"));
    assert!(
        v.get("cert").is_some() || v.get("error").is_some() || v.get("farkas_protocol").is_some(),
        "answer {answer:.120} has none of cert/error/farkas_protocol (input {input:.120})"
    );
}

const VALID: &str =
    "{\"maxVar\":1,\"hyps\":[[\"lt\",[[0,-1]]],[\"le\",[[1,-1],[0,2]]],[\"le\",[[1,1]]]]}";

/// Structured malformations: every shape a confused or hostile client could
/// produce, each answered with an error (or ignored, for blank lines) — and
/// the daemon must still solve a real request afterwards.
#[test]
fn malformed_requests_never_kill_the_daemon() {
    let cases: &[&str] = &[
        "not json at all",
        "{",
        "[]",
        "null",
        "42",
        "\"maxVar\"",
        "{\"maxVar\":1}",
        "{\"hyps\":[]}",
        "{\"maxVar\":\"one\",\"hyps\":[]}",
        "{\"maxVar\":-1,\"hyps\":[]}",
        "{\"maxVar\":1.5,\"hyps\":[]}",
        "{\"maxVar\":1,\"hyps\":{}}",
        "{\"maxVar\":1,\"hyps\":[42]}",
        "{\"maxVar\":1,\"hyps\":[[]]}",
        "{\"maxVar\":1,\"hyps\":[[\"gt\",[[0,1]]]]}",
        "{\"maxVar\":1,\"hyps\":[[\"lt\"]]}",
        "{\"maxVar\":1,\"hyps\":[[\"lt\",[[0]]]]}",
        "{\"maxVar\":1,\"hyps\":[[\"lt\",[[0,\"x\"]]]]}",
        "{\"maxVar\":1,\"hyps\":[[\"lt\",[[0,1.25]]]]}",
        "{\"maxVar\":1,\"hyps\":[[\"lt\",[[-3,1]]]]}",
        "{\"maxVar\":1,\"hyps\":[[\"lt\",[[0,1],[0,1],[0,1]]]]}",
        // absurd maxVar: must be a fast error, not an OOM
        "{\"maxVar\":999999999999,\"hyps\":[[\"lt\",[[0,-1]]]]}",
        // atom index beyond maxVar: protocol error, not an indexing panic
        "{\"maxVar\":1,\"hyps\":[[\"lt\",[[7,1]]]]}",
        "{\"maxVar\":1,\"hyps\":[[\"lt\",[[0,-1]]],[\"le\",[[999999999,1]]]]}",
        "{\"hello\":false}",
        "{\"hello\":1}",
        "{\"hello\":true}",
    ];
    let mut d = Daemon::spawn();
    for input in cases {
        let answer = d.ask(input);
        assert_protocol_answer(input, &answer);
        // liveness after every malformation: a real request still solves
        let ok = d.ask(VALID);
        assert!(
            ok.starts_with("{\"cert\":[["),
            "daemon broken after {input:.120}: {ok:.120}"
        );
    }
    d.shutdown();
}

/// Random byte garbage and random JSON-ish mutations of a valid request.
#[test]
fn random_garbage_never_kills_the_daemon() {
    let mut rng = XorShift(0x243F6A8885A308D3);
    let mut d = Daemon::spawn();
    for round in 0..300 {
        let input = if round % 2 == 0 {
            // printable garbage (newline-free so it stays one request)
            let len = 1 + (rng.next() % 200) as usize;
            (0..len)
                .map(|_| (b' ' + (rng.next() % 94) as u8) as char)
                .collect::<String>()
        } else {
            // structured mutation: flip one byte of a valid request
            let mut bytes = VALID.as_bytes().to_vec();
            let pos = (rng.next() as usize) % bytes.len();
            bytes[pos] = b' ' + (rng.next() % 94) as u8;
            String::from_utf8_lossy(&bytes).into_owned()
        };
        let answer = d.ask(&input);
        assert_protocol_answer(&input, &answer);
    }
    let ok = d.ask(VALID);
    assert!(
        ok.starts_with("{\"cert\":[["),
        "daemon broken after garbage: {ok:.120}"
    );
    d.shutdown();
}

/// Giant-but-wellformed inputs: coefficients with tens of thousands of
/// digits and a megabyte-scale line must answer (slowly is fine), not wedge.
#[test]
fn giant_inputs_answer_and_terminate() {
    let mut d = Daemon::spawn();
    let big = "9".repeat(30_000);
    let req = format!(
        "{{\"maxVar\":1,\"hyps\":[[\"lt\",[[0,-1]]],[\"le\",[[1,-{big}],[0,{big}]]],[\"le\",[[1,{big}]]]]}}"
    );
    let answer = d.ask(&req);
    assert_protocol_answer(&req, &answer);
    assert!(
        answer.starts_with("{\"cert\":"),
        "giant coefficients: {answer:.120}"
    );

    // one huge line that is not valid JSON
    let junk = "x".repeat(1 << 20);
    let answer = d.ask(&junk);
    assert_eq!(answer, "{\"error\":\"bad request\"}");
    d.shutdown();
}

/// EOF mid-request (no trailing newline) must be a clean exit, not a hang.
#[test]
fn eof_mid_request_exits_cleanly() {
    let mut d = Daemon::spawn();
    let ok = d.ask(VALID);
    assert!(ok.starts_with("{\"cert\":[["));
    let stdin = d.child.stdin.as_mut().unwrap();
    stdin
        .write_all(b"{\"maxVar\":1,\"hyps\":[[\"l")
        .expect("write partial");
    stdin.flush().expect("flush");
    d.shutdown();
}
