//! Shared test utilities. Deterministic PRNG — no `rand` dep, no wall-clock
//! seeds, so failures reproduce.
#![allow(dead_code)] // not every test binary uses every helper

pub struct XorShift(pub u64);

impl XorShift {
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// Small signed coefficient in [-10, 10] \ {0}.
    pub fn coeff(&mut self) -> i64 {
        let c = self.below(20) as i64 - 10;
        if c == 0 { 1 } else { c }
    }
}
