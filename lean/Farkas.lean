import Farkas.Auto

/-!
# farkas

Fast, exact Farkas-certificate oracle and lazy preprocessing for Lean's
`linarith`. Farkas' lemma says the certificate exists; this package finds
it fast.

`import Farkas` = drop-in acceleration (see `Farkas.Auto`). For explicit
opt-in per call site use `linarith (oracle := Farkas.native)`.
-/
