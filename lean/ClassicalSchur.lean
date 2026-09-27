/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ClassicalSchur.Basic
import ClassicalSchur.Ramsey
import ClassicalSchur.Lift
import ClassicalSchur.Values

/-!
# Classical Schur numbers: the Eliahou–Revuelta number `L(n)`

`L(4) = 16` and `49 ≤ L(5) ≤ 65` (`ClassicalSchur.erL_four`,
`ClassicalSchur.erL_five_bounds`). The mathematics is in A. McKenna, *The
Schur degree of block sums: `L(4) = 16` and `L(5) ≥ 49`* (2026), which the
modules of this library cite as "the paper".
-/
