/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosBracket
import Azurite.AzFloat.SqrtRat
import Azurite.AzFloat.PowRatBracket
import Azurite.AzRat.Sub
import Azurite.AzRat.Add
import Azurite.AzRat.Div

/-!
## The bracket of `arccos q` for a rational `q`

`acosRatBracket neg q w` encloses `arccos q` for an `AzRat` `q` with `0 < |q| < 1` (`neg`:
`q < 0`) at Ziv level `w`, by the half-angle identity of `AzFloat/AcosBracket.lean`,
`arccos a = 2 arctan √((1 − a)/(1 + a))`: here `Q = (1 − a)/(1 + a)` is an **exact rational**,
taken as the unreduced quotient `(den − num)/(den + num)` (no gcd: reducing it costs more than
the rest of the bracket for a `q` of many bits),
its square root is enclosed by the two directed roundings of `sqrtRatCore`, and the
arctangent is the doubled `atanWiden` — at the level `w + 8` plus half the number of leading
zero bits of `Q` for `q > 0` (relative accuracy for the small result next to `1`), `w + 8` for
`q < 0`, where the result is subtracted from `π`.

The proofs are in `Equiv/AcosRatBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The bracket of `arccos q` at Ziv level `w` for a rational `0 < |q| < 1`; `neg`: `q < 0`. -/
def acosRatBracket (neg : Bool) (q : AzRat) (w : Nat) : Encl :=
  let n := q.den - q.num
  let d := q.den + q.num
  let K := if neg then w + 8 else w + 8 + (d.size - (n.size + 2)) / 2
  let P := K + 64 + 8
  let A := atanWiden (sqrtRatCore n d P .Floor).1 (sqrtRatCore n d P .Ceiling).1 K (K + 64)
  let A2 : Encl := (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1)
  if neg then piShiftEncl false false A2 (w + 72) else A2

/-- The bracket of `arccos q` as a pair of `Roundable`s. -/
def acosRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox false (acosRatBracket (!q.sign) q w)

end Azurite.AzFloat
