/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinBracket
import Azurite.AzFloat.SqrtRat
import Azurite.AzFloat.TanRatBracket
import Azurite.AzRat.Sub
import Azurite.AzRat.Mul

/-!
## The bracket of `arcsin q` for a rational `q`

`asinRatBracket q w` encloses `arcsin |q|` for an `AzRat` `q` with `0 < |q| < 1` at Ziv level
`w`, by the half-angle identity of `AzFloat/AsinBracket.lean`,
`arcsin a = 2 arctan (a / (1 + √(1 − a²)))`: here `1 − a²` is an exact rational, its square root
is enclosed by the two directed roundings of `sqrtRatPrecRound`, `a` by its two directed
roundings, and `asinArgOf` forms the quotient; the arctangent is the doubled `atanWiden` at the
level `K = atanWork (ratExpBound q) w` (relative accuracy), `V = K + 64`, the argument at
`V + 8` bits.

`asinRatApprox` negates and swaps the ends for `q < 0`; `asinTinyRat?` is the tiny-argument
path, the test of `tanTinyRat?` (`arcsin |q| ∈ (|q|, |q| + |q|³]`).

The proofs are in `Equiv/AsinRatBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The bracket of `arcsin |q|` at Ziv level `w` for a rational `0 < |q| < 1`. -/
def asinRatBracket (q : AzRat) (w : Nat) : Encl :=
  let a := q.abs
  let K := atanWork (ratExpBound q) w
  let P := K + 64 + 8
  let r := 1 - a * a
  let s : Encl := ((sqrtRatPrecRound r P .Floor).1, (sqrtRatPrecRound r P .Ceiling).1)
  let t := asinArgOf (ofAzRatRound a P .Floor).1 (ofAzRatRound a P .Ceiling).1 s P
  let A := atanWiden t.1 t.2 K (K + 64)
  (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1)

/-- The bracket of `arcsin q` as a pair of `Roundable`s (negated and swapped for `q < 0`). -/
def asinRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox (!q.sign) (asinRatBracket q w)

/-- The tiny-argument path of `arcsin q`: the test of `tanTinyRat?` (`|q| < 2^e`,
`e ≤ −(p + 72)`), valid because `|q| < arcsin |q| ≤ |q| + |q|³`. -/
def asinTinyRat? (q : AzRat) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  tanTinyRat? q p mode

end Azurite.AzFloat
