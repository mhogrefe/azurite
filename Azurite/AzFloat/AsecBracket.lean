/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosBracket

/-!
## The bracket of `arcsec x`

`arcsec x = arccos (1/x)` for `|x| ≥ 1`.  For `a > 1` the half-angle identity of the arccosine
becomes

  `arcsec a = 2 arctan t`,  `t = √((a − 1)/(a + 1))`,

with `t ∈ (0, 1)` and **no reciprocal**; and `arcsec (−a) = π − arcsec a`.

* The argument `t` is `diffQuotSqrt a 1` (`AzFloat/AcosBracket.lean`): the correctly rounded
  `a − 1` and `a + 1`, their quotient and its square root, all with relative accuracy, so `t`
  is accurate for `a` next to `1`, where `arcsec a ≈ √(2 (a − 1))` is small.
* `asecWork a w` is the level of the arctangent for `x > 0`: `w + 8` plus half the number of
  leading zero bits of `a − 1` (read off a 64-bit rounding).
* `asecBracket neg x w` encloses `arcsec x` (`neg`: `x < 0`), with width at most `2^(−w)`;
  `asecApprox` is the pair of `Roundable`s for the Ziv loop of `AzFloat/Asec.lean`.

A huge `x` needs nothing special: `arcsec x` is next to the irrational `π/2`, and no working
precision grows with the exponent.

The proofs are in `Equiv/AsecBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The level of the arctangent for `arcsec a`, `a > 1`, at Ziv level `w`. -/
def asecWork (a : AzFloat) (w : Nat) : Nat :=
  w + 8 + match (subPrecRound a one 64 .Ceiling).1.exponent? with
    | some e => if e.sign then 0 else e.abs.toNat / 2
    | none => 0

/-- The bracket of `arcsec x` at Ziv level `w` for a finite `x` with `|x| > 1`; `neg`:
`x < 0`. -/
def asecBracket (neg : Bool) (x : AzFloat) (w : Nat) : Encl :=
  let a := x.abs
  let K := if neg then w + 8 else asecWork a w
  let t := diffQuotSqrt a one (K + 64 + 8)
  let A := atanWiden t.1 t.2 K (K + 64)
  let A2 : Encl := (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1)
  if neg then piShiftEncl false false A2 (w + 72) else A2

/-- The bracket of `arcsec x` as a pair of `Roundable`s. -/
def asecApprox (neg : Bool) (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  enclApprox false (asecBracket neg x w)

end Azurite.AzFloat
