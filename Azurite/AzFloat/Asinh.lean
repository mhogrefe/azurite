/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AsinhBracket
import Azurite.AzFloat.LnP1

/-!
## The inverse hyperbolic sine

`asinhPrecRound x p mode` is `asinh x = ln (x + √(x² + 1))` correctly rounded to precision `p`
in `mode`, with the comparison against the exact value; `asinh x` rounds to nearest at the
precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `asinhApprox`
(`AzFloat/AsinhBracket.lean`): the logarithm of a float just below `|x| + √(x² + 1)`.  The loop
terminates because `asinh q` is irrational for every rational `q ≠ 0`
(`irrational_arsinh_rat`: its hyperbolic sine is rational).

**Extreme arguments.**  A tiny `x` (`|x| < 2^e`, `e ≤ −(max p q + 72)`) is rounded by one test
(`sinTiny?`: `|x| − |x|³ ≤ asinh |x| < |x|`).  A small `x` above that starts the loop with
`−e` more bits (the logarithm is accurate absolutely, the result is `≈ x`).  A huge `x` gives
`≈ ln (2|x|)` and costs one logarithm.

Special values: `asinh NaN = NaN`, `asinh (±∞) = ±∞`, `asinh 0 = 0` exactly.  The function is
odd: `asinhPrecRound (−x) p mode` is the negation of `asinhPrecRound x p (−mode)`.
-/

namespace Azurite.AzFloat

/-- `asinh x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` and a finite `x ≠ 0`). -/
def asinhPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => (infinity s, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match sinTiny? s (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
      zivLoopCertified (asinhApprox (!s) (finite s e q m hv)) p mode
        (p + zivGuardBits + leadingZeroBits e)
        (asinhApprox_isSome_exists p mode (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          (finiteVal_neg_iff s e hv) _ (by unfold zivGuardBits; omega))

/-- `asinh x` rounded to nearest at the precision of `x`. -/
def asinh (x : AzFloat) : AzFloat := (asinhPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
