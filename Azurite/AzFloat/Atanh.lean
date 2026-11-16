/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AtanhBracket
import Azurite.AzFloat.LnP1

/-!
## The inverse hyperbolic tangent

`atanhPrecRound x p mode` is `atanh x = (1/2) ln ((1 + x)/(1 − x))`, defined for `|x| ≤ 1`,
correctly rounded to precision `p` in `mode`, with the comparison against the exact value;
`atanh x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `atanhApprox`
(`AzFloat/AtanhBracket.lean`): half the logarithm of a float just below
`(1 + |x|)/(1 − |x|)`.  The loop terminates because `atanh q` is irrational for every rational
`0 < |q| < 1` (`irrational_artanh_rat`: its hyperbolic tangent is rational).

**Extreme arguments.**  A tiny `x` (`|x| < 2^e`, `e ≤ −(max p q + 72)`) is rounded by one test
(`tanTiny?`: `|x| < atanh |x| ≤ |x| + |x|³`).  A small `x` above that starts the loop with
`−e` more bits.  Next to `±1` the result is large, `≈ (1/2) ln (2/(1 − |x|))`, and `1 − |x|`
is rounded with relative accuracy.

Special values: `atanh NaN = NaN`; `atanh (±∞) = NaN`; `atanh x = NaN` for `|x| > 1`;
`atanh (±1) = ±∞`; `atanh 0 = 0` exactly.  The function is odd: `atanhPrecRound (−x) p mode` is
the negation of `atanhPrecRound x p (−mode)`.
-/

namespace Azurite.AzFloat

/-- `atanh x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|x| > 1`, and for `p = 0` and a finite `0 < |x| < 1`). -/
def atanhPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if eqIEEE (finite s e q m hv).abs one = true then (infinity s, .eq)
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then (nan, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match tanTiny? s (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
      zivLoopCertified (atanhApprox (!s) (finite s e q m hv)) p mode
        (p + zivGuardBits + leadingZeroBits e)
        (atanhApprox_isSome_exists p mode (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          (abs_lt_one_of_exponent (abs_finiteVal_bounds s e hv).2 he)
          (finiteVal_neg_iff s e hv) _ (by unfold zivGuardBits; omega))

/-- `atanh x` rounded to nearest at the precision of `x`. -/
def atanh (x : AzFloat) : AzFloat := (atanhPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
