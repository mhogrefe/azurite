/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AsinBracket
import Azurite.AzFloat.Atan2
import Azurite.AzFloat.PiConstants

/-!
## The arcsine

`asinPrecRound x p mode` is `arcsin x` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `asin x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `asinApprox` (`AzFloat/AsinBracket.lean`):
`arcsin |x| = 2 arctan (|x| / (1 + √(1 − x²)))`, the arctangent by the levels of
`AzFloat/AtanBracket.lean`.  The loop terminates because `arcsin x` is irrational for every
nonzero float `x` in `[−1, 1]` (`irrational_arcsin_rat`, from `irrational_sin_rat`).

**Extreme arguments.**  Tiny `x` (`|x| < 2^e`, `e ≤ −(max p q + 72)`) never reach the loop:
`asinTiny?` rounds from `|x| < arcsin |x| ≤ |x| + |x|³` by one test, at a cost independent of
`e`.  Small `x` above that threshold are computed with relative accuracy.  Near `±1` the
difference `1 − |x|` is correctly rounded, so `√(1 − x²)` keeps its relative accuracy.

Special values: `arcsin NaN = NaN`; `arcsin x = NaN` for `|x| > 1`, in particular for `±∞`;
`arcsin (±1) = ±π/2` (correctly rounded); `arcsin 0 = 0` exactly.
-/

namespace Azurite.AzFloat

/-- `arcsin x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|x| > 1`, and for `p = 0` unless the value is `0`). -/
def asinPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if eqIEEE (finite s e q m hv).abs one = true then signedRound s piDiv2PrecRound p mode
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then (nan, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match asinTiny? s (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
        zivLoopCertified (asinApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
          (asinApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
            (finiteVal_ne_zero s e hv)
            (abs_lt_one_of_exponent (abs_finiteVal_bounds s e hv).2 he)
            (finiteVal_neg_iff s e hv) e (p + zivGuardBits)
            (by unfold zivGuardBits; omega))

/-- `arcsin x` rounded to nearest at the precision of `x`. -/
def asin (x : AzFloat) : AzFloat := (asinPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
