/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AsechBracket

/-!
## The inverse hyperbolic secant

`asechPrecRound x p mode` is `asech x = acosh (1/x) = ln ((1 + √(1 − x²))/x)`, defined for
`0 ≤ x ≤ 1`, correctly rounded to precision `p` in `mode`, with the comparison against the
exact value; `asech x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `asechApprox`
(`AzFloat/AsechBracket.lean`): the logarithm of a float just below
`(1 + √((1 − x)(1 + x)))/x`.  The loop terminates because `acosh q` is irrational for every
rational `q > 1` (`irrational_arcosh_rat`), here `q = 1/x`.

**Extreme arguments.**  Next to `1` the result is `≈ √(2 (1 − x))`; `1 − x` is rounded with
relative accuracy and the loop starts with half its leading zero bits more (`acoshExtra`).  A
tiny `x` gives `≈ ln (2/x)` and costs one logarithm.

Special values: `asech NaN = NaN`; `asech (±∞) = NaN`; `asech x = NaN` for `x < 0` and for
`x > 1`; `asech 0 = +∞`; `asech 1 = 0` exactly (the only exact case).
-/

namespace Azurite.AzFloat

/-- `asech x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `x < 0` and `x > 1`, and for `p = 0` and `0 < x < 1`). -/
def asechPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (infinity true, .eq)
  | finite s e q m hv =>
    if hs : s = true then
      if eqIEEE (finite s e q m hv) one = true then (zero, .eq)
      else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then (nan, .eq)
      else if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        zivLoopCertified (asechApprox (finite s e q m hv)) p mode
          (p + zivGuardBits + acoshExtra (subPrecRound one (finite s e q m hv) q .Floor).1)
          (asechApprox_isSome_exists p mode (toVal_finite s e q m hv)
            ((finiteVal_sign_iff s e hv).mp hs)
            (lt_of_le_of_lt (le_abs_self _)
              (abs_lt_one_of_exponent (abs_finiteVal_bounds s e hv).2 he)) _
            (by unfold zivGuardBits; omega))
    else (nan, .eq)

/-- `asech x` rounded to nearest at the precision of `x`. -/
def asech (x : AzFloat) : AzFloat := (asechPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
