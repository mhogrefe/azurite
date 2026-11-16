/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AcothBracket

/-!
## The inverse hyperbolic cotangent

`acothPrecRound x p mode` is `acoth x = atanh (1/x) = (1/2) ln ((x + 1)/(x − 1))`, defined for
`|x| ≥ 1`, correctly rounded to precision `p` in `mode`, with the comparison against the exact
value; `acoth x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `acothApprox`
(`AzFloat/AcothBracket.lean`).  The loop terminates because `atanh q` is irrational for every
rational `0 < |q| < 1` (`irrational_artanh_rat`), here `q = 1/x`.

**Oddness.**  The loop always runs on `acoth |x|`; for `x < 0` the mode is negated and the
result is negated, so `acothPrecRound (−x) p mode` is the negation of
`acothPrecRound x p (−mode)`.

**Extreme arguments.**  For a huge `x` the result is `≈ 1/x`, enclosed with relative accuracy
by two divisions, at a cost that does not grow with the exponent.  When `x` is a power of two
the value `1/x + 1/(3x³) + …` is exponentially close to the float `1/x`, from above; that float
is the exact lower end of the enclosure — this is why the loop runs on the absolute value.
Next to `±1` the result is large, `≈ (1/2) ln (2/(|x| − 1))`.

Special values: `acoth NaN = NaN`; `acoth (±∞) = 0` (there is no negative zero);
`acoth (±1) = ±∞`; `acoth x = NaN` for `|x| < 1`, including `0`.
-/

namespace Azurite.AzFloat

/-- `acoth x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|x| < 1`, and for `p = 0` and a finite `|x| > 1`). -/
def acothPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (zero, .eq)
  | zero => (nan, .eq)
  | finite s e q m hv =>
    if h1 : eqIEEE (finite s e q m hv).abs one = true then (infinity s, .eq)
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        let r := zivLoopCertified (acothApprox (finite s e q m hv) e) p
          (if !s then -mode else mode) (p + zivGuardBits + acschExtra e p)
          (acothApprox_isSome_exists p _ (toVal_finite s e q m hv)
            (one_lt_abs_of_exponent (abs_finiteVal_bounds s e hv).1 he (fun h => by
              have habs : (finite s e q m hv).abs.toVal
                  = some ((|finiteVal s e m| : ℝ) : EReal) := by
                rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
                congr 1
              exact h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)))
            he (abs_finiteVal_bounds s e hv).1 _ (by unfold zivGuardBits; omega))
        if !s then (-r.1, r.2.swap) else r
    else (nan, .eq)

/-- `acoth x` rounded to nearest at the precision of `x`. -/
def acoth (x : AzFloat) : AzFloat := (acothPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
