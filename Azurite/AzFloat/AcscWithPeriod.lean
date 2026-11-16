/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AcscWithPeriodBracket
import Azurite.AzFloat.Equiv.AsecBracket
import Azurite.AzFloat.AsinWithPeriod

/-!
## The arccosecant with a period: `arccsc (x) u / (2π)`

`acscWithPeriodPrecRound x u p mode` is `arccsc (x) u / (2π) = arcsin (1/x) u / (2π)`, the
arccosecant of a float `x` measured in `u`ths of a turn for a `UInt64` `u` (degrees for
`u = 360`), in `[−u/4, u/4]`, correctly rounded to precision `p` in `mode`, with the comparison
against the exact value; `acscWithPeriod x u` rounds to nearest at the precision of `x`.  The
function is odd in `x`.

Special values:

* `NaN` gives `NaN`;
* `|x| < 1` gives `NaN`, including `0` and also for `u = 0`;
* `±∞` give `0` (there is no negative zero);
* `u = 0` gives `0` for `|x| ≥ 1`;
* `x = ±1` give `±u/4`, a quarter turn, rounded;
* `x = ±2` give `±u/12`, a twelfth of a turn, rounded (a float exactly when `u` is a multiple
  of `3` and the precision holds it; otherwise the correctly rounded rational).

Every other value is irrational — the exact values of the arccosecant are those of the arcsine
seen through the reciprocal (`irrational_acscPeriod_of_toVal`) — which certifies the Ziv loop
(`zivLoopCertified`, no fuel) on `acscPeriodApprox` (`AzFloat/AcscWithPeriodBracket.lean`).  A
huge `x` costs no more than any other.

The specification `acscWithPeriodPrecRound_eq` is in `Equiv/AcscWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `arccsc (x) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `|x| < 1`, and for `p = 0` unless the value is rational). -/
def acscWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (zero, .eq)
  | zero => (nan, .eq)
  | finite s e q m hv =>
    if h1 : eqIEEE (finite s e q m hv).abs one = true then
      setPrecRound (turnFraction s u 2) p mode
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then
      if hu : u.toNat = 0 then (zero, .eq)
      else if h2 : eqIEEE (finite s e q m hv).abs (one <<< AzInt.ofInt 1) = true then
        turnTwelfth s u p mode
      else if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        zivLoopCertified
          (acscPeriodApprox (!s) (finite s e q m hv) e.abs.toNat (AzNat.ofNat u.toNat)) p mode
          (p + zivGuardBits)
          (acscPeriodApprox_isSome_exists p mode (toVal_finite s e q m hv)
            (one_lt_abs_of_exponent (abs_finiteVal_bounds s e hv).1 he (fun h => by
              have habs : (finite s e q m hv).abs.toVal
                  = some ((|finiteVal s e m| : ℝ) : EReal) := by
                rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
                congr 1
              exact h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)))
            (fun h => by
              have habs : (finite s e q m hv).abs.toVal
                  = some ((|finiteVal s e m| : ℝ) : EReal) := by
                rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
                congr 1
              exact h2 ((eqIEEE_iff _ _).mpr ⟨_, habs, by
                rw [h, toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt]
                norm_num⟩))
            (finiteVal_neg_iff s e hv)
            (two_pow_le_of_exponent (abs_finiteVal_bounds s e hv).1 he)
            (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
            (by unfold zivGuardBits; omega))
    else (nan, .eq)

/-- `arccsc (x) u / (2π)` rounded to nearest at the precision of `x` (`0` for `x = ±∞`). -/
def acscWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (acscWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
