/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AsinWithPeriodBracket
import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.Compare

/-!
## The arcsine with a period: `arcsin (x) u / (2π)`

`asinWithPeriodPrecRound x u p mode` is `arcsin (x) u / (2π)`, the arcsine of a float `x`
measured in `u`ths of a turn for a `UInt64` `u` (degrees for `u = 360`), correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `asinWithPeriod x u`
rounds to nearest at the precision of `x`.

Special values:

* `NaN` and `±∞` give `NaN`;
* `|x| > 1` gives `NaN`, also for `u = 0`;
* `x = 0` gives `0` (there is no negative zero);
* `u = 0` gives `0` for `|x| ≤ 1`;
* `x = ±1` give `±u/4`, a quarter turn, rounded;
* `x = ±1/2` give `±u/12`, a twelfth of a turn, rounded (a float exactly when `u` is a multiple
  of `3` and the precision holds it; otherwise the correctly rounded rational).

These are the only rational values: for `|x| < 1`, `|x| ∉ {0, 1/2}` and `u ≠ 0` the value is
irrational by Niven's theorem for the sine (`irrational_arcsin_rat_mul_div_two_pi`), which
certifies the Ziv loop (`zivLoopCertified`, no fuel) on `asinPeriodApprox`
(`AzFloat/AsinWithPeriodBracket.lean`).  A tiny `x` costs no more than any other.

The specification `asinWithPeriodPrecRound_eq` is in `Equiv/AsinWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `± u/12` rounded to precision `p` with `mode` (`pos`: the sign is positive): the correctly
rounded rational. -/
def turnTwelfth (pos : Bool) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  let r := AzRat.ofAzNats (AzNat.ofNat u.toNat) (AzNat.ofNat 12)
  ofAzRatRound (if pos then r else -r) p mode

/-- `arcsin (x) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `|x| > 1`, and for `p = 0` unless the value is rational). -/
def asinWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if eqIEEE (finite s e q m hv).abs one = true then setPrecRound (turnFraction s u 2) p mode
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then (nan, .eq)
    else if hu : u.toNat = 0 then (zero, .eq)
    else if hh : eqIEEE (finite s e q m hv).abs (one <<< AzInt.ofInt (-1)) = true then
      turnTwelfth s u p mode
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified
        (asinPeriodApprox (!s) (finite s e q m hv) e (AzNat.ofNat u.toNat)) p mode
        (p + zivGuardBits)
        (asinPeriodApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
          (finiteVal_ne_zero s e hv)
          (abs_lt_one_of_exponent (abs_finiteVal_bounds s e hv).2 he)
          (fun h => by
            have habs : (finite s e q m hv).abs.toVal
                = some ((|finiteVal s e m| : ℝ) : EReal) := by
              rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
              congr 1
            exact hh ((eqIEEE_iff _ _).mpr ⟨_, habs, by
              rw [h, toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt]
              norm_num⟩))
          (finiteVal_neg_iff s e hv) (abs_finiteVal_bounds s e hv).2
          (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `arcsin (x) u / (2π)` rounded to nearest at the precision of `x`. -/
def asinWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (asinWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
