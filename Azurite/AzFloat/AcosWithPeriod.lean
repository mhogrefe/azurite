/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AcosWithPeriodBracket
import Azurite.AzFloat.Compare

/-!
## The arccosine with a period: `arccos (x) u / (2π)`

`acosWithPeriodPrecRound x u p mode` is `arccos (x) u / (2π)`, the arccosine of a float `x`
measured in `u`ths of a turn for a `UInt64` `u` (degrees for `u = 360`), in `[0, u/2]`,
correctly rounded to precision `p` in `mode`, with the comparison against the exact value;
`acosWithPeriod x u` rounds to nearest at the precision of `x`.

Special values:

* `NaN` and `±∞` give `NaN`;
* `|x| > 1` gives `NaN`, also for `u = 0`;
* `x = 0` gives `u/4`, a quarter turn;
* `u = 0` gives `0` for `|x| ≤ 1`;
* `x = 1` gives `0`, `x = −1` gives `u/2`, a half turn;
* `x = 1/2` gives `u/6` and `x = −1/2` gives `u/3`.

All of these are rational and are returned as the correctly rounded rational (`turnRatio`; a
float exactly when it is dyadic and the precision holds it — for the sixth and the third, when
`u` is a multiple of `3`).  Every other value is irrational
(`irrational_arccos_rat_mul_div_two_pi`, Niven's theorem for the cosine), which certifies the
Ziv loop (`zivLoopCertified`, no fuel) on `acosPeriodApprox`
(`AzFloat/AcosWithPeriodBracket.lean`).

**Values next to a rational one.**  For a tiny `x` the value is within `2^(−|e|)` of the float
`u/4`.  The quarter and half turns enter the enclosure as exact floats and the loop runs in the
orientation `acosPeriodOrientOf` (on the negative value, the result negated back in the negated
mode, except just above `u/4`), so the cost does not grow with the exponent.

The specification `acosWithPeriodPrecRound_eq` is in `Equiv/AcosWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `n u / d` rounded to precision `p` with `mode`: the correctly rounded rational. -/
def turnRatio (u : UInt64) (n d : Nat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  ofAzRatRound (AzRat.ofAzNats (AzNat.ofNat (n * u.toNat)) (AzNat.ofNat d)) p mode

/-- `arccos (x) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `|x| > 1`, and for `p = 0`). -/
def acosWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => if p = 0 then (nan, .eq) else turnRatio u 1 4 p mode
  | finite s e q m hv =>
    if eqIEEE (finite s e q m hv).abs one = true then
      (if s then (zero, .eq) else if p = 0 then (nan, .eq) else turnRatio u 1 2 p mode)
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then (nan, .eq)
    else if hu : u.toNat = 0 then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else if hh : eqIEEE (finite s e q m hv).abs (one <<< AzInt.ofInt (-1)) = true then
      (if s then turnRatio u 1 6 p mode else turnRatio u 1 3 p mode)
    else
      haveI : NeZero p := ⟨hp⟩
      let o := acosPeriodOrientOf (le (finite s e q m hv).abs (one <<< AzInt.ofInt (-1))) s
      let r := zivLoopCertified
        (acosPeriodApprox o s (finite s e q m hv) e (AzNat.ofNat u.toNat)) p
        (if o then -mode else mode) (p + zivGuardBits)
        (acosPeriodApprox_isSome_exists p _ o (toVal_finite s e q m hv)
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
          (abs_finiteVal_bounds s e hv).2 (finiteVal_sign_iff s e hv)
          (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
          (by unfold zivGuardBits; omega))
      if o then (-r.1, r.2.swap) else r

/-- `arccos (x) u / (2π)` rounded to nearest at the precision of `x` (at precision `1` for
`x = 0`). -/
def acosWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (acosWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
