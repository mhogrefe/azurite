/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Atan2WithPeriodBracket
import Azurite.AzFloat.Compare

/-!
## `atan2 (y, x)` with a period: `atan2 (y, x) u / (2π)`

`atan2WithPeriodPrecRound y x u p mode` is the angle of the point `(x, y)` measured in `u`ths of
a turn for a `UInt64` `u` (degrees for `u = 360`), in `(−u/2, u/2]`, correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `atan2WithPeriod y x u`
rounds to nearest at the larger of the precisions of the arguments.

There is no negative zero, so a zero argument behaves as `+0`:

* `NaN` in either argument gives `NaN`;
* `y = ±∞`: `±u/8` for `x = +∞`, `±3u/8` for `x = −∞`, `±u/4` for a finite `x`;
* `y` finite: `0` for `x = +∞`; `±u/2` with the sign of `y` for `x = −∞` (`u/2` for `y = 0`);
* `y = 0`: `0` for `x ≥ 0`, `u/2` for `x < 0`;
* `x = 0`, `y ≠ 0`: `±u/4`;
* `|y| = |x|` (finite, nonzero): `±u/8` for `x > 0`, `±3u/8` for `x < 0`;
* `u = 0`: `0` for all arguments other than `NaN`.

All of these are rational and returned as the rounding of the exact value (`turnFracN`).  Every
other value is irrational (`irrational_arg_mul_div_two_pi`, from Niven's theorem for the
tangent), which certifies the Ziv loop (`zivLoopCertified`, no fuel) on `atan2PeriodApprox`
(`AzFloat/Atan2WithPeriodBracket.lean`).

**Values next to a rational one.**  For a very unequal pair the value is within `2^(−|ey − ex|)`
of `0`, `±u/4` or `±u/2`, which are floats.  The quarter and half turns enter the enclosure as
exact floats, and the loop runs on the value or on its negative (`atan2PeriodOrient`, the result
negated back in the negated mode) so that the exact end is always the lower one, which
`roundingPossible` accepts: the cost does not grow with the exponents.

The specification `atan2WithPeriodPrecRound_eq` is in `Equiv/Atan2WithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `± n u 2^(−k)` as a float (`pos`: the sign is positive). -/
def turnFracN (pos : Bool) (n : Nat) (u : UInt64) (k : Nat) : AzFloat :=
  let f := ofAzNat (AzNat.ofNat (n * u.toNat)) <<< AzInt.ofInt (-(k : Int))
  if pos then f else -f

/-- `atan2 (y, x) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0` unless the value is rational). -/
def atan2WithPeriodPrecRound (y x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match y with
  | nan => (nan, .eq)
  | zero =>
    match x with
    | nan => (nan, .eq)
    | zero => (zero, .eq)
    | infinity sx => if sx then (zero, .eq) else setPrecRound (turnFracN true 1 u 1) p mode
    | finite sx _ _ _ _ =>
      if sx then (zero, .eq) else setPrecRound (turnFracN true 1 u 1) p mode
  | infinity sy =>
    match x with
    | nan => (nan, .eq)
    | infinity sx =>
      if sx then setPrecRound (turnFracN sy 1 u 3) p mode
      else setPrecRound (turnFracN sy 3 u 3) p mode
    | _ => setPrecRound (turnFracN sy 1 u 2) p mode
  | finite sy ey qy my hvy =>
    match x with
    | nan => (nan, .eq)
    | zero => setPrecRound (turnFracN sy 1 u 2) p mode
    | infinity sx => if sx then (zero, .eq) else setPrecRound (turnFracN sy 1 u 1) p mode
    | finite sx ex qx mx hvx =>
      if hu : u.toNat = 0 then (zero, .eq)
      else if h1 : eqIEEE (finite sy ey qy my hvy).abs (finite sx ex qx mx hvx).abs = true then
        setPrecRound (turnFracN sy (if sx then 1 else 3) u 3) p mode
      else if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        let o := atan2PeriodOrient (finite sy ey qy my hvy) (finite sx ex qx mx hvx) sx
        let r := zivLoopCertified
          (atan2PeriodApprox o (finite sy ey qy my hvy) (finite sx ex qx mx hvx) ey ex sx
            (AzNat.ofNat u.toNat)) p (if o = !sy then mode else -mode) (p + zivGuardBits)
          (atan2PeriodApprox_isSome_exists p _ o (toVal_finite sy ey qy my hvy)
            (toVal_finite sx ex qx mx hvx) (finiteVal_ne_zero sy ey hvy)
            (finiteVal_ne_zero sx ex hvx)
            (fun h => by
              have hya : (finite sy ey qy my hvy).abs.toVal
                  = some ((|finiteVal sy ey my| : ℝ) : EReal) := by
                rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
                congr 1
              have hxa : (finite sx ex qx mx hvx).abs.toVal
                  = some ((|finiteVal sx ex mx| : ℝ) : EReal) := by
                rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
                congr 1
              exact h1 ((eqIEEE_iff _ _).mpr ⟨_, hya, by rw [h]; exact hxa⟩))
            (finiteVal_sign_iff sx ex hvx)
            (abs_finiteVal_bounds sy ey hvy).2 (abs_finiteVal_bounds sx ex hvx).1
            (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
            (by unfold zivGuardBits; omega))
        if o = !sy then r else (-r.1, r.2.swap)

/-- `atan2 (y, x) u / (2π)` rounded to nearest at the larger of the precisions of `y`, `x`. -/
def atan2WithPeriod (y x : AzFloat) (u : UInt64) : AzFloat :=
  (atan2WithPeriodPrecRound y x u (max (y.precision?.getD 1) (x.precision?.getD 1))
    .Nearest).1

end Azurite.AzFloat
