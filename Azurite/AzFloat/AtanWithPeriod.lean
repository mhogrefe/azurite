/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AtanWithPeriodBracket
import Azurite.AzFloat.Compare

/-!
## The arctangent with a period: `arctan (x) u / (2π)`

`atanWithPeriodPrecRound x u p mode` is `arctan (x) u / (2π)`, the arctangent of a float `x`
measured in `u`ths of a turn for a `UInt64` `u` (degrees for `u = 360`), correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `atanWithPeriod x u`
rounds to nearest at the precision of `x`.

Special values:

* `NaN` gives `NaN`;
* `±∞` give `±u/4`, a quarter turn, rounded;
* `x = 0` gives `0` (there is no negative zero);
* `u = 0` gives `0` for every `x` other than `NaN`;
* `x = ±1` give `±u/8`, an eighth of a turn, rounded.

These are the only rational values: for a finite `x ∉ {0, ±1}` and `u ≠ 0` the value is
irrational by Niven's theorem for the tangent (`irrational_arctan_rat_mul_div_two_pi`), which
certifies the Ziv loop (`zivLoopCertified`, no fuel) on `atanPeriodApprox`
(`AzFloat/AtanWithPeriodBracket.lean`).  A tiny `x` costs no more than any other: the bracket
of `arctan |x|` is then `[|x| − |x| 2^(2e), |x|]`.

The specification `atanWithPeriodPrecRound_eq` is in `Equiv/AtanWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `± u 2^(−k)` as a float (`pos`: the sign is positive). -/
def turnFraction (pos : Bool) (u : UInt64) (k : Nat) : AzFloat :=
  let f := ofAzNat (AzNat.ofNat u.toNat) <<< AzInt.ofInt (-(k : Int))
  if pos then f else -f

/-- `arctan (x) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0` unless the value is `0`, `±u/4` or `±u/8`). -/
def atanWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => setPrecRound (turnFraction s u 2) p mode
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hu : u.toNat = 0 then (zero, .eq)
    else if h1 : eqIEEE (finite s e q m hv).abs one = true then
      setPrecRound (turnFraction s u 3) p mode
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (atanPeriodApprox (!s) (finite s e q m hv) e (AzNat.ofNat u.toNat)) p
        mode (p + zivGuardBits)
        (atanPeriodApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
          (finiteVal_ne_zero s e hv)
          (fun h => by
            have habs : (finite s e q m hv).abs.toVal
                = some ((|finiteVal s e m| : ℝ) : EReal) := by
              rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
              congr 1
            exact h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩))
          (finiteVal_neg_iff s e hv)
          (abs_finiteVal_bounds s e hv).1 (abs_finiteVal_bounds s e hv).2
          (by rw [AzNat.toNat_ofNat]; exact hu)
          (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `arctan (x) u / (2π)` rounded to nearest at the precision of `x`. -/
def atanWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (atanWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
