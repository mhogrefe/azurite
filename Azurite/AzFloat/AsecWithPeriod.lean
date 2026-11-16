/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AsecWithPeriodBracket
import Azurite.AzFloat.AcosWithPeriod

/-!
## The arcsecant with a period: `arcsec (x) u / (2π)`

`asecWithPeriodPrecRound x u p mode` is `arcsec (x) u / (2π) = arccos (1/x) u / (2π)`, the
arcsecant of a float `x` measured in `u`ths of a turn for a `UInt64` `u` (degrees for
`u = 360`), in `[0, u/2]`, correctly rounded to precision `p` in `mode`, with the comparison
against the exact value; `asecWithPeriod x u` rounds to nearest at the precision of `x`.

Special values:

* `NaN` gives `NaN`;
* `|x| < 1` gives `NaN`, including `0` and also for `u = 0`;
* `±∞` give `u/4`, a quarter turn;
* `u = 0` gives `0` for `|x| ≥ 1`;
* `x = 1` gives `0`, `x = −1` gives `u/2`, a half turn;
* `x = 2` gives `u/6` and `x = −2` gives `u/3`.

All of these are rational and are returned as the correctly rounded rational (`turnRatio`).
Every other value is irrational — the exact values of the arcsecant are those of the arccosine
seen through the reciprocal (`irrational_asecPeriod_of_toVal`) — which certifies the Ziv loop
(`zivLoopCertified`, no fuel) on `asecPeriodApprox` (`AzFloat/AsecWithPeriodBracket.lean`).

**Values next to a rational one.**  For a huge `x` the value is within `2^(−e)` of the float
`u/4`; the quarter turn enters the enclosure as an exact float and the loop runs in the
orientation `acosPeriodOrientOf`, so the cost does not grow with the exponent.

The specification `asecWithPeriodPrecRound_eq` is in `Equiv/AsecWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `arcsec (x) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `|x| < 1`, and for `p = 0`). -/
def asecWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => if p = 0 then (nan, .eq) else turnRatio u 1 4 p mode
  | zero => (nan, .eq)
  | finite s e q m hv =>
    if h1 : eqIEEE (finite s e q m hv).abs one = true then
      (if s then (zero, .eq) else if p = 0 then (nan, .eq) else turnRatio u 1 2 p mode)
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then
      if hu : u.toNat = 0 then (zero, .eq)
      else if hp : p = 0 then (nan, .eq)
      else if h2 : eqIEEE (finite s e q m hv).abs (one <<< AzInt.ofInt 1) = true then
        (if s then turnRatio u 1 6 p mode else turnRatio u 1 3 p mode)
      else
        haveI : NeZero p := ⟨hp⟩
        let o := acosPeriodOrientOf (le (one <<< AzInt.ofInt 1) (finite s e q m hv).abs) s
        let r := zivLoopCertified
          (asecPeriodApprox o s (finite s e q m hv) (AzNat.ofNat u.toNat)) p
          (if o then -mode else mode) (p + zivGuardBits)
          (asecPeriodApprox_isSome_exists p _ o (toVal_finite s e q m hv)
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
            (finiteVal_sign_iff s e hv) (by rw [AzNat.toNat_ofNat]; exact hu)
            (p + zivGuardBits) (by unfold zivGuardBits; omega))
        if o then (-r.1, r.2.swap) else r
    else (nan, .eq)

/-- `arcsec (x) u / (2π)` rounded to nearest at the precision of `x` (at precision `1` for
`x = ±∞`). -/
def asecWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (asecWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
