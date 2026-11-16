/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinWithPeriod
import Azurite.AzFloat.Equiv.AsinRatWithPeriodBracket

/-!
## The arcsine of a rational with a period: `arcsin (q) u / (2π)`

`asinRatWithPeriodPrecRound q u p mode` is `arcsin (q) u / (2π)`, the arcsine of an `AzRat` `q`
measured in `u`ths of a turn for a `UInt64` `u`, correctly rounded to precision `p` in `mode`,
with the comparison against the exact value; `asinRatWithPeriod q u p` rounds to nearest.

Special values, as for the float `asinWithPeriodPrecRound`: `q = 0` gives `0`; `q = ±1` give
`±u/4`, rounded; `|q| > 1` gives `NaN`, also for `u = 0`; `u = 0` gives `0` for `|q| ≤ 1`;
`q = ±1/2` give `±u/12`, the correctly rounded rational.  Every other value is irrational
(`irrational_asinPeriod_toRat`, Niven's theorem for the sine), which certifies the Ziv loop
(`zivLoopCertified`, no fuel) on `asinRatPeriodApprox`
(`AzFloat/AsinRatWithPeriodBracket.lean`).  The argument is never rounded to the target
precision, and a tiny `q` costs no more than any other.

The specification `asinRatWithPeriodPrecRound_eq` is in `Equiv/AsinRatWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `arcsin (q) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `|q| > 1`, and for `p = 0` unless the value is rational). -/
def asinRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if h1 : q.num = q.den then setPrecRound (turnFraction q.sign u 2) p mode
  else if hle : q.num ≤ q.den then
    if hu : u.toNat = 0 then (zero, .eq)
    else if hh : (q.abs + q.abs).num = (q.abs + q.abs).den then turnTwelfth q.sign u p mode
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (asinRatPeriodApprox q (AzNat.ofNat u.toNat)) p mode
        (p + zivGuardBits)
        (asinRatPeriodApprox_isSome_exists p mode q h0
          (lt_of_le_of_ne ((abs_toRat_le_one_iff q).mp hle)
            (fun h => h1 ((abs_toRat_eq_one_iff q).mp h)))
          (fun h => hh ((abs_toRat_eq_half_iff q).mp h))
          (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
          (by unfold zivGuardBits; omega))
  else (nan, .eq)

/-- `arcsin (q) u / (2π)` rounded to nearest at precision `p`. -/
def asinRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (asinRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
