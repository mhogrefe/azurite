/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosWithPeriod

/-!
## The arccosine of a rational with a period: `arccos (q) u / (2π)`

`acosRatWithPeriodPrecRound q u p mode` is `arccos (q) u / (2π)`, the arccosine of an `AzRat`
`q` measured in `u`ths of a turn for a `UInt64` `u`, in `[0, u/2]`, correctly rounded to
precision `p` in `mode`, with the comparison against the exact value;
`acosRatWithPeriod q u p` rounds to nearest.

Special values, as for the float `acosWithPeriodPrecRound`: `NaN` for `|q| > 1`, also for
`u = 0`; `q = 0` gives `u/4`; `q = 1` gives `0` and `q = −1` gives `u/2`; `u = 0` gives `0`;
`q = 1/2` gives `u/6` and `q = −1/2` gives `u/3` — all returned as the correctly rounded
rational.  Every other value is irrational (`irrational_acosPeriod_toRat`), which certifies the
Ziv loop (`zivLoopCertified`, no fuel) on `acosRatPeriodApprox`
(`AzFloat/AcosWithPeriodBracket.lean`), run in the orientation `acosPeriodOrientOf`.  The
argument is never rounded to the target precision, and a tiny `q` (a value next to `u/4`)
costs no more than any other.

The specification `acosRatWithPeriodPrecRound_eq` is in `Equiv/AcosRatWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `arccos (q) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `|q| > 1`, and for `p = 0`). -/
def acosRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : q.num = 0 then (if p = 0 then (nan, .eq) else turnRatio u 1 4 p mode)
  else if h1 : q.num = q.den then
    (if q.sign then (zero, .eq) else if p = 0 then (nan, .eq) else turnRatio u 1 2 p mode)
  else if hle : q.num ≤ q.den then
    if hu : u.toNat = 0 then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else if hh : (q.abs + q.abs).num = (q.abs + q.abs).den then
      (if q.sign then turnRatio u 1 6 p mode else turnRatio u 1 3 p mode)
    else
      haveI : NeZero p := ⟨hp⟩
      let o := acosPeriodOrientOf (ratAbsLeHalf q) q.sign
      let r := zivLoopCertified (acosRatPeriodApprox o q (AzNat.ofNat u.toNat)) p
        (if o then -mode else mode) (p + zivGuardBits)
        (acosRatPeriodApprox_isSome_exists p _ o q h0
          (lt_of_le_of_ne ((abs_toRat_le_one_iff q).mp hle)
            (fun h => h1 ((abs_toRat_eq_one_iff q).mp h)))
          (fun h => hh ((abs_toRat_eq_half_iff q).mp h))
          (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
          (by unfold zivGuardBits; omega))
      if o then (-r.1, r.2.swap) else r
  else (nan, .eq)

/-- `arccos (q) u / (2π)` rounded to nearest at precision `p`. -/
def acosRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (acosRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
