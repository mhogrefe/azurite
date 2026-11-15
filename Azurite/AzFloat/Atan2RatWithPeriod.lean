/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2WithPeriod
import Azurite.AzFloat.Equiv.Atan2RatWithPeriodBracket

/-!
## `atan2 (y, x) u / (2π)` for rationals

`atan2RatWithPeriodPrecRound y x u p mode` is the angle of the point `(x, y)` with `AzRat`
coordinates, measured in `u`ths of a turn for a `UInt64` `u`, in `(−u/2, u/2]`, correctly rounded
to precision `p` in `mode`, with the comparison against the exact value;
`atan2RatWithPeriod y x u p` rounds to nearest.

Rational values, returned as the rounding of the exact value: `y = 0` gives `0` for `x ≥ 0` and
`u/2` for `x < 0`; `x = 0`, `y ≠ 0` gives `±u/4`; `|y| = |x|` gives `±u/8` for `x > 0` and
`±3u/8` for `x < 0`; `u = 0` gives `0`.  Every other value is irrational
(`irrational_arg_mul_div_two_pi`), which certifies the Ziv loop (`zivLoopCertified`, no fuel) on
`atan2RatPeriodApprox` (`AzFloat/Atan2RatWithPeriodBracket.lean`), run in the orientation
`atan2RatPeriodOrient`: the quotient `|y|/|x|` is formed as a rational, and a value next to a
quarter or half turn costs nothing extra.

The specification `atan2RatWithPeriodPrecRound_eq` is in `Equiv/Atan2RatWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `atan2 (y, x) u / (2π)` for rationals, rounded to precision `p` with `mode`, and the
comparison with the exact value (`(nan, .eq)` for `p = 0` unless the value is rational). -/
def atan2RatWithPeriodPrecRound (y x : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hy : y.num = 0 then
    (if x.sign then (zero, .eq) else setPrecRound (turnFracN true 1 u 1) p mode)
  else if hx : x.num = 0 then setPrecRound (turnFracN y.sign 1 u 2) p mode
  else if hu : u.toNat = 0 then (zero, .eq)
  else if h1 : (y.abs / x.abs).num = (y.abs / x.abs).den then
    setPrecRound (turnFracN y.sign (if x.sign then 1 else 3) u 3) p mode
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    let o := atan2RatPeriodOrient (y.abs / x.abs) x.sign
    let r := zivLoopCertified (atan2RatPeriodApprox o y x (AzNat.ofNat u.toNat)) p
      (if o = !y.sign then mode else -mode) (p + zivGuardBits)
      (atan2RatPeriodApprox_isSome_exists p _ o y x hy hx h1
        (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
        (by unfold zivGuardBits; omega))
    if o = !y.sign then r else (-r.1, r.2.swap)

/-- `atan2 (y, x) u / (2π)` for rationals, rounded to nearest at precision `p`. -/
def atan2RatWithPeriod (y x : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (atan2RatWithPeriodPrecRound y x u p .Nearest).1

end Azurite.AzFloat
