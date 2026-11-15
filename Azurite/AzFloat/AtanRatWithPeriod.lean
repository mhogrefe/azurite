/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.Equiv.AtanRatWithPeriodBracket

/-!
## The arctangent of a rational with a period: `arctan (q) u / (2π)`

`atanRatWithPeriodPrecRound q u p mode` is `arctan (q) u / (2π)`, the arctangent of an `AzRat`
`q` measured in `u`ths of a turn for a `UInt64` `u`, correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `atanRatWithPeriod q u p` rounds to
nearest.

Special values, as for the float `atanWithPeriodPrecRound`: `q = 0` gives `0`; `u = 0` gives
`0`; `q = ±1` (`num = den`) give `±u/8`, an eighth of a turn, rounded.  Every other value is
irrational (`irrational_atanPeriod_toRat`, Niven's theorem for the tangent), which certifies
the Ziv loop (`zivLoopCertified`, no fuel) on `atanRatPeriodApprox`
(`AzFloat/AtanRatWithPeriodBracket.lean`).  The argument is never rounded to the target
precision, and a tiny `q` costs no more than any other.

The specification `atanRatWithPeriodPrecRound_eq` is in `Equiv/AtanRatWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `arctan (q) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0` unless the value is `0` or `±u/8`). -/
def atanRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hu : u.toNat = 0 then (zero, .eq)
  else if h1 : q.num = q.den then setPrecRound (turnFraction q.sign u 3) p mode
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified (atanRatPeriodApprox q (AzNat.ofNat u.toNat)) p mode (p + zivGuardBits)
      (atanRatPeriodApprox_isSome_exists p mode q h0 h1
        (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
        (by unfold zivGuardBits; omega))

/-- `arctan (q) u / (2π)` rounded to nearest at precision `p`. -/
def atanRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (atanRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
