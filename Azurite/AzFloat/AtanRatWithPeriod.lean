/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.Atan2RatWithPeriod

/-!
## The arctangent of a rational with a period: `arctan (q) u / (2π)`

`atanRatWithPeriodPrecRound q u p mode` is `arctan (q) u / (2π)`, the arctangent of an `AzRat`
`q` measured in `u`ths of a turn for a `UInt64` `u`, correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `atanRatWithPeriod q u p` rounds to
nearest.

Special values, as for the float `atanWithPeriodPrecRound`: `q = 0` gives `0`; `u = 0` gives
`0`; `q = ±1` (`num = den`) give `±u/8`, an eighth of a turn, rounded.  Every other value is
irrational and is computed as `atan2 (q, 1) u / (2π)` by `atan2RatWithPeriodPrecRound`
(`AzFloat/Atan2RatWithPeriod.lean`), which keeps the quarter turn exact: a huge `q` gives a
value next to the float `±u/4` at no extra cost (a direct evaluation needs a working precision
of about `lg |q|` bits to separate the two).  The argument is never rounded to the target
precision, and a tiny `q` costs no more than any other.

The specification `atanRatWithPeriodPrecRound_eq` is in `Equiv/AtanRatWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `arctan (q) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0` unless the value is `0` or `±u/8`). -/
def atanRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.num = 0 then (zero, .eq)
  else if u.toNat = 0 then (zero, .eq)
  else if q.num = q.den then setPrecRound (turnFraction q.sign u 3) p mode
  else atan2RatWithPeriodPrecRound q 1 u p mode

/-- `arctan (q) u / (2π)` rounded to nearest at precision `p`. -/
def atanRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (atanRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
