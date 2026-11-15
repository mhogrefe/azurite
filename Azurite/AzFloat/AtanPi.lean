/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.AtanRatWithPeriod

/-!
## `arctan (x) / π`

`atanPiPrecRound x p mode` is `arctan (x) / π` for a float `x` (the arctangent in half-turns, the
IEEE 754 `atanPi`), correctly rounded to precision `p` in `mode`, with the comparison against the
exact value; `atanPi x` rounds to nearest at the precision of `x`.  `atanPiRatPrecRound q p mode`
and `atanPiRat q p` are the same for an `AzRat` `q`.  These are the period-`2` cases of
`atanWithPeriodPrecRound` and `atanRatWithPeriodPrecRound`
(`arctan (x) / π = arctan (x) · 2 / (2π)`).

Exact values: `atanPi 0 = 0`, `atanPi (±1) = ±1/4`, `atanPi (±∞) = ±1/2`; every other value is
irrational (Niven's theorem for the tangent).  `atanPi NaN = NaN`; `(nan, .eq)` for `p = 0`
unless the value is one of the exact ones.  There is no negative zero.
-/

namespace Azurite.AzFloat

/-- `arctan (x) / π` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def atanPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  atanWithPeriodPrecRound x 2 p mode

/-- `arctan (x) / π` rounded to nearest at the precision of `x`. -/
def atanPi (x : AzFloat) : AzFloat := (atanPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `arctan (q) / π` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the
comparison with the exact value. -/
def atanPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  atanRatWithPeriodPrecRound q 2 p mode

/-- `arctan (q) / π` rounded to nearest at precision `p`. -/
def atanPiRat (q : AzRat) (p : Nat) : AzFloat := (atanPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
