/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2WithPeriod
import Azurite.AzFloat.Atan2RatWithPeriod

/-!
## `atan2 (y, x) / π`

`atan2PiPrecRound y x p mode` is `atan2 (y, x) / π` for floats (the angle of `(x, y)` in
half-turns, in `(−1, 1]`: the IEEE 754 `atan2Pi`), correctly rounded to precision `p` in `mode`,
with the comparison against the exact value; `atan2Pi y x` rounds to nearest at the larger of the
precisions of the arguments.  `atan2PiRatPrecRound y x p mode` and `atan2PiRat y x p` are the
same for `AzRat` arguments.  These are the period-`2` cases of `atan2WithPeriodPrecRound` and
`atan2RatWithPeriodPrecRound`.

Exact values (there is no negative zero): `0` and `1` on the real axis, `±1/2` on the imaginary
axis, `±1/4`, `±3/4` on the diagonals, and the corresponding values at the infinities
(`±1/4`, `±3/4` for two infinities; `±1/2` for `y = ±∞`; `0`, `±1` for `x = ±∞`); every other
value is irrational.  `NaN` in either argument gives `NaN`.
-/

namespace Azurite.AzFloat

/-- `atan2 (y, x) / π` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def atan2PiPrecRound (y x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  atan2WithPeriodPrecRound y x 2 p mode

/-- `atan2 (y, x) / π` rounded to nearest at the larger of the precisions of `y` and `x`. -/
def atan2Pi (y x : AzFloat) : AzFloat :=
  (atan2PiPrecRound y x (max (y.precision?.getD 1) (x.precision?.getD 1)) .Nearest).1

/-- `atan2 (y, x) / π` for `AzRat` arguments, rounded to precision `p` with `mode`, and the
comparison with the exact value. -/
def atan2PiRatPrecRound (y x : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  atan2RatWithPeriodPrecRound y x 2 p mode

/-- `atan2 (y, x) / π` for `AzRat` arguments, rounded to nearest at precision `p`. -/
def atan2PiRat (y x : AzRat) (p : Nat) : AzFloat := (atan2PiRatPrecRound y x p .Nearest).1

end Azurite.AzFloat
