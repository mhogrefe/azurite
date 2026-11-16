/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinWithPeriod
import Azurite.AzFloat.AsinRatWithPeriod

/-!
## `arcsin (x) / π`

`asinPiPrecRound x p mode` is `arcsin (x) / π` for a float `x` (the arcsine in half-turns, the
IEEE 754 `asinPi`), correctly rounded to precision `p` in `mode`, with the comparison against the
exact value; `asinPi x` rounds to nearest at the precision of `x`.  `asinPiRatPrecRound q p mode`
and `asinPiRat q p` are the same for an `AzRat` `q`.  These are the period-`2` cases of
`asinWithPeriodPrecRound` and `asinRatWithPeriodPrecRound`.

Exact and rational values: `asinPi 0 = 0`, `asinPi (±1) = ±1/2`, `asinPi (±1/2) = ±1/6` (the
correctly rounded rational); every other value in `[−1, 1]` is irrational (Niven's theorem for
the sine).  `NaN` for `NaN`, `±∞` and `|x| > 1`.  There is no negative zero.
-/

namespace Azurite.AzFloat

/-- `arcsin (x) / π` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def asinPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  asinWithPeriodPrecRound x 2 p mode

/-- `arcsin (x) / π` rounded to nearest at the precision of `x`. -/
def asinPi (x : AzFloat) : AzFloat := (asinPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `arcsin (q) / π` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the
comparison with the exact value. -/
def asinPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  asinRatWithPeriodPrecRound q 2 p mode

/-- `arcsin (q) / π` rounded to nearest at precision `p`. -/
def asinPiRat (q : AzRat) (p : Nat) : AzFloat := (asinPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
