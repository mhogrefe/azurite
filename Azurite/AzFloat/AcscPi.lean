/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscWithPeriod
import Azurite.AzFloat.AcscRat

/-!
## `arccsc (x) / π`

`acscPiPrecRound x p mode` is `arccsc (x) / π` for a float `x` (the arccosecant in
half-turns, in `[−1/2, 1/2]`), correctly rounded to precision `p` in `mode`, with the comparison against the exact
value; `acscPi x` rounds to nearest at the precision of `x`.  `acscPiRatPrecRound q p mode` and
`acscPiRat q p` are the same for an `AzRat` `q`.  These are the period-`2` cases of
`acscWithPeriodPrecRound` and `acscRatWithPeriodPrecRound`.

Rational values: `acscPi (±1) = ±1/2`, `acscPi (±∞) = 0`, and the correctly rounded
`acscPi (±2) = ±1/6`; every other value is irrational.  `NaN` for `NaN` and for `|x| < 1`.
-/

namespace Azurite.AzFloat

/-- `arccsc (x) / π` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def acscPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  acscWithPeriodPrecRound x 2 p mode

/-- `arccsc (x) / π` rounded to nearest at the precision of `x` (`0` for `x = ±∞`). -/
def acscPi (x : AzFloat) : AzFloat := (acscPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `arccsc (q) / π` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the
comparison with the exact value. -/
def acscPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  acscRatWithPeriodPrecRound q 2 p mode

/-- `arccsc (q) / π` rounded to nearest at precision `p`. -/
def acscPiRat (q : AzRat) (p : Nat) : AzFloat := (acscPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
