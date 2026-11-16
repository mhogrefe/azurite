/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotWithPeriod
import Azurite.AzFloat.AcotRat

/-!
## `arccot (x) / π`

`acotPiPrecRound x p mode` is `arccot (x) / π` for a float `x` (the odd arccotangent in
half-turns, in `[−1/2, 1/2]`), correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `acotPi x` rounds to nearest at the precision of `x`.
`acotPiRatPrecRound q p mode` and `acotPiRat q p` are the same for an `AzRat` `q`.  These are
the period-`2` cases of `acotWithPeriodPrecRound` and `acotRatWithPeriodPrecRound`.

Rational values: `acotPi 0 = 1/2`, `acotPi (±1) = ±1/4`, `acotPi (±∞) = 0`; every other value
is irrational.  `NaN` for `NaN`.
-/

namespace Azurite.AzFloat

/-- `arccot (x) / π` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def acotPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  acotWithPeriodPrecRound x 2 p mode

/-- `arccot (x) / π` rounded to nearest at the precision of `x` (`0` for `x = ±∞`). -/
def acotPi (x : AzFloat) : AzFloat := (acotPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `arccot (q) / π` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the
comparison with the exact value. -/
def acotPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  acotRatWithPeriodPrecRound q 2 p mode

/-- `arccot (q) / π` rounded to nearest at precision `p`. -/
def acotPiRat (q : AzRat) (p : Nat) : AzFloat := (acotPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
