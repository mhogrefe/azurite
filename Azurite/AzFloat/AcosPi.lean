/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosWithPeriod
import Azurite.AzFloat.AcosRatWithPeriod

/-!
## `arccos (x) / π`

`acosPiPrecRound x p mode` is `arccos (x) / π` for a float `x` (the arccosine in half-turns, the
IEEE 754 `acosPi`, in `[0, 1]`), correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `acosPi x` rounds to nearest at the precision of `x`.
`acosPiRatPrecRound q p mode` and `acosPiRat q p` are the same for an `AzRat` `q`.  These are
the period-`2` cases of `acosWithPeriodPrecRound` and `acosRatWithPeriodPrecRound`.

Rational values: `acosPi 1 = 0`, `acosPi 0 = 1/2`, `acosPi (−1) = 1`, and the correctly rounded
`acosPi (1/2) = 1/3`, `acosPi (−1/2) = 2/3`; every other value in `[−1, 1]` is irrational
(Niven's theorem for the cosine).  `NaN` for `NaN`, `±∞` and `|x| > 1`.
-/

namespace Azurite.AzFloat

/-- `arccos (x) / π` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def acosPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  acosWithPeriodPrecRound x 2 p mode

/-- `arccos (x) / π` rounded to nearest at the precision of `x` (at precision `1` for
`x = 0`). -/
def acosPi (x : AzFloat) : AzFloat := (acosPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `arccos (q) / π` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the
comparison with the exact value. -/
def acosPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  acosRatWithPeriodPrecRound q 2 p mode

/-- `arccos (q) / π` rounded to nearest at precision `p`. -/
def acosPiRat (q : AzRat) (p : Nat) : AzFloat := (acosPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
