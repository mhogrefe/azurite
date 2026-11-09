/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosPeriod
import Azurite.AzFloat.CosRatPeriod

/-!
## `cos (π x)`

`cosPiPrecRound x p mode` is `cos (π x)` for a float `x`, correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `cosPi x` rounds to nearest at the precision
of `x`.  `cosPiRatPrecRound q p mode` and `cosPiRat q p` are the same for an `AzRat` `q`.  These
are the period-`2` cases of `cosWithPeriodPrecRound` and `cosRatWithPeriodPrecRound`
(`cos (π x) = cos (2π x / 2)`), so the argument is reduced exactly and no error of `π` is
amplified by a large `x`.  Exact values: `±1` at the integers, `0` at the half-integers, and for
rational arguments `±1/2` at the thirds; every other value is irrational (Niven).

Special values: `cosPi NaN = cosPi (±∞) = NaN`, `cosPi 0 = 1`; `(nan, .eq)` for `p = 0`.
-/

namespace Azurite.AzFloat

/-- `cos (π x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def cosPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  cosWithPeriodPrecRound x 2 p mode

/-- `cos (π x)` rounded to nearest at the precision of `x`. -/
def cosPi (x : AzFloat) : AzFloat := (cosPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `cos (π q)` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value (`(nan, .eq)` for `p = 0`). -/
def cosPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  cosRatWithPeriodPrecRound q 2 p mode

/-- `cos (π q)` rounded to nearest at precision `p`. -/
def cosPiRat (q : AzRat) (p : Nat) : AzFloat := (cosPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
