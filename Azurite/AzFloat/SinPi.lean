/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinWithPeriod
import Azurite.AzFloat.SinRatWithPeriod

/-!
## `sin (π x)`

`sinPiPrecRound x p mode` is `sin (π x)` for a float `x`, correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `sinPi x` rounds to nearest at the precision
of `x`.  `sinPiRatPrecRound q p mode` and `sinPiRat q p` are the same for an `AzRat` `q`.  These
are the period-`2` cases of `sinWithPeriodPrecRound` and `sinRatWithPeriodPrecRound`
(`sin (π x) = sin (2π x / 2)`), so the argument is reduced exactly and no error of `π` is
amplified by a large `x`.  Exact values: `0` at the integers, `±1` at the half-integers, and for
rational arguments `±1/2` at the odd sixths; every other value is irrational (Niven).

Special values: `sinPi NaN = sinPi (±∞) = NaN`, `sinPi 0 = 0` (at every precision); `(nan, .eq)`
for `p = 0` otherwise.
-/

namespace Azurite.AzFloat

/-- `sin (π x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `x = 0`). -/
def sinPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  sinWithPeriodPrecRound x 2 p mode

/-- `sin (π x)` rounded to nearest at the precision of `x`. -/
def sinPi (x : AzFloat) : AzFloat := (sinPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `sin (π q)` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value (`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def sinPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  sinRatWithPeriodPrecRound q 2 p mode

/-- `sin (π q)` rounded to nearest at precision `p`. -/
def sinPiRat (q : AzRat) (p : Nat) : AzFloat := (sinPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
