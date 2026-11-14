/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanWithPeriod
import Azurite.AzFloat.TanRatWithPeriod

/-!
## `tan (π x)`

`tanPiPrecRound x p mode` is `tan (π x)` for a float `x`, correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `tanPi x` rounds to nearest at the precision
of `x`.  `tanPiRatPrecRound q p mode` and `tanPiRat q p` are the same for an `AzRat` `q`.  These
are the period-`2` cases of `tanWithPeriodPrecRound` and `tanRatWithPeriodPrecRound`
(`tan (π x) = tan (2π x / 2)`), so the argument is reduced exactly and no error of `π` is
amplified by a large `x`.

Exact values, as in IEEE 754 `tanPi` (without signed zeros): `0` at the integers; at the
half-integers `n + 1/2` the **poles**, `+∞` for an even integer `n` and `−∞` for an odd one
(`Spec.tanPole_pi_mul_int_add_half`); `±1` at the odd quarters; every other value is irrational
(Niven's theorem for the tangent).

Special values: `tanPi NaN = tanPi (±∞) = NaN`, `tanPi 0 = 0` (at every precision); `(nan, .eq)`
for `p = 0` otherwise.
-/

namespace Azurite.AzFloat

/-- `tan (π x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `x = 0`); a signed infinity at the half-integers. -/
def tanPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  tanWithPeriodPrecRound x 2 p mode

/-- `tan (π x)` rounded to nearest at the precision of `x`. -/
def tanPi (x : AzFloat) : AzFloat := (tanPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `tan (π q)` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value (`(nan, .eq)` for `p = 0` unless `q = 0`); a signed infinity at the
half-integers. -/
def tanPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  tanRatWithPeriodPrecRound q 2 p mode

/-- `tan (π q)` rounded to nearest at precision `p`. -/
def tanPiRat (q : AzRat) (p : Nat) : AzFloat := (tanPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
