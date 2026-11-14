/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosPi
import Azurite.AzFloat.SinPi
import Azurite.AzFloat.SinCosWithPeriod
import Azurite.AzFloat.SinCosRatWithPeriod

/-!
## `sin (π x)` and `cos (π x)` together

`sinCosPiPrecRound x p mode` is the pair of `sin (π x)` and `cos (π x)` for a float `x`, each
correctly rounded to precision `p` in `mode` with the comparison against the exact value:
`sinCosPiPrecRound x p mode = (sinPiPrecRound x p mode, cosPiPrecRound x p mode)`
(`sinCosPiPrecRound_eq`, `Equiv/SinCosPi.lean`), from one computation; `sinCosPi x` rounds both
to nearest at the precision of `x`.  `sinCosPiRatPrecRound q p mode` and `sinCosPiRat q p` are
the same for an `AzRat` `q`.  These are the period-`2` cases of `sinCosWithPeriodPrecRound` and
`sinCosRatWithPeriodPrecRound`: the argument is reduced exactly, and the joint computation runs
whenever both values are irrational.  The remaining cases are delegated to the separate
functions: for a float, the integers and half-integers (both values exact); for a rational,
also the thirds and sixths (one value is `±1/2`).
-/

namespace Azurite.AzFloat

/-- `(sin (π x), cos (π x))`, each rounded to precision `p` with `mode` and paired with the
comparison with the exact value (as `sinPiPrecRound` and `cosPiPrecRound`). -/
def sinCosPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × (AzFloat × Ordering) :=
  sinCosWithPeriodPrecRound x 2 p mode

/-- `(sin (π x), cos (π x))`, both rounded to nearest at the precision of `x`. -/
def sinCosPi (x : AzFloat) : AzFloat × AzFloat :=
  let r := sinCosPiPrecRound x (x.precision?.getD 1) .Nearest
  (r.1.1, r.2.1)

/-- `(sin (π q), cos (π q))` for an `AzRat` `q`, each rounded to precision `p` with `mode` and
paired with the comparison with the exact value (as `sinPiRatPrecRound` and
`cosPiRatPrecRound`). -/
def sinCosPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × (AzFloat × Ordering) :=
  sinCosRatWithPeriodPrecRound q 2 p mode

/-- `(sin (π q), cos (π q))`, both rounded to nearest at precision `p`. -/
def sinCosPiRat (q : AzRat) (p : Nat) : AzFloat × AzFloat :=
  let r := sinCosPiRatPrecRound q p .Nearest
  (r.1.1, r.2.1)

end Azurite.AzFloat
