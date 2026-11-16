/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosRat
import Azurite.AzFloat.AcosRatWithPeriod

/-!
## The arcsecant of a rational, plain and with a period

For a rational `q` the reciprocal `1/q` is again an exact rational, so the arcsecant is the
arccosine of it:

* `asecRatPrecRound q p mode` is `arcsec q = arccos (1/q)`: `acosRatPrecRound q⁻¹` for
  `|q| ≥ 1` (`den ≤ num`), and `NaN` otherwise (in particular for `q = 0`);
  `asecRat q p` rounds to nearest.
* `asecRatWithPeriodPrecRound q u p mode` is `arcsec (q) u / (2π)`:
  `acosRatWithPeriodPrecRound q⁻¹ u` for `|q| ≥ 1`, and `NaN` otherwise, also for `u = 0`;
  `asecRatWithPeriod q u p` rounds to nearest.

So `arcsec 1 = 0`, `arcsec (−1) = π`; with a period `0` at `1`, `u/2` at `−1`, `u/6` at `2`,
`u/3` at `−2`, `0` for `u = 0`; and everything else is irrational.  The specifications are in
`Equiv/AsecRat.lean`.
-/

namespace Azurite.AzFloat

/-- `arcsec q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|q| < 1`, and for `p = 0` unless `q = 1`). -/
def asecRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.den ≤ q.num then acosRatPrecRound q⁻¹ p mode else (nan, .eq)

/-- `arcsec q` rounded to nearest at precision `p`. -/
def asecRat (q : AzRat) (p : Nat) : AzFloat := (asecRatPrecRound q p .Nearest).1

/-- `arcsec (q) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `|q| < 1`, and for `p = 0`). -/
def asecRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.den ≤ q.num then acosRatWithPeriodPrecRound q⁻¹ u p mode else (nan, .eq)

/-- `arcsec (q) u / (2π)` rounded to nearest at precision `p`. -/
def asecRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (asecRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
