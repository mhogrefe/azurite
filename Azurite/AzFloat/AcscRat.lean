/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinRat
import Azurite.AzFloat.AsinRatWithPeriod

/-!
## The arccosecant of a rational, plain and with a period

For a rational `q` the reciprocal `1/q` is again an exact rational, so the arccosecant is the
arcsine of it:

* `acscRatPrecRound q p mode` is `arccsc q = arcsin (1/q)`: `asinRatPrecRound q⁻¹` for
  `|q| ≥ 1` (`den ≤ num`), and `NaN` otherwise (in particular for `q = 0`);
  `acscRat q p` rounds to nearest.
* `acscRatWithPeriodPrecRound q u p mode` is `arccsc (q) u / (2π)`:
  `asinRatWithPeriodPrecRound q⁻¹ u` for `|q| ≥ 1`, and `NaN` otherwise, also for `u = 0`;
  `acscRatWithPeriod q u p` rounds to nearest.

So `arccsc (±1) = ±π/2`; with a period `±u/4` at `±1`, `±u/12` at `±2`, `0` for `u = 0`; and
everything else is irrational.  Both are odd in `q`.  The specifications are in
`Equiv/AcscRat.lean`.
-/

namespace Azurite.AzFloat

/-- `arccsc q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|q| < 1`, and for `p = 0`). -/
def acscRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.den ≤ q.num then asinRatPrecRound q⁻¹ p mode else (nan, .eq)

/-- `arccsc q` rounded to nearest at precision `p`. -/
def acscRat (q : AzRat) (p : Nat) : AzFloat := (acscRatPrecRound q p .Nearest).1

/-- `arccsc (q) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `|q| < 1`, and for `p = 0`). -/
def acscRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.den ≤ q.num then asinRatWithPeriodPrecRound q⁻¹ u p mode else (nan, .eq)

/-- `arccsc (q) u / (2π)` rounded to nearest at precision `p`. -/
def acscRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (acscRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
