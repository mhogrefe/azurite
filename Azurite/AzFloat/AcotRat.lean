/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanRat
import Azurite.AzFloat.AtanRatWithPeriod
import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.PiConstants

/-!
## The arccotangent of a rational, plain and with a period

For a rational `q ≠ 0` the reciprocal `1/q` is again an exact rational, so the (odd)
arccotangent is the arctangent of it:

* `acotRatPrecRound q p mode` is `arccot q = arctan (1/q)`: `atanRatPrecRound q⁻¹` for
  `q ≠ 0`, and the correctly rounded `π/2` for `q = 0`; `acotRat q p` rounds to nearest.
* `acotRatWithPeriodPrecRound q u p mode` is `arccot (q) u / (2π)`:
  `atanRatWithPeriodPrecRound q⁻¹ u` for `q ≠ 0`, and the quarter turn `u/4`, rounded, for
  `q = 0`; `acotRatWithPeriod q u p` rounds to nearest.

With a period the rational values are `u/4` at `0`, `±u/8` at `±1` and `0` for `u = 0`;
everything else is irrational.  Both are odd in `q ≠ 0`.  The specifications are in
`Equiv/AcotRat.lean`.
-/

namespace Azurite.AzFloat

/-- `arccot q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def acotRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then piDiv2PrecRound p mode else atanRatPrecRound q⁻¹ p mode

/-- `arccot q` rounded to nearest at precision `p`. -/
def acotRat (q : AzRat) (p : Nat) : AzFloat := (acotRatPrecRound q p .Nearest).1

/-- `arccot (q) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0` unless the value is rational). -/
def acotRatWithPeriodPrecRound (q : AzRat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.num = 0 then setPrecRound (turnFraction true u 2) p mode
  else atanRatWithPeriodPrecRound q⁻¹ u p mode

/-- `arccot (q) u / (2π)` rounded to nearest at precision `p`. -/
def acotRatWithPeriod (q : AzRat) (u : UInt64) (p : Nat) : AzFloat :=
  (acotRatWithPeriodPrecRound q u p .Nearest).1

end Azurite.AzFloat
