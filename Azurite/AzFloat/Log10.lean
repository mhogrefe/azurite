/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBase
import Azurite.AzFloat.LogBaseP1
import Azurite.AzFloat.LogBaseRat

/-!
## Base-10 logarithms

Wrappers around the natural-base functions with the base `10`: `log10PrecRound`/`log10` for a
float, `log10RatPrecRound`/`log10Rat` for a rational (returning a float), and
`log10P1PrecRound`/`log10P1` for `log₁₀ (1 + x)`.  The specifications in `Equiv/Log10.lean` are
the base-`10` instances of the general ones.
-/

namespace Azurite.AzFloat

/-- `log₁₀ x` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def log10PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  logBasePrecRound x 10 p mode

/-- `log₁₀ x` rounded to nearest at the precision of `x`. -/
def log10 (x : AzFloat) : AzFloat := logBase x 10

/-- `log₁₀ q` for a rational `q`, rounded to precision `p` with `mode`, and the comparison with
the exact value. -/
def log10RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  logBaseRatPrecRound q 10 p mode

/-- `log₁₀ q` for a rational `q`, rounded to nearest at precision `p`. -/
def log10Rat (q : AzRat) (p : Nat) : AzFloat := logBaseRat q 10 p

/-- `log₁₀ (1 + x)` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def log10P1PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  logBaseP1PrecRound x 10 p mode

/-- `log₁₀ (1 + x)` rounded to nearest at the precision of `x`. -/
def log10P1 (x : AzFloat) : AzFloat := logBaseP1 x 10

end Azurite.AzFloat
