/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinhRat

/-!
## The inverse hyperbolic cosecant of a rational

For a rational `q ≠ 0` the reciprocal `1/q` is again an exact rational, so the inverse
hyperbolic cosecant is the inverse hyperbolic sine of it: `acschRatPrecRound q p mode` is
`acsch q = asinh (1/q)`, i.e. `asinhRatPrecRound q⁻¹` (whose tiny-argument path covers a huge
`q`), and `+∞` at `q = 0`; `acschRat q p` rounds to nearest.  The function is odd in `q ≠ 0`.
The specification `acschRatPrecRound_eq` is in `Equiv/Acsch.lean`.
-/

namespace Azurite.AzFloat

/-- `acsch q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def acschRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then (infinity true, .eq) else asinhRatPrecRound q⁻¹ p mode

/-- `acsch q` rounded to nearest at precision `p`. -/
def acschRat (q : AzRat) (p : Nat) : AzFloat := (acschRatPrecRound q p .Nearest).1

end Azurite.AzFloat
