/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcoshRat

/-!
## The inverse hyperbolic secant of a rational

For a rational `q ≠ 0` the reciprocal `1/q` is again an exact rational, so the inverse
hyperbolic secant is the inverse hyperbolic cosine of it: `asechRatPrecRound q p mode` is
`asech q = acosh (1/q)`, i.e. `acoshRatPrecRound q⁻¹` — `NaN` for `q < 0` and for `q > 1`, `0`
at `q = 1` — and `+∞` at `q = 0`; `asechRat q p` rounds to nearest.  The specification
`asechRatPrecRound_eq` is in `Equiv/Asech.lean`.
-/

namespace Azurite.AzFloat

/-- `asech q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `q < 0` and `q > 1`, and for `p = 0` and `0 < q < 1`). -/
def asechRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then (infinity true, .eq) else acoshRatPrecRound q⁻¹ p mode

/-- `asech q` rounded to nearest at precision `p`. -/
def asechRat (q : AzRat) (p : Nat) : AzFloat := (asechRatPrecRound q p .Nearest).1

end Azurite.AzFloat
