/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanhRat

/-!
## The inverse hyperbolic cotangent of a rational

For a rational `q ≠ 0` the reciprocal `1/q` is again an exact rational, so the inverse
hyperbolic cotangent is the inverse hyperbolic tangent of it: `acothRatPrecRound q p mode` is
`acoth q = atanh (1/q)`, i.e. `atanhRatPrecRound q⁻¹` — `±∞` at `q = ±1`, `NaN` for `|q| < 1`,
its tiny-argument path covering a huge `q` — and `NaN` at `q = 0`; `acothRat q p` rounds to
nearest.  The function is odd in `q`.  The specification `acothRatPrecRound_eq` is in
`Equiv/Acoth.lean`.
-/

namespace Azurite.AzFloat

/-- `acoth q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|q| < 1`, and for `p = 0` and `|q| > 1`). -/
def acothRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then (nan, .eq) else atanhRatPrecRound q⁻¹ p mode

/-- `acoth q` rounded to nearest at precision `p`. -/
def acothRat (q : AzRat) (p : Nat) : AzFloat := (acothRatPrecRound q p .Nearest).1

end Azurite.AzFloat
