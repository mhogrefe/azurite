/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Div

/-!
# Reciprocal

`recipPrecRound y p mode = divPrecRound one y p mode`: the reciprocal is the division of `one`,
correctly rounded with the exact comparison (`Equiv/Recip.lean`).  Special values follow
division: `1/0 = +∞`, `1/(±∞) = 0`, `1/NaN = NaN`.  A dedicated Newton reciprocal
(`AzNat.approxReciprocal` plus one exact correction product) would skip the Barrett multiplication
by the dividend at large precision; not implemented — divisions are a small share of the cost of
the functions built on them.
-/

namespace Azurite.AzFloat

/-- `1 / y` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def recipPrecRound (y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  divPrecRound one y p mode

/-- `1 / y` rounded to nearest at the precision of `y`. -/
def recip (y : AzFloat) : AzFloat := (recipPrecRound y (y.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
