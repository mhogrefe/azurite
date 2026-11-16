/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanWithPeriod

/-!
## The arccotangent with a period: `arccot (x) u / (2π)`

`acotWithPeriodPrecRound x u p mode` is `arccot (x) u / (2π) = arctan (1/x) u / (2π)`, the
**odd** arccotangent (see `AzFloat/Acot.lean`) of a float `x` measured in `u`ths of a turn
for a `UInt64` `u` (degrees for `u = 360`), in `[−u/4, u/4]`, correctly rounded to precision
`p` in `mode`, with the comparison against the exact value; `acotWithPeriod x u` rounds to
nearest at the precision of `x`.  The function is odd in `x`.

Special values:

* `NaN` gives `NaN`;
* `±∞` give `0` (there is no negative zero);
* `u = 0` gives `0` for every `x` other than `NaN`;
* `x = 0` gives `u/4`, a quarter turn, rounded (the value approached from the right: there is
  one zero only);
* `x = ±1` give `±u/8`, an eighth of a turn, rounded.

These are the only rational values, by Niven's theorem for the tangent.  A finite `x ≠ 0` is
computed as `atan2 (±1, |x|) u / (2π)` by `atan2WithPeriodPrecRound`
(`AzFloat/Atan2WithPeriod.lean`), whose enclosures keep the quarter turn exact — a tiny `x`
gives a value within `|x| u` of the float `±u/4` — and have relative accuracy for a huge `x`,
where the value is `≈ u/(2πx)`.  So neither extreme costs more than any other argument.

The specification `acotWithPeriodPrecRound_eq` is in `Equiv/AcotWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `arccot (x) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0` unless the value is rational). -/
def acotWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (zero, .eq)
  | zero => setPrecRound (turnFraction true u 2) p mode
  | finite s e q m hv =>
    atan2WithPeriodPrecRound (if s then one else -one) (finite s e q m hv).abs u p mode

/-- `arccot (x) u / (2π)` rounded to nearest at the precision of `x` (`0` for `x = ±∞`,
precision `1` for `x = 0`). -/
def acotWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (acotWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
