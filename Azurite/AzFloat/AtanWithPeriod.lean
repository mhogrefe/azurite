/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2WithPeriod

/-!
## The arctangent with a period: `arctan (x) u / (2π)`

`atanWithPeriodPrecRound x u p mode` is `arctan (x) u / (2π)`, the arctangent of a float `x`
measured in `u`ths of a turn for a `UInt64` `u` (degrees for `u = 360`), correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `atanWithPeriod x u`
rounds to nearest at the precision of `x`.

Special values:

* `NaN` gives `NaN`;
* `±∞` give `±u/4`, a quarter turn, rounded;
* `x = 0` gives `0` (there is no negative zero);
* `u = 0` gives `0` for every `x` other than `NaN`;
* `x = ±1` give `±u/8`, an eighth of a turn, rounded.

These are the only rational values: for a finite `x ∉ {0, ±1}` and `u ≠ 0` the value is
irrational by Niven's theorem for the tangent.  It is computed as
`atan2 (x, 1) u / (2π)` by `atan2WithPeriodPrecRound` (`AzFloat/Atan2WithPeriod.lean`), whose
enclosures keep the quarter turn exact: a huge `x` gives a value within `2^(−e)` of the float
`±u/4`, and a direct evaluation of `arctan (x) / (2π)` would need a working precision growing
with the exponent to separate the two (until 2026-11-15 this function did exactly that).  A
tiny `x` costs no more than any other either.

The specification `atanWithPeriodPrecRound_eq` is in `Equiv/AtanWithPeriod.lean`.
-/

namespace Azurite.AzFloat

/-- `± u 2^(−k)` as a float (`pos`: the sign is positive). -/
def turnFraction (pos : Bool) (u : UInt64) (k : Nat) : AzFloat :=
  let f := ofAzNat (AzNat.ofNat u.toNat) <<< AzInt.ofInt (-(k : Int))
  if pos then f else -f

/-- `arctan (x) u / (2π)` rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0` unless the value is `0`, `±u/4` or `±u/8`). -/
def atanWithPeriodPrecRound (x : AzFloat) (u : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => setPrecRound (turnFraction s u 2) p mode
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if u.toNat = 0 then (zero, .eq)
    else if eqIEEE (finite s e q m hv).abs one = true then
      setPrecRound (turnFraction s u 3) p mode
    else atan2WithPeriodPrecRound (finite s e q m hv) one u p mode

/-- `arctan (x) u / (2π)` rounded to nearest at the precision of `x`. -/
def atanWithPeriod (x : AzFloat) (u : UInt64) : AzFloat :=
  (atanWithPeriodPrecRound x u (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
