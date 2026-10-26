/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBase
import Azurite.AzFloat.PowBaseM1
import Azurite.AzFloat.PowBaseM1Rat
import Azurite.AzFloat.PowBaseRat

/-!
## `10^x`, `10^q`, `10^x − 1` and `10^q − 1`

The base-`10` special cases of `powBase`, `powBaseRat`, `powBaseM1` and `powBaseM1Rat`
(`u = 10`): `pow10PrecRound x p mode`/`pow10 x`, `pow10RatPrecRound q p mode`/`pow10Rat q p`,
`pow10M1PrecRound x p mode`/`pow10M1 x`, `pow10M1RatPrecRound q p mode`/`pow10M1Rat q p`, all
correctly rounded with the comparison against the exact value (`Equiv/Pow10.lean`).  The
primitive root of `10` is `10` itself, so `10^x` is rational exactly for the integers `x`.
-/

namespace Azurite.AzFloat

/-- `10^x` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def pow10PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  powBasePrecRound 10 x p mode

/-- `10^x` rounded to nearest at the precision of `x`. -/
def pow10 (x : AzFloat) : AzFloat := powBase 10 x

/-- `10^q` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def pow10RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  powBaseRatPrecRound 10 q p mode

/-- `10^q` rounded to nearest at precision `p`. -/
def pow10Rat (q : AzRat) (p : Nat) : AzFloat := powBaseRat 10 q p

/-- `10^x − 1` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def pow10M1PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  powBaseM1PrecRound 10 x p mode

/-- `10^x − 1` rounded to nearest at the precision of `x`. -/
def pow10M1 (x : AzFloat) : AzFloat := powBaseM1 10 x

/-- `10^q − 1` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def pow10M1RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  powBaseM1RatPrecRound 10 q p mode

/-- `10^q − 1` rounded to nearest at precision `p`. -/
def pow10M1Rat (q : AzRat) (p : Nat) : AzFloat := powBaseM1Rat 10 q p

end Azurite.AzFloat
