/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzRat.FromSci

/-!
# Decimal input of an `AzFloat`

`ofDecimalStringRound s p mode` reads a decimal in the language of `AzRat.fromSci` (an optional
sign, digits with an optional point, an optional `e`/`E` exponent fitting in a signed 64-bit
integer) and rounds the exact rational it denotes to precision `p` with `mode`, returning the
float and the comparison with the exact value; the special spellings `NaN`, `Infinity` and
`-Infinity` of `toDecimalString` are accepted as well.  Anything else is `none`.

Since a decimal string is an exact rational, correct rounding is `ofAzRatRound`'s, and
`Equiv/OfString.lean` proves that reading back `toDecimalString x` at the precision of `x`
gives `x`.
-/

namespace Azurite.AzFloat

/-- Read a decimal, rounding to precision `p` with `mode`; `NaN`, `Infinity`, `-Infinity`
are the special values. -/
def ofDecimalStringRound (s : String) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if s = "NaN" then some (nan, .eq)
  else if s = "Infinity" then some (infinity true, .eq)
  else if s = "-Infinity" then some (infinity false, .eq)
  else (AzRat.fromSci s).map fun q => ofAzRatRound q p mode

/-- Read a decimal, rounding to nearest at precision `p`. -/
def ofDecimalString (s : String) (p : Nat) : Option AzFloat :=
  (ofDecimalStringRound s p .Nearest).map (·.1)

end Azurite.AzFloat
