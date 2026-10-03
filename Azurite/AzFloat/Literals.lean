/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.HexString
import Azurite.AzRat.FromSci

/-!
# Literals and display

* Integer literals `(n : AzFloat)` are exact, at the precision of their bit length (`0` and `1`
  come from the `Zero` and `One` instances).
* Scientific literals `(2.5 : AzFloat)`, `(1e-3 : AzFloat)` are the exact decimal rounded to
  nearest at `literalPrecision = 53` bits, the precision of a binary64 `Float`; other precisions
  go through `ofDecimalString` or `ofAzRat`.
* `Repr` is the exact hexadecimal debug format (`0x1.8#2`); `ToString` is the shortest
  round-tripping decimal.
-/

namespace Azurite.AzFloat

/-- Integer literals are exact. -/
instance (n : Nat) : OfNat AzFloat (n + 2) := ⟨ofAzNat (AzNat.ofNat (n + 2))⟩

/-- The precision of scientific literals, that of a binary64 `Float`. -/
def literalPrecision : Nat := 53

/-- The value of a scientific literal, `m · 10^e` or `m · 10^(−e)`, as a rational. -/
def scientificValue (m : Nat) (negExp : Bool) (e : Nat) : AzRat :=
  AzRat.ofSciParts 10 true (AzNat.ofNat m) (if negExp then -(e : Int) else e)

instance : OfScientific AzFloat :=
  ⟨fun m negExp e => ofAzRat (scientificValue m negExp e) literalPrecision⟩

instance : Repr AzFloat := ⟨fun x _ => toHexString x⟩

end Azurite.AzFloat
