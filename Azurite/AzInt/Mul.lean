/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzNat.Mul

namespace Azurite.AzInt

/-- Multiply an `AzInt` `z` by a `UInt64` `u`. -/
def mulUInt64 (z : AzInt) (u : UInt64) : AzInt :=
  mkNorm z.sign (z.abs.mulUInt64 u)

/-- Multiply an `AzInt` `z` by an `Int64` `i`. -/
def mulInt64 (z : AzInt) (i : Int64) : AzInt :=
  if i ≥ 0 then mkNorm z.sign (z.abs.mulUInt64 i.toUInt64)
  else mkNorm (!z.sign) (z.abs.mulUInt64 (-i).toUInt64)

/-- Multiply two `AzInt`s. -/
def mul (a b : AzInt) : AzInt :=
  mkNorm (a.sign == b.sign) (a.abs * b.abs)

instance : Mul AzInt := ⟨mul⟩

end Azurite.AzInt
