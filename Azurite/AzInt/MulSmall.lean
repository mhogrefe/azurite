/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzNat.Mul.Schoolbook

/-!
# `AzInt` times a small factor

`mulUInt64` and `mulInt64` depend only on `AzNat.mulUInt64`, not on the full `AzNat`
multiplication dispatcher, so they live apart from `AzInt.mul`: the Toom–Cook evaluation
framework uses them and is itself part of the dispatcher.
-/

namespace Azurite.AzInt

/-- Multiply an `AzInt` `z` by a `UInt64` `u`. -/
def mulUInt64 (z : AzInt) (u : UInt64) : AzInt :=
  mkNorm z.sign (z.abs.mulUInt64 u)

/-- Multiply an `AzInt` `z` by an `Int64` `i`. -/
def mulInt64 (z : AzInt) (i : Int64) : AzInt :=
  if i ≥ 0 then mkNorm z.sign (z.abs.mulUInt64 i.toUInt64)
  else mkNorm (!z.sign) (z.abs.mulUInt64 (-i).toUInt64)

end Azurite.AzInt
