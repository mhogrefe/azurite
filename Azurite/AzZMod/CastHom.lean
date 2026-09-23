/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Instances
import Azurite.AzNat.Instances
import Azurite.AzInt.Instances
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Mul

/-!
## Reduction ring homomorphisms into `AzZMod m`

`ofAzNat`/`ofAzInt` packaged as `AzNat →+* AzZMod m` / `AzInt →+* AzZMod m`, so
they can drive `AzPolynomial.map` / `AzMvPolynomial.map` for the
coefficient-reducing casts.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- Reduction `AzNat →+* AzZMod m` (the limb-level `ofAzNat`). -/
def ofAzNatRingHom [NeZero m.toNat] : AzNat →+* AzZMod m where
  toFun := ofAzNat m
  map_one' := toZMod_injective (by simp [toZMod_ofAzNat])
  map_mul' a b := toZMod_injective (by simp [toZMod_ofAzNat, AzNat.toNat_mul])
  map_zero' := toZMod_injective (by simp [toZMod_ofAzNat])
  map_add' a b := toZMod_injective (by simp [toZMod_ofAzNat, AzNat.toNat_add])

/-- Reduction `AzInt →+* AzZMod m` (the limb-level `ofAzInt`). -/
def ofAzIntRingHom [NeZero m.toNat] : AzInt →+* AzZMod m where
  toFun := ofAzInt m
  map_one' := toZMod_injective (by simp [toZMod_ofAzInt])
  map_mul' a b := toZMod_injective (by simp [toZMod_ofAzInt, AzInt.toInt_mul])
  map_zero' := toZMod_injective (by simp [toZMod_ofAzInt])
  map_add' a b := toZMod_injective (by simp [toZMod_ofAzInt, AzInt.toInt_add])

end Azurite.AzZMod
