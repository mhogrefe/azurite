/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Conversion
import Azurite.AzZMod.Equiv.Basic
import Azurite.AzInt.Equiv.Basic

namespace Azurite.AzZMod

/-- **`ofAzInt` agrees with the `ZMod` cast.**  Converting an `AzInt` and then
viewing it in `ZMod m.toNat` is the same as casting its integer value. -/
@[simp] theorem toZMod_ofAzInt (m : AzNat) [NeZero m.toNat] (z : AzInt) :
    toZMod (ofAzInt m z) = (z.toInt : ZMod m.toNat) := by
  unfold ofAzInt AzInt.toInt
  by_cases h : z.sign = true
  · rw [ite_eq_left h, ite_eq_left h, toZMod_ofAzNat]; norm_cast
  · rw [ite_eq_right h, ite_eq_right h, toZMod_neg, toZMod_ofAzNat, Int.cast_neg, Int.cast_natCast]

end Azurite.AzZMod
