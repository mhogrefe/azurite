/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.MulNat
import Azurite.AzNat.Equiv.Mul.Dispatch

/-!
# Equivalence: multiplication by a machine-sized natural
-/

namespace Azurite.AzNat

theorem toNat_mulNat (x : AzNat) (a : ℕ) : (x.mulNat a).toNat = x.toNat * a := by
  unfold mulNat
  split_ifs with h
  · rw [toNat_mulUInt64]
    congr 1
    exact UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
  · rw [toNat_mul, toNat_ofNat]

end Azurite.AzNat
