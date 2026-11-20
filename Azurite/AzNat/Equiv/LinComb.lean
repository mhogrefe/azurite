/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.LinComb
import Azurite.AzNat.Equiv.Gcd.HalfBinary
import Azurite.AzNat.Equiv.MulNat
import Azurite.AzNat.Equiv.Add

/-!
## `linComb` is the linear combination

`(linComb x y s t).toNat = x.toNat · s + y.toNat · t`, from `linCombLimbs_add`.
-/

namespace Azurite.AzNat

theorem toNat_linComb (x y : AzNat) (s t : ℕ) :
    (linComb x y s t).toNat = x.toNat * s + y.toNat * t := by
  unfold linComb
  have hf : (x.mulNat s + y.mulNat t).toNat = x.toNat * s + y.toNat * t := by
    rw [toNat_add, toNat_mulNat, toNat_mulNat]
  by_cases h : s ≤ 9223372036854775807 ∧ t ≤ 9223372036854775807
  · rw [ite_eq_left h]
    dsimp only
    by_cases hc : (linCombLimbs x.limbs y.limbs s.toUInt64 t.toUInt64 false).2 = true
    · rw [ite_eq_left hc]
      exact hf
    · have := linCombLimbs_add x y s.toUInt64 t.toUInt64
      rw [ite_eq_right hc, add_zero, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega),
        UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)] at this
      rw [ite_eq_right hc, toNat_ofLimbs]
      exact this
  · rw [ite_eq_right h]
    exact hf

end Azurite.AzNat
