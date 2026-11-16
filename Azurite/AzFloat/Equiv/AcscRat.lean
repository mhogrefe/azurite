/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscRat
import Azurite.AzFloat.Equiv.AsinRat
import Azurite.AzFloat.Equiv.AsinRatWithPeriod
import Azurite.AzFloat.Equiv.AcscWithPeriod
import Azurite.AzFloat.Equiv.AsecRat

/-!
# Equivalence: `arccsc q` for a rational `q`, plain and with a period

`acscRatPrecRound_eq : acscRatPrecRound q p mode = roundVal p mode (Spec.acsc q)` and
`acscRatWithPeriodPrecRound_eq :
  acscRatWithPeriodPrecRound q u p mode = roundVal p mode (Spec.acscWithPeriod q u)`, for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

/-- **`arccsc q` is correctly rounded.** -/
theorem acscRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acscRatPrecRound q p mode
      = roundVal p mode (Spec.acsc (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold acscRatPrecRound
  by_cases h : q.den ≤ q.num
  · have h1 := (one_le_abs_toRat_iff q).mp h
    have hinv : |((AzRat.toRat q : ℚ) : ℝ)⁻¹| ≤ 1 := by
      rw [abs_inv]
      exact inv_le_one_of_one_le₀ h1
    rw [ite_eq_left h, asinRatPrecRound_eq, coe_toRat_inv, Spec.asin_coe hinv,
      Spec.acsc_coe h1]
  · have h1 : |((AzRat.toRat q : ℚ) : ℝ)| < 1 :=
      not_le.mp fun h' => h ((one_le_abs_toRat_iff q).mpr h')
    rw [ite_eq_right h, Spec.acsc_coe_of_lt_one h1, roundVal_none]

/-- **`arccsc (q) u / (2π)` of a rational is correctly rounded.** -/
theorem acscRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    acscRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.acscWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  unfold acscRatWithPeriodPrecRound
  by_cases h : q.den ≤ q.num
  · have h1 := (one_le_abs_toRat_iff q).mp h
    have hinv : |((AzRat.toRat q : ℚ) : ℝ)⁻¹| ≤ 1 := by
      rw [abs_inv]
      exact inv_le_one_of_one_le₀ h1
    rw [ite_eq_left h, asinRatWithPeriodPrecRound_eq, coe_toRat_inv,
      Spec.asinWithPeriod_coe hinv, Spec.acscWithPeriod_coe h1]
  · have h1 : |((AzRat.toRat q : ℚ) : ℝ)| < 1 :=
      not_le.mp fun h' => h ((one_le_abs_toRat_iff q).mpr h')
    rw [ite_eq_right h, Spec.acscWithPeriod_coe_of_lt_one h1, roundVal_none]

end Azurite.AzFloat
