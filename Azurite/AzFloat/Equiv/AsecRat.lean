/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecRat
import Azurite.AzFloat.Equiv.AcosRat
import Azurite.AzFloat.Equiv.AcosRatWithPeriod
import Azurite.AzFloat.Equiv.AsecWithPeriod

/-!
# Equivalence: `arcsec q` for a rational `q`, plain and with a period

`one_le_abs_toRat_iff` (`1 ≤ |q|` iff `den ≤ num`),
`asecRatPrecRound_eq : asecRatPrecRound q p mode = roundVal p mode (Spec.asec q)` and
`asecRatWithPeriodPrecRound_eq :
  asecRatWithPeriodPrecRound q u p mode = roundVal p mode (Spec.asecWithPeriod q u)`, for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

/-- `1 ≤ |q|` iff `den ≤ num`. -/
theorem one_le_abs_toRat_iff (q : AzRat) : q.den ≤ q.num ↔ 1 ≤ |(AzRat.toRat q : ℝ)| := by
  have hden := den_pos_real q
  rw [abs_coe_toRat, le_div_iff₀ hden, one_mul, Nat.cast_le]
  change AzNat.compare q.den q.num ≠ Ordering.gt ↔ _
  rw [AzNat.compare_eq_compare_toNat]
  constructor
  · intro h
    exact not_lt.mp fun hlt => h (compare_gt_iff_gt.mpr hlt)
  · intro h hgt
    exact absurd (compare_gt_iff_gt.mp hgt) (not_lt.mpr h)

/-- The value of the rational reciprocal. -/
theorem coe_toRat_inv (q : AzRat) :
    ((AzRat.toRat q⁻¹ : ℚ) : ℝ) = ((AzRat.toRat q : ℚ) : ℝ)⁻¹ := by
  rw [AzRat.toRat_inv, Rat.cast_inv]

/-- **`arcsec q` is correctly rounded.** -/
theorem asecRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asecRatPrecRound q p mode
      = roundVal p mode (Spec.asec (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold asecRatPrecRound
  by_cases h : q.den ≤ q.num
  · have h1 := (one_le_abs_toRat_iff q).mp h
    have hinv : |((AzRat.toRat q : ℚ) : ℝ)⁻¹| ≤ 1 := by
      rw [abs_inv]
      exact inv_le_one_of_one_le₀ h1
    rw [ite_eq_left h, acosRatPrecRound_eq, coe_toRat_inv, Spec.acos_coe hinv,
      Spec.asec_coe h1]
  · have h1 : |((AzRat.toRat q : ℚ) : ℝ)| < 1 :=
      not_le.mp fun h' => h ((one_le_abs_toRat_iff q).mpr h')
    rw [ite_eq_right h, Spec.asec_coe_of_lt_one h1, roundVal_none]

/-- **`arcsec (q) u / (2π)` of a rational is correctly rounded.** -/
theorem asecRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    asecRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.asecWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  unfold asecRatWithPeriodPrecRound
  by_cases h : q.den ≤ q.num
  · have h1 := (one_le_abs_toRat_iff q).mp h
    have hinv : |((AzRat.toRat q : ℚ) : ℝ)⁻¹| ≤ 1 := by
      rw [abs_inv]
      exact inv_le_one_of_one_le₀ h1
    rw [ite_eq_left h, acosRatWithPeriodPrecRound_eq, coe_toRat_inv,
      Spec.acosWithPeriod_coe hinv, Spec.asecWithPeriod_coe h1]
  · have h1 : |((AzRat.toRat q : ℚ) : ℝ)| < 1 :=
      not_le.mp fun h' => h ((one_le_abs_toRat_iff q).mpr h')
    rw [ite_eq_right h, Spec.asecWithPeriod_coe_of_lt_one h1, roundVal_none]

end Azurite.AzFloat
