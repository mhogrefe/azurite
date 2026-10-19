/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.BrentSalamin

/-!
# The lemniscate constant

`ϖ = 2 ∫₀¹ dt/√(1 − t⁴) = 2.62205755429211981046…`, half the arc length of Bernoulli's
lemniscate.  The substitution `t = cos φ` turns the (improper) integral into
`∫₀^{π/2} dφ/√(1 + cos²φ) = K(1/√2)/√2`, so `ϖ = √2 K(1/√2)`
(`lemniscate_eq_sqrt_two_mul_ellipticK`), and Gauss's AGM evaluation of `K` gives
`ϖ = π/AGM(1, √2) = π · G` with `G` Gauss's constant (`lemniscate_eq_pi_div_AGM`).
-/

namespace Azurite.BZ

open Real MeasureTheory intervalIntegral Set

/-- The integrand `1/√(1 − t⁴)` (zero at `t = 1`, where `√0⁻¹ = 0`). -/
noncomputable def lemnIntegrand (t : ℝ) : ℝ := (Real.sqrt (1 - t ^ 4))⁻¹

/-- **The lemniscate constant** `ϖ = 2 ∫₀¹ dt/√(1 − t⁴)`. -/
noncomputable def lemniscate : ℝ := 2 * ∫ t in (0 : ℝ)..1, lemnIntegrand t

/-! ### Integrability: `1/√(1 − t⁴) ≤ (1 − t)^(−1/2)` on `[0, 1]` -/

theorem lemnIntegrand_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |lemnIntegrand t| ≤ (1 - t) ^ (-(1 / (2 : ℝ))) := by
  rcases eq_or_lt_of_le ht1 with rfl | hlt
  · simp [lemnIntegrand]
  · have h1 : 0 < 1 - t := by linarith
    have ht3 : t ^ 4 ≤ t := by
      have : t ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
      calc t ^ 4 = t * t ^ 3 := by ring
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left this ht0
        _ = t := mul_one t
    have h4 : 1 - t ≤ 1 - t ^ 4 := by linarith
    have hpos : 0 < Real.sqrt (1 - t ^ 4) := Real.sqrt_pos.mpr (by linarith)
    rw [lemnIntegrand, abs_of_nonneg (inv_nonneg.mpr hpos.le), Real.rpow_neg h1.le,
      ← Real.sqrt_eq_rpow]
    exact inv_anti₀ (Real.sqrt_pos.mpr h1) (Real.sqrt_le_sqrt h4)

theorem measurable_lemnIntegrand : Measurable lemnIntegrand := by
  unfold lemnIntegrand
  fun_prop

theorem intervalIntegrable_lemnIntegrand : IntervalIntegrable lemnIntegrand volume 0 1 := by
  have hg : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(1 / (2 : ℝ)))) volume 0 1 := by
    have h := (intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : (-1 : ℝ) < -(1 / (2 : ℝ)))).comp_sub_left 1
    simp only [sub_zero, sub_self] at h
    exact h.symm
  refine hg.mono_fun' measurable_lemnIntegrand.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le zero_le_one] at ht
  beta_reduce
  rw [Real.norm_eq_abs]
  exact lemnIntegrand_le ht.1.le ht.2

/-! ### The substitution `t = cos φ` -/

theorem sqrt_one_sub_cos_pow_four (x : ℝ) :
    Real.sqrt (1 - Real.cos x ^ 4) = |Real.sin x| * Real.sqrt (1 + Real.cos x ^ 2) := by
  have h : 1 - Real.cos x ^ 4 = Real.sin x ^ 2 * (1 + Real.cos x ^ 2) := by
    rw [Real.sin_sq]; ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem lemnIntegrand_cos_mul_sin_of_pos {x : ℝ} (hs : 0 < Real.sin x) :
    lemnIntegrand (Real.cos x) * Real.sin x = (Real.sqrt (1 + Real.cos x ^ 2))⁻¹ := by
  rw [lemnIntegrand, sqrt_one_sub_cos_pow_four, abs_of_pos hs, mul_inv, mul_comm, ← mul_assoc,
    mul_inv_cancel₀ hs.ne', one_mul]

theorem abs_lemnIntegrand_cos_mul_sin_le (x : ℝ) :
    |lemnIntegrand (Real.cos x) * Real.sin x| ≤ 1 := by
  rw [lemnIntegrand, sqrt_one_sub_cos_pow_four, abs_mul, abs_inv, abs_mul, abs_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases eq_or_ne (Real.sin x) 0 with h0 | h0
  · simp [h0]
  · have hs : 0 < |Real.sin x| := abs_pos.mpr h0
    have hr : 1 ≤ Real.sqrt (1 + Real.cos x ^ 2) := by
      rw [Real.le_sqrt' one_pos]; nlinarith [sq_nonneg (Real.cos x)]
    rw [mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
    exact inv_le_one_of_one_le₀ hr

theorem cos_image_Ioo_subset : Real.cos '' Ioo 0 (π / 2) ⊆ Ico 0 1 := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩).le, ?_⟩
  have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl hx.2.le hx.1
  rwa [Real.cos_zero] at this

theorem cos_image_Icc_subset : Real.cos '' Icc 0 (π / 2) ⊆ Icc 0 1 := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩, Real.cos_le_one x⟩

theorem continuousOn_lemnIntegrand : ContinuousOn lemnIntegrand (Ico 0 1) := by
  refine ContinuousOn.inv₀ ?_ fun t ht => ?_
  · exact (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 4))).continuousOn
  · have : t ^ 4 < 1 := pow_lt_one₀ ht.1 ht.2 (by norm_num)
    exact (Real.sqrt_pos.mpr (by linarith)).ne'

theorem integral_lemnIntegrand :
    ∫ t in (0 : ℝ)..1, lemnIntegrand t
      = ∫ x in (0 : ℝ)..(π / 2), lemnIntegrand (Real.cos x) * Real.sin x := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hmin : min (0 : ℝ) (π / 2) = 0 := min_eq_left hpi
  have hmax : max (0 : ℝ) (π / 2) = π / 2 := max_eq_right hpi
  have key := intervalIntegral.integral_comp_mul_deriv''' (a := 0) (b := π / 2) (f := Real.cos)
    (f' := fun x => -Real.sin x) (g := lemnIntegrand) Real.continuous_cos.continuousOn
    (fun x _ => (Real.hasDerivAt_cos x).hasDerivWithinAt)
    (by rw [hmin, hmax]; exact continuousOn_lemnIntegrand.mono cos_image_Ioo_subset)
    (by
      rw [uIcc_of_le hpi]
      exact ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
        intervalIntegrable_lemnIntegrand).mono_set cos_image_Icc_subset)
    (by
      rw [uIcc_of_le hpi]
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le hpi).mp ?_
      refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_
        (Filter.Eventually.of_forall fun x => ?_)
      · exact ((measurable_lemnIntegrand.comp Real.measurable_cos).mul
          Real.measurable_sin.neg).aestronglyMeasurable
      · simp only [Function.comp, Real.norm_eq_abs, mul_neg, abs_neg]
        exact abs_lemnIntegrand_cos_mul_sin_le x)
  rw [Real.cos_zero, Real.cos_pi_div_two, intervalIntegral.integral_symm 0 1] at key
  have h2 : ∫ x in (0 : ℝ)..(π / 2), (lemnIntegrand ∘ Real.cos) x * (-Real.sin x)
      = -∫ x in (0 : ℝ)..(π / 2), lemnIntegrand (Real.cos x) * Real.sin x := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext x
    simp only [Function.comp, mul_neg]
  linarith

/-! ### `ϖ = √2 K(1/√2) = π/AGM(1, √2)` -/

theorem lemniscate_eq_sqrt_two_mul_ellipticK :
    lemniscate = Real.sqrt 2 * ellipticK salaminB0 := by
  have h2 : ∫ x in (0 : ℝ)..(π / 2), lemnIntegrand (Real.cos x) * Real.sin x
      = ∫ x in (0 : ℝ)..(π / 2),
          (Real.sqrt 2)⁻¹ * (Real.sqrt (1 - salaminB0 ^ 2 * Real.sin x ^ 2))⁻¹ := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le (by positivity)] at hx
    have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_pos, hx.2])
    have hc : 1 + Real.cos x ^ 2 = 2 * (1 - 1 / 2 * Real.sin x ^ 2) := by
      linear_combination Real.sin_sq_add_cos_sq x
    rw [lemnIntegrand_cos_mul_sin_of_pos hs, salaminB0_sq, hc,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv]
  rw [lemniscate, integral_lemnIntegrand, h2, intervalIntegral.integral_const_mul]
  unfold ellipticK
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  calc 2 * ((Real.sqrt 2)⁻¹ * ∫ θ in (0 : ℝ)..(π / 2),
        (Real.sqrt (1 - salaminB0 ^ 2 * Real.sin θ ^ 2))⁻¹)
      = (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt 2)⁻¹ * ∫ θ in (0 : ℝ)..(π / 2),
        (Real.sqrt (1 - salaminB0 ^ 2 * Real.sin θ ^ 2))⁻¹ := by rw [hsq]; ring
    _ = Real.sqrt 2 * ∫ θ in (0 : ℝ)..(π / 2),
        (Real.sqrt (1 - salaminB0 ^ 2 * Real.sin θ ^ 2))⁻¹ := by
        rw [mul_assoc (Real.sqrt 2), mul_inv_cancel₀ hs, mul_one]

/-- `AGM(1, √2) = √2 · AGM(1, 1/√2)`. -/
theorem AGM_one_sqrt_two : AGM 1 (Real.sqrt 2) = Real.sqrt 2 * AGM 1 salaminB0 := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hb0 := salaminB0_pos
  rw [AGM_comm 1 salaminB0, ← AGM_smul hs2 hb0 one_pos, mul_one, salaminB0,
    mul_one_div_cancel hs2.ne', AGM_comm]

/-- **Gauss**: `ϖ = π/AGM(1, √2)`. -/
theorem lemniscate_eq_pi_div_AGM : lemniscate = π / AGM 1 (Real.sqrt 2) := by
  rw [lemniscate_eq_sqrt_two_mul_ellipticK, ellipticK_salaminB0, AGM_one_sqrt_two]
  have hM : 0 < AGM 1 salaminB0 := AGM_one_pos salaminB0_pos
  have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [eq_div_iff (by positivity)]
  calc Real.sqrt 2 * (π / (2 * AGM 1 salaminB0)) * (Real.sqrt 2 * AGM 1 salaminB0)
      = (Real.sqrt 2 * Real.sqrt 2) * AGM 1 salaminB0 * (π / (2 * AGM 1 salaminB0)) := by ring
    _ = π := by rw [hsq]; field_simp

/-- `ϖ = π · G` with `G = 1/AGM(1, √2)` Gauss's constant. -/
theorem lemniscate_eq_pi_mul_gauss : lemniscate = π * (AGM 1 (Real.sqrt 2))⁻¹ := by
  rw [lemniscate_eq_pi_div_AGM, div_eq_mul_inv]

theorem lemniscate_pos : 0 < lemniscate := by
  rw [lemniscate_eq_pi_div_AGM]
  exact div_pos Real.pi_pos (AGM_one_pos (by positivity))

end Azurite.BZ
