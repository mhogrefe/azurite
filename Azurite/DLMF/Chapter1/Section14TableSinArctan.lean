/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableSinImproper

/-!
# DLMF Table 1.14.3, row 12: `𝓕_s[arctan(t/a)]`

**DLMF discrepancy.** For `a, x > 0` the integral `∫_0^∞ arctan(t/a) sin(xt) dt` does not converge,
even as an improper integral: with `arctan(t/a) = π/2 − arctan(a/t)`, the partial integrals are
`(π/2)(1 − cos(xR))/x − ∫_0^R arctan(a/t) sin(xt) dt`, and the last term converges
(`dlmf_table_1_14_3_r12_not_tendsto`). DLMF's value `√(π/2) e^{−ax}/x` is the Abel limit
`lim_{ε→0+} √(2/π) ∫_0^∞ e^{−εt} arctan(t/a) sin(xt) dt` (`dlmf_table_1_14_3_r12`), proved by
parts against the primitive `abelSinPrimitive` of `e^{−εt} sin(xt)` and dominated convergence.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### The kernel `a/(a² + t²)` -/

theorem abs_arctan_le_pi_div_two (y : ℝ) : |Real.arctan y| ≤ π / 2 :=
  abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan y).le, (Real.arctan_lt_pi_div_two y).le⟩

theorem arctan_div_eq {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    Real.arctan (t / a) = π / 2 - Real.arctan (a / t) := by
  rw [← Real.arctan_inv_of_pos (div_pos ha ht), inv_div]

theorem integrable_poisson_kernel {a : ℝ} (ha : 0 < a) :
    Integrable fun t : ℝ => a / (a ^ 2 + t ^ 2) := by
  refine ((integrable_inv_one_add_sq.comp_div ha.ne').const_mul a⁻¹).congr
    (ae_of_all _ fun t => ?_)
  simp only
  field_simp

theorem integral_poisson_kernel {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), a / (a ^ 2 + t ^ 2) = π / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
    (f := fun t : ℝ => Real.arctan (t / a))
    (f' := fun t => a / (a ^ 2 + t ^ 2)) (m := π / 2)
    ((by fun_prop : Continuous fun t : ℝ => Real.arctan (t / a)).continuousWithinAt)
    (fun t _ => by
      have := ((hasDerivAt_id' t).div_const a).arctan
      refine this.congr_deriv ?_
      field_simp)
    (integrable_poisson_kernel ha).integrableOn
    ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const ha))
  rw [h, zero_div, Real.arctan_zero, sub_zero]

theorem integral_poisson_kernel_cos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), a / (a ^ 2 + t ^ 2) * Real.cos (x * t) = π / 2 * Real.exp (-(a * x)) := by
  have h := integral_inv_sq_add_sq_cos (w := (a : ℂ)) (by simpa using ha) hx
  have e : ∀ t : ℝ, 1 / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) * ((Real.cos (x * t) : ℝ) : ℂ) =
      ((1 / (a ^ 2 + t ^ 2) * Real.cos (x * t) : ℝ) : ℂ) := fun t => by push_cast; ring
  simp_rw [e] at h
  rw [integral_complex_ofReal] at h
  have h' : ∫ t in Ioi (0 : ℝ), 1 / (a ^ 2 + t ^ 2) * Real.cos (x * t) =
      π / 2 * (Real.exp (-(a * x)) / a) := by
    apply ofReal_injective
    rw [h]; push_cast; ring
  have e2 : ∀ t : ℝ, a / (a ^ 2 + t ^ 2) * Real.cos (x * t) =
      a * (1 / (a ^ 2 + t ^ 2) * Real.cos (x * t)) := fun t => by ring
  simp_rw [e2]
  rw [integral_const_mul, h']
  field_simp

theorem continuous_poisson_kernel {a : ℝ} (ha : 0 < a) :
    Continuous fun t : ℝ => a / (a ^ 2 + t ^ 2) :=
  continuous_const.div (by fun_prop) fun t => by positivity

theorem integrableOn_poisson_kernel_mul {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} {C : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0))) (hC : ∀ t, 0 < t → |g t| ≤ C) :
    IntegrableOn (fun t => g t * (a / (a ^ 2 + t ^ 2))) (Ioi 0) := by
  refine ((integrable_poisson_kernel ha).integrableOn.const_mul C).mono'
    (hg.mul (continuous_poisson_kernel ha).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < a / (a ^ 2 + t ^ 2))]
  exact mul_le_mul_of_nonneg_right (hC t ht) (by positivity)

theorem abs_one_sub_cos_div_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    |(1 - Real.cos (x * t)) / x| ≤ 2 / x := by
  rw [abs_div, abs_of_pos hx]
  refine div_le_div_of_nonneg_right ?_ hx.le
  have := Real.abs_cos_le_one (x * t)
  rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]

/-- `∫_0^∞ (1 − cos(xt))/x · a/(a² + t²) dt = (π/2)(1 − e^{−ax})/x`. -/
theorem integral_one_sub_cos_poisson {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), (1 - Real.cos (x * t)) / x * (a / (a ^ 2 + t ^ 2)) =
      π / 2 * (1 - Real.exp (-(a * x))) / x := by
  have hk := (integrable_poisson_kernel ha).integrableOn (s := Ioi 0)
  have hkc : IntegrableOn (fun t => a / (a ^ 2 + t ^ 2) * Real.cos (x * t)) (Ioi 0) := by
    have := integrableOn_poisson_kernel_mul ha (g := fun t => Real.cos (x * t)) (C := 1)
      (by fun_prop) (fun t _ => Real.abs_cos_le_one _)
    simpa only [mul_comm] using this
  have e : ∀ t : ℝ, (1 - Real.cos (x * t)) / x * (a / (a ^ 2 + t ^ 2)) =
      x⁻¹ * (a / (a ^ 2 + t ^ 2) - a / (a ^ 2 + t ^ 2) * Real.cos (x * t)) := fun t => by
    field_simp
  simp_rw [e]
  rw [integral_const_mul, integral_sub hk hkc, integral_poisson_kernel ha,
    integral_poisson_kernel_cos ha hx]
  field_simp

/-! ### Partial integrals and divergence -/

theorem hasDerivAt_real_arctan_div {a t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.arctan (a / t)) (-(a / (a ^ 2 + t ^ 2))) t := by
  have := ((hasDerivAt_const t a).div (hasDerivAt_id' t) ht).arctan
  simp only [Pi.div_apply] at this
  refine this.congr_deriv ?_
  field_simp
  ring

theorem continuousOn_one_sub_cos_mul_arctan {a x : ℝ} (R : ℝ) :
    ContinuousOn (fun t : ℝ => (1 - Real.cos (x * t)) / x * Real.arctan (a / t)) (Icc 0 R) := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | htp
  · show Tendsto _ (𝓝[Icc 0 R] 0) (𝓝 ((1 - Real.cos (x * 0)) / x * Real.arctan (a / 0)))
    simp only [mul_zero, Real.cos_zero, sub_self, zero_div, zero_mul]
    have hg : Tendsto (fun t : ℝ => |(1 - Real.cos (x * t)) / x| * (π / 2)) (𝓝[Icc 0 R] 0)
        (𝓝 0) := by
      have := ((by fun_prop : Continuous fun t : ℝ => |(1 - Real.cos (x * t)) / x| * (π / 2)
        ).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Icc 0 R))
      simpa using this
    refine squeeze_zero_norm (fun s => ?_) hg
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_arctan_le_pi_div_two _) (abs_nonneg _)
  · exact ((by fun_prop : Continuous fun t : ℝ => (1 - Real.cos (x * t)) / x).continuousAt.mul
      (hasDerivAt_real_arctan_div (a := a) htp.ne').continuousAt).continuousWithinAt

theorem intervalIntegrable_arctan_div_mul_sin (a x : ℝ) {R : ℝ} :
    IntervalIntegrable (fun t : ℝ => Real.arctan (a / t) * Real.sin (x * t)) volume 0 R :=
  (intervalIntegrable_const (c := π / 2)).mono_fun'
    ((by fun_prop : Measurable fun t : ℝ => Real.arctan (a / t) * Real.sin (x * t))
      |>.aestronglyMeasurable)
    (ae_of_all _ fun t => by
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _) |>.trans
        (abs_arctan_le_pi_div_two _))

/-- `∫_0^R arctan(a/t) sin(xt) dt = (1 − cos(xR))/x · arctan(a/R) +
∫_0^R (1 − cos(xt))/x · a/(a² + t²) dt`. -/
theorem integral_arctan_div_mul_sin {a x : ℝ} (ha : 0 < a) (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0 : ℝ)..R, Real.arctan (a / t) * Real.sin (x * t) =
      (1 - Real.cos (x * R)) / x * Real.arctan (a / R) +
        ∫ t in (0 : ℝ)..R, (1 - Real.cos (x * t)) / x * (a / (a ^ 2 + t ^ 2)) := by
  have hk : IntervalIntegrable (fun t : ℝ => (1 - Real.cos (x * t)) / x * (a / (a ^ 2 + t ^ 2)))
      volume 0 R := ((by fun_prop : Continuous fun t : ℝ => (1 - Real.cos (x * t)) / x).mul
        (continuous_poisson_kernel ha)).intervalIntegrable _ _
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    (continuousOn_one_sub_cos_mul_arctan (a := a) (x := x) R) (fun t ht => ?_)
    ((intervalIntegrable_arctan_div_mul_sin a x).sub hk)
  · rw [intervalIntegral.integral_sub (intervalIntegrable_arctan_div_mul_sin a x) hk] at hF
    simp only [mul_zero, Real.cos_zero, sub_self, zero_div, zero_mul, sub_zero] at hF
    linarith
  · have htp : 0 < t := ht.1
    have hS : HasDerivAt (fun t : ℝ => (1 - Real.cos (x * t)) / x) (Real.sin (x * t)) t := by
      have := ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id' t).const_mul x).cos).div_const x
      refine this.congr_deriv ?_
      field_simp
      ring
    refine (hS.mul (hasDerivAt_real_arctan_div (a := a) htp.ne')).congr_deriv ?_
    ring

theorem integral_arctan_mul_sin {a x : ℝ} (ha : 0 < a) (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0 : ℝ)..R, Real.arctan (t / a) * Real.sin (x * t) =
      π / 2 * ((1 - Real.cos (x * R)) / x) -
        ∫ t in (0 : ℝ)..R, Real.arctan (a / t) * Real.sin (x * t) := by
  have hsin : ∫ t in (0 : ℝ)..R, Real.sin (x * t) = (1 - Real.cos (x * R)) / x := by
    have hc := intervalIntegral.integral_comp_mul_left (fun t => Real.sin t) hx.ne'
      (a := 0) (b := R)
    rw [hc, integral_sin, mul_zero, Real.cos_zero, smul_eq_mul]
    field_simp
  have hsI : IntervalIntegrable (fun t : ℝ => π / 2 * Real.sin (x * t)) volume 0 R :=
    (by fun_prop : Continuous fun t : ℝ => π / 2 * Real.sin (x * t)).intervalIntegrable _ _
  rw [← hsin, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hsI (intervalIntegrable_arctan_div_mul_sin a x)]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  rw [arctan_div_eq ha ht.1]
  ring

theorem tendsto_integral_arctan_div_mul_sin {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.arctan (a / t) * Real.sin (x * t)) atTop
      (𝓝 (π / 2 * (1 - Real.exp (-(a * x))) / x)) := by
  have hb : Tendsto (fun R : ℝ => (1 - Real.cos (x * R)) / x * Real.arctan (a / R)) atTop
      (𝓝 0) := by
    have hz : Tendsto (fun R : ℝ => 2 / x * |Real.arctan (a / R)|) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => Real.arctan (a / R)) atTop (𝓝 0) := by
        have := (Real.continuous_arctan.tendsto 0).comp
          ((tendsto_const_nhds (x := a)).div_atTop tendsto_id)
        simpa [Function.comp_def] using this
      simpa using (h1.abs).const_mul (2 / x)
    refine squeeze_zero_norm (fun R => ?_) hz
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_one_sub_cos_div_le hx R) (abs_nonneg _)
  have hk : IntegrableOn (fun t => (1 - Real.cos (x * t)) / x * (a / (a ^ 2 + t ^ 2))) (Ioi 0) :=
    integrableOn_poisson_kernel_mul ha (by fun_prop) (fun t _ => abs_one_sub_cos_div_le hx t)
  have hI := intervalIntegral_tendsto_integral_Ioi 0 hk tendsto_id
  rw [integral_one_sub_cos_poisson ha hx] at hI
  have := hb.add hI
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  rw [integral_arctan_div_mul_sin ha hx hR]
  rfl

theorem not_tendsto_cos_mul_atTop {x : ℝ} (hx : 0 < x) (c : ℝ) :
    ¬ Tendsto (fun R => Real.cos (x * R)) atTop (𝓝 c) := by
  intro h
  have hs1 : Tendsto (fun n : ℕ => 2 * π / x * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hs2 : Tendsto (fun n : ℕ => 2 * π / x * n + π / x) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hs1
  have h1 := h.comp hs1
  have h2 := h.comp hs2
  have e1 : (fun R => Real.cos (x * R)) ∘ (fun n : ℕ => 2 * π / x * n) = fun _ => 1 := by
    funext n; simp only [Function.comp]
    rw [show x * (2 * π / x * n) = n * (2 * π) by field_simp, Real.cos_nat_mul_two_pi]
  have e2 : (fun R => Real.cos (x * R)) ∘ (fun n : ℕ => 2 * π / x * n + π / x) = fun _ => -1 := by
    funext n; simp only [Function.comp]
    rw [show x * (2 * π / x * n + π / x) = n * (2 * π) + π by field_simp,
      Real.cos_nat_mul_two_pi_add_pi]
  rw [e1] at h1; rw [e2] at h2
  have := tendsto_nhds_unique tendsto_const_nhds h1
  have := tendsto_nhds_unique tendsto_const_nhds h2
  linarith

/-- **Table 1.14.3, row 12 (divergence)**: for `a, x > 0` the improper integral
`lim_{R→∞} √(2/π) ∫_0^R arctan(t/a) sin(xt) dt` does not exist: it equals
`√(2/π)[(π/2)(1 − cos(xR))/x − ∫_0^R arctan(a/t) sin(xt) dt]`, whose last term converges.
DLMF's value holds in the Abel sense, `dlmf_table_1_14_3_r12`. -/
theorem dlmf_table_1_14_3_r12_not_tendsto {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ¬ ∃ L : ℂ, Tendsto (fun R => ((√(2 / π) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..R, ((Real.arctan (t / a) : ℝ) : ℂ) * ((Real.sin (x * t) : ℝ) : ℂ))
        atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hs : 0 < √(2 / π) := by positivity
  have hJ : Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.arctan (t / a) * Real.sin (x * t)) atTop
      (𝓝 ((√(2 / π))⁻¹ * L.re)) := by
    have := ((Complex.continuous_re.tendsto L).comp hL).const_mul (√(2 / π))⁻¹
    refine this.congr fun R => ?_
    simp only [Function.comp, ← ofReal_mul, intervalIntegral.integral_ofReal, ofReal_re]
    rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have hB := tendsto_integral_arctan_div_mul_sin ha hx
  have hsum := hJ.add hB
  have hcos : Tendsto (fun R => Real.cos (x * R)) atTop
      (𝓝 (1 - 2 * x / π * ((√(2 / π))⁻¹ * L.re + π / 2 * (1 - Real.exp (-(a * x))) / x))) := by
    refine (tendsto_const_nhds.sub (hsum.const_mul (2 * x / π))).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [integral_arctan_mul_sin ha hx hR]
    field_simp
    ring
  exact not_tendsto_cos_mul_atTop hx _ hcos

/-! ### Abel summation -/

/-- The primitive `∫_0^t e^{−εs} sin(xs) ds = (x − e^{−εt}(ε sin(xt) + x cos(xt)))/(ε² + x²)`. -/
noncomputable def abelSinPrimitive (ε x t : ℝ) : ℝ :=
  (x - Real.exp (-(ε * t)) * (ε * Real.sin (x * t) + x * Real.cos (x * t))) / (ε ^ 2 + x ^ 2)

theorem continuous_abelSinPrimitive (ε x : ℝ) : Continuous (abelSinPrimitive ε x) := by
  unfold abelSinPrimitive; fun_prop

theorem abelSinPrimitive_zero (ε x : ℝ) : abelSinPrimitive ε x 0 = 0 := by
  simp [abelSinPrimitive]

theorem hasDerivAt_abelSinPrimitive (ε : ℝ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (abelSinPrimitive ε x) (Real.exp (-(ε * t)) * Real.sin (x * t)) t := by
  have he := ((hasDerivAt_id' t).const_mul ε).neg.exp
  have hs := ((hasDerivAt_id' t).const_mul x).sin
  have hc := ((hasDerivAt_id' t).const_mul x).cos
  have h := ((hasDerivAt_const t x).sub (he.mul ((hs.const_mul ε).add (hc.const_mul x)))).div_const
    (ε ^ 2 + x ^ 2)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply] at h
  unfold abelSinPrimitive
  refine h.congr_deriv ?_
  have : ε ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem abs_abelSinPrimitive_num_le {ε x t : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) (ht : 0 ≤ t) :
    |x - Real.exp (-(ε * t)) * (ε * Real.sin (x * t) + x * Real.cos (x * t))| ≤ 2 * x + ε := by
  have he : Real.exp (-(ε * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 := Real.exp_pos (-(ε * t))
  have h1 : |ε * Real.sin (x * t) + x * Real.cos (x * t)| ≤ ε + x := by
    calc _ ≤ |ε * Real.sin (x * t)| + |x * Real.cos (x * t)| := abs_add_le _ _
      _ ≤ ε * 1 + x * 1 := by
          rw [abs_mul, abs_mul, abs_of_nonneg hε, abs_of_pos hx]
          gcongr
          · exact Real.abs_sin_le_one _
          · exact Real.abs_cos_le_one _
      _ = ε + x := by ring
  calc _ ≤ |x| + |Real.exp (-(ε * t)) * (ε * Real.sin (x * t) + x * Real.cos (x * t))| :=
        abs_sub _ _
    _ ≤ x + 1 * (ε + x) := by
        rw [abs_of_pos hx, abs_mul, abs_of_pos he0]
        gcongr
    _ = 2 * x + ε := by ring

theorem abs_abelSinPrimitive_le {ε x t : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) (ht : 0 ≤ t) :
    |abelSinPrimitive ε x t| ≤ (2 * x + ε) / (ε ^ 2 + x ^ 2) := by
  unfold abelSinPrimitive
  rw [abs_div, abs_of_pos (by positivity : 0 < ε ^ 2 + x ^ 2)]
  exact div_le_div_of_nonneg_right (abs_abelSinPrimitive_num_le hε hx ht) (by positivity)

theorem abs_abelSinPrimitive_le' {ε x t : ℝ} (hε : 0 ≤ ε) (hεx : ε ≤ x) (hx : 0 < x)
    (ht : 0 ≤ t) : |abelSinPrimitive ε x t| ≤ 3 / x := by
  refine (abs_abelSinPrimitive_le hε hx ht).trans ?_
  rw [div_le_div_iff₀ (by positivity) hx]
  nlinarith

theorem tendsto_abelSinPrimitive {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    Tendsto (abelSinPrimitive ε x) atTop (𝓝 (x / (ε ^ 2 + x ^ 2))) := by
  have he : Tendsto (fun t => Real.exp (-(ε * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hε))
  have hb : Tendsto (fun t => Real.exp (-(ε * t)) *
      (ε * Real.sin (x * t) + x * Real.cos (x * t))) atTop (𝓝 0) := by
    have hz := he.mul_const (ε + x)
    rw [zero_mul] at hz
    refine squeeze_zero_norm (fun t => ?_) hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    calc _ ≤ |ε * Real.sin (x * t)| + |x * Real.cos (x * t)| := abs_add_le _ _
      _ ≤ ε * 1 + x * 1 := by
          rw [abs_mul, abs_mul, abs_of_pos hε, abs_of_pos hx]
          gcongr
          · exact Real.abs_sin_le_one _
          · exact Real.abs_cos_le_one _
      _ = ε + x := by ring
  have := (tendsto_const_nhds (x := x)).sub hb
  rw [sub_zero] at this
  exact this.div_const _

theorem integral_exp_mul_sin {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(ε * t)) * Real.sin (x * t) = x / (ε ^ 2 + x ^ 2) := by
  have hint : IntegrableOn (fun t => Real.exp (-(ε * t)) * Real.sin (x * t)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hε).mono' (by fun_prop)
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
    (continuous_abelSinPrimitive ε x).continuousWithinAt
    (fun t _ => hasDerivAt_abelSinPrimitive ε hx t) hint (tendsto_abelSinPrimitive hε hx)
  rw [h, abelSinPrimitive_zero ε x, sub_zero]

/-- `∫_0^∞ arctan(a/t) e^{−εt} sin(xt) dt = ∫_0^∞ P_ε(t) a/(a² + t²) dt` (integration by
parts against the primitive `P_ε = abelSinPrimitive ε x`). -/
theorem integral_arctan_div_mul_exp_sin {a ε x : ℝ} (ha : 0 < a) (hε : 0 < ε) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), Real.arctan (a / t) * (Real.exp (-(ε * t)) * Real.sin (x * t)) =
      ∫ t in Ioi (0 : ℝ), abelSinPrimitive ε x t * (a / (a ^ 2 + t ^ 2)) := by
  have hPb : ∀ t, 0 < t → |abelSinPrimitive ε x t| ≤ (2 * x + ε) / (ε ^ 2 + x ^ 2) :=
    fun t ht => abs_abelSinPrimitive_le hε.le hx ht.le
  have hkP := integrableOn_poisson_kernel_mul ha
    (continuous_abelSinPrimitive ε x).aestronglyMeasurable hPb
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := 0) (b' := 0)
    (u := fun t => Real.arctan (a / t)) (u' := fun t => -(a / (a ^ 2 + t ^ 2)))
    (v := abelSinPrimitive ε x) (v' := fun t => Real.exp (-(ε * t)) * Real.sin (x * t))
    (fun t ht => hasDerivAt_real_arctan_div (ne_of_gt ht))
    (fun t _ => hasDerivAt_abelSinPrimitive ε hx t)
    (by
      refine ((exp_neg_integrableOn_Ioi 0 hε).const_mul (π / 2)).mono' (by fun_prop)
        (ae_of_all _ fun t => ?_)
      simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
      calc |Real.arctan (a / t)| * (Real.exp (-(ε * t)) * |Real.sin (x * t)|)
          ≤ π / 2 * (Real.exp (-(ε * t)) * 1) := by
            gcongr
            · exact abs_arctan_le_pi_div_two _
            · exact Real.abs_sin_le_one _
        _ = π / 2 * Real.exp (-(ε * t)) := by ring)
    (by
      have := hkP.neg
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, Pi.neg_apply]; ring)
    (by
      have hc : Tendsto (fun t => (π / 2) * |abelSinPrimitive ε x t|) (𝓝[>] 0) (𝓝 0) := by
        have := ((continuous_abelSinPrimitive ε x).abs.const_mul (π / 2)).tendsto 0
        rw [abelSinPrimitive_zero ε x, abs_zero, mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm (fun t => ?_) hc
      simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_arctan_le_pi_div_two _) (abs_nonneg _))
    (by
      have h1 : Tendsto (fun t : ℝ => Real.arctan (a / t)) atTop (𝓝 0) := by
        have := (Real.continuous_arctan.tendsto 0).comp
          ((tendsto_const_nhds (x := a)).div_atTop tendsto_id)
        simpa [Function.comp_def] using this
      have hz := h1.norm.mul_const ((2 * x + ε) / (ε ^ 2 + x ^ 2))
      rw [norm_zero, zero_mul] at hz
      refine squeeze_zero_norm' ?_ hz
      filter_upwards [eventually_gt_atTop 0] with t ht
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_left (hPb t ht) (norm_nonneg _))
  rw [h, sub_zero, zero_sub, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

theorem tendsto_integral_abelSinPrimitive {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Tendsto (fun ε => ∫ t in Ioi (0 : ℝ), abelSinPrimitive ε x t * (a / (a ^ 2 + t ^ 2)))
      (𝓝[>] 0) (𝓝 (π / 2 * (1 - Real.exp (-(a * x))) / x)) := by
  rw [← integral_one_sub_cos_poisson ha hx]
  refine tendsto_integral_filter_of_dominated_convergence (fun t => 3 / x * (a / (a ^ 2 + t ^ 2)))
    (Eventually.of_forall fun ε => ((continuous_abelSinPrimitive ε x).mul
      (continuous_poisson_kernel ha)).aestronglyMeasurable) ?_
    ((integrable_poisson_kernel ha).integrableOn.const_mul _) ?_
  · filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < a / (a ^ 2 + t ^ 2))]
    exact mul_le_mul_of_nonneg_right (abs_abelSinPrimitive_le' hε.1.le hε.2.le hx (le_of_lt ht))
      (by positivity)
  · refine ae_of_all _ fun t => ?_
    have hc : ContinuousAt (fun ε => abelSinPrimitive ε x t * (a / (a ^ 2 + t ^ 2))) 0 := by
      unfold abelSinPrimitive
      exact ((ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)).mul
        continuousAt_const)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    convert this using 2
    unfold abelSinPrimitive
    simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
    field_simp
    ring

/-- **Table 1.14.3, row 12**: `𝓕_s[arctan(t/a)](x) = √(π/2) e^{−ax}/x` (`a, x > 0`) in the Abel
sense: `lim_{ε→0+} √(2/π) ∫_0^∞ e^{−εt} arctan(t/a) sin(xt) dt`. The improper integral itself
diverges (`dlmf_table_1_14_3_r12_not_tendsto`). -/
theorem dlmf_table_1_14_3_r12 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Tendsto (fun ε => ((√(2 / π) : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((Real.exp (-(ε * t)) : ℝ) : ℂ) * ((Real.arctan (t / a) : ℝ) : ℂ) *
          ((Real.sin (x * t) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (((√(π / 2) : ℝ) : ℂ) * ((Real.exp (-(a * x)) / x : ℝ) : ℂ))) := by
  have key : ∀ ε, 0 < ε → ∫ t in Ioi (0 : ℝ),
      Real.exp (-(ε * t)) * Real.arctan (t / a) * Real.sin (x * t) =
      π / 2 * (x / (ε ^ 2 + x ^ 2)) -
        ∫ t in Ioi (0 : ℝ), abelSinPrimitive ε x t * (a / (a ^ 2 + t ^ 2)) := fun ε hε => by
    have hes : IntegrableOn (fun t => Real.exp (-(ε * t)) * Real.sin (x * t)) (Ioi 0) := by
      refine (exp_neg_integrableOn_Ioi 0 hε).mono' (by fun_prop) (ae_of_all _ fun t => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)
    have hae : IntegrableOn
        (fun t => Real.arctan (a / t) * (Real.exp (-(ε * t)) * Real.sin (x * t))) (Ioi 0) := by
      refine (hes.norm.const_mul (π / 2)).mono' (by fun_prop) (ae_of_all _ fun t => ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_arctan_le_pi_div_two _) (abs_nonneg _)
    rw [← integral_exp_mul_sin hε hx, ← integral_arctan_div_mul_exp_sin ha hε hx,
      ← integral_const_mul, ← integral_sub (hes.const_mul _) hae]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [arctan_div_eq ha ht]
    ring
  have h1 : Tendsto (fun ε : ℝ => π / 2 * (x / (ε ^ 2 + x ^ 2))) (𝓝[>] 0)
      (𝓝 (π / 2 * (x / ((0 : ℝ) ^ 2 + x ^ 2)))) := by
    have : ContinuousAt (fun ε : ℝ => π / 2 * (x / (ε ^ 2 + x ^ 2))) 0 :=
      continuousAt_const.mul (continuousAt_const.div (by fun_prop) (by positivity))
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := h1.sub (tendsto_integral_abelSinPrimitive ha hx)
  have hreal := hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => (key ε hε).symm)
  have hc := ((continuous_ofReal.tendsto _).comp hreal).const_mul ((√(2 / π) : ℝ) : ℂ)
  refine (hc.congr fun ε => ?_).trans (le_of_eq ?_)
  · simp only [Function.comp, ← ofReal_mul, integral_complex_ofReal]
  · have hv : π / 2 * (x / ((0 : ℝ) ^ 2 + x ^ 2)) - π / 2 * (1 - Real.exp (-(a * x))) / x =
        π / 2 * (Real.exp (-(a * x)) / x) := by
      field_simp
      ring
    rw [hv, ofReal_mul, ← mul_assoc, sqrt_two_div_pi_mul_pi_div_two]

end Azurite.DLMF
