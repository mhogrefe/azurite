/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableSin
import Azurite.DLMF.Chapter1.Section14Inversion

/-!
# DLMF Table 1.14.3: improper Fourier sine transforms

Rows whose integrals converge only as `lim_{R→∞} √(2/π) ∫_0^R` (rows 1, 2, 4, 11), and row 3.

* Row 1 (`t^{−1}`): the Dirichlet integral `tendsto_sinInt` (`Section14Inversion.lean`).
* Row 4 (`t/(a² + t²)`): row 1 minus `a²` times row 6.
* Row 11 (`sin(at)/t`, `x ≠ a`): the Frullani integral `tendsto_integral_cos_sub_cos`,
  `∫_0^R (cos(bt) − cos(ct))/t dt → ln(c/b)`.
* Rows 2–3 (`t^{−1/2}`, `t^{−3/2}`): `t = u²` (`integral_inv_sqrt_mul_comp`) reduces to the Fresnel
  integrals `∫_0^∞ sin(at²) dt = ∫_0^∞ cos(at²) dt = √(π/2)/(2√a)` (Table 1.14.2 rows 7–8 at
  `x = 0`); row 3 is a Lebesgue integral, by parts against `−2t^{−1/2}`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Tools -/

theorem tendsto_sqrt_two_div_pi_ofReal {φ : ℝ → ℝ} {L : ℝ}
    (h : Tendsto (fun R => ∫ t in (0 : ℝ)..R, φ t) atTop (𝓝 L)) :
    Tendsto (fun R => ((√(2 / π) : ℝ) : ℂ) * ∫ t in (0 : ℝ)..R, ((φ t : ℝ) : ℂ)) atTop
      (𝓝 (((√(2 / π) : ℝ) : ℂ) * L)) := by
  simp_rw [intervalIntegral.integral_ofReal]
  exact ((continuous_ofReal.tendsto L).comp h).const_mul _

theorem abs_inv_mul_sin_le (x t : ℝ) : |t⁻¹ * Real.sin (x * t)| ≤ |x| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [abs_mul, abs_inv, inv_mul_le_iff₀ (abs_pos.mpr ht), mul_comm, ← abs_mul]
  exact Real.abs_sin_le_abs

theorem intervalIntegrable_inv_mul_sin (x a b : ℝ) :
    IntervalIntegrable (fun t => t⁻¹ * Real.sin (x * t)) volume a b :=
  (intervalIntegrable_const (c := |x|)).mono_fun'
    ((by fun_prop : Measurable fun t : ℝ => t⁻¹ * Real.sin (x * t)).aestronglyMeasurable)
    (ae_of_all _ fun t => by simp only [Real.norm_eq_abs]; exact abs_inv_mul_sin_le x t)

theorem intervalIntegrable_inv_mul_sin_complex (x a b : ℝ) :
    IntervalIntegrable (fun t => ((t⁻¹ * Real.sin (x * t) : ℝ) : ℂ)) volume a b :=
  (intervalIntegrable_const (c := |x|)).mono_fun'
    ((by fun_prop : Measurable fun t : ℝ => ((t⁻¹ * Real.sin (x * t) : ℝ) : ℂ))
      |>.aestronglyMeasurable)
    (ae_of_all _ fun t => by simp only [Complex.norm_real, Real.norm_eq_abs]
                             exact abs_inv_mul_sin_le x t)

theorem integrableOn_div_mul_sin {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) (x : ℝ) :
    IntegrableOn (fun t => g t / t * ((Real.sin (x * t) : ℝ) : ℂ)) (Ioi 0) := by
  have hm1 : Measurable fun t : ℝ => ((t : ℂ))⁻¹ * ((Real.sin (x * t) : ℝ) : ℂ) := by fun_prop
  have hm := hg.aestronglyMeasurable.mul hm1.aestronglyMeasurable
  refine (hg.norm.mul_const |x|).mono' (hm.congr (ae_of_all _ fun t => ?_))
    (ae_of_all _ fun t => ?_)
  · simp only [Pi.mul_apply]; ring
  rw [div_mul_eq_mul_div, mul_div_assoc, norm_mul,
    show ((Real.sin (x * t) : ℝ) : ℂ) / (t : ℂ) = ((t⁻¹ * Real.sin (x * t) : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_inv_mul_sin_le x t) (norm_nonneg _)

/-- `∫_0^R sin(xt)/t dt → π/2` (`x > 0`; the Dirichlet integral). -/
theorem tendsto_integral_inv_mul_sin {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, t⁻¹ * Real.sin (x * t)) atTop (𝓝 (π / 2)) := by
  have e : ∀ R, ∫ t in (0 : ℝ)..R, t⁻¹ * Real.sin (x * t) = sinInt (x * R) := fun R => by
    have hp : ∀ t : ℝ, t⁻¹ * Real.sin (x * t) = x * (fun z => Real.sin z / z) (x * t) :=
      fun t => by
        rcases eq_or_ne t 0 with rfl | ht
        · simp
        · simp only; field_simp
    simp_rw [hp]
    have hc := intervalIntegral.integral_comp_mul_left (fun z => Real.sin z / z) hx.ne'
      (a := 0) (b := R)
    rw [intervalIntegral.integral_const_mul, hc, mul_zero, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hx.ne', one_mul, sinInt]
  simp_rw [e]
  exact tendsto_sinInt.comp (tendsto_id.const_mul_atTop hx)

theorem sqrt_two_div_pi_mul_pi_div_two :
    ((√(2 / π) : ℝ) : ℂ) * ((π / 2 : ℝ) : ℂ) = ((√(π / 2) : ℝ) : ℂ) := by
  rw [← ofReal_mul]
  congr 1
  have h : π / 2 = 2 / π * (π / 2) ^ 2 := by field_simp
  conv_rhs => rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-! ### Row 1 -/

/-- **Table 1.14.3, row 1**: `𝓕_s[t^{−1}](x) = √(π/2)` (`x > 0`), as the improper integral
`lim_{R→∞} √(2/π) ∫_0^R`. -/
theorem dlmf_table_1_14_3_r1 {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R => ((√(2 / π) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..R, ((t⁻¹ : ℝ) : ℂ) * ((Real.sin (x * t) : ℝ) : ℂ)) atTop
      (𝓝 ((√(π / 2) : ℝ) : ℂ)) := by
  have h := tendsto_sqrt_two_div_pi_ofReal (tendsto_integral_inv_mul_sin hx)
  rw [← sqrt_two_div_pi_mul_pi_div_two]
  push_cast at h ⊢
  exact h

/-! ### Row 4 -/

/-- **Table 1.14.3, row 4**: `𝓕_s[t/(a² + t²)](x) = √(π/2) e^{−ax}` (`ℜa > 0`, `x > 0`), as an
improper integral. -/
theorem dlmf_table_1_14_3_r4 {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R => ((√(2 / π) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..R, (t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) * ((Real.sin (x * t) : ℝ) : ℂ)) atTop
      (𝓝 (((√(π / 2) : ℝ) : ℂ) * cexp (-(a * x)))) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  set g : ℝ → ℂ := fun t => 1 / (a ^ 2 + (t : ℂ) ^ 2)
  have hg : IntegrableOn g (Ioi 0) := by
    simpa only [g, one_div] using (integrable_inv_sq_add_sq ha).integrableOn
  have hgs := integrableOn_div_mul_sin hg x
  have hp : ∀ t : ℝ, (t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) * ((Real.sin (x * t) : ℝ) : ℂ) =
      ((t⁻¹ * Real.sin (x * t) : ℝ) : ℂ) -
        a ^ 2 * (g t / t * ((Real.sin (x * t) : ℝ) : ℂ)) := fun t => by
    rcases eq_or_ne t 0 with rfl | ht
    · simp [g]
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
    have hs := sq_add_sq_ne_zero ha t
    simp only [g]; push_cast
    field_simp
    ring
  have hI1 : ∀ R, IntervalIntegrable (fun t : ℝ => ((t⁻¹ * Real.sin (x * t) : ℝ) : ℂ))
      volume 0 R := fun R => intervalIntegrable_inv_mul_sin_complex x 0 R
  have hI2 : ∀ R, 0 ≤ R → IntervalIntegrable
      (fun t : ℝ => a ^ 2 * (g t / t * ((Real.sin (x * t) : ℝ) : ℂ))) volume 0 R := fun R hR =>
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
      (hgs.mono_set Ioc_subset_Ioi_self)).const_mul _
  have h1 := tendsto_sqrt_two_div_pi_ofReal (tendsto_integral_inv_mul_sin hx)
  have h2 := ((intervalIntegral_tendsto_integral_Ioi 0 hgs tendsto_id).const_mul
    (((√(2 / π) : ℝ) : ℂ) * a ^ 2))
  simp only [id] at h2
  have hlim := h1.sub h2
  have e6 : ((√(2 / π) : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ), g t / t * ((Real.sin (x * t) : ℝ) : ℂ) =
      ((√(π / 2) : ℝ) : ℂ) * ((1 - cexp (-(a * x))) / a ^ 2) := by
    rw [← dlmf_table_1_14_3_r6 ha hx]
    unfold dlmfFourierSin
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [g]; rw [div_div, mul_comm (a ^ 2 + _)]
  have hval : ((√(2 / π) : ℝ) : ℂ) * ((π / 2 : ℝ) : ℂ) - ((√(2 / π) : ℝ) : ℂ) * a ^ 2 *
      ∫ t in Ioi (0 : ℝ), g t / t * ((Real.sin (x * t) : ℝ) : ℂ) =
      ((√(π / 2) : ℝ) : ℂ) * cexp (-(a * x)) := by
    rw [show ((√(2 / π) : ℝ) : ℂ) * a ^ 2 *
        ∫ t in Ioi (0 : ℝ), g t / t * ((Real.sin (x * t) : ℝ) : ℂ) =
        a ^ 2 * (((√(2 / π) : ℝ) : ℂ) *
          ∫ t in Ioi (0 : ℝ), g t / t * ((Real.sin (x * t) : ℝ) : ℂ)) by ring, e6,
      sqrt_two_div_pi_mul_pi_div_two]
    field_simp
    ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  simp_rw [hp]
  rw [intervalIntegral.integral_sub (hI1 R) (hI2 R hR), intervalIntegral.integral_const_mul]
  ring

/-! ### Row 11: a Frullani integral -/

theorem abs_inv_mul_one_sub_cos_le (u : ℝ) : |u⁻¹ * (1 - Real.cos u)| ≤ |u| / 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have h1 : 0 ≤ 1 - Real.cos u := by linarith [Real.cos_le_one u]
  have h2 : 1 - Real.cos u ≤ u ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := u)]
  rw [abs_mul, abs_inv, abs_of_nonneg h1, inv_mul_le_iff₀ (abs_pos.mpr hu)]
  calc 1 - Real.cos u ≤ u ^ 2 / 2 := h2
    _ = |u| * (|u| / 2) := by rw [← sq_abs]; ring

theorem intervalIntegrable_inv_mul_one_sub_cos (a b : ℝ) :
    IntervalIntegrable (fun u => u⁻¹ * (1 - Real.cos u)) volume a b :=
  ((continuous_abs.div_const 2).intervalIntegrable a b).mono_fun'
    ((by fun_prop : Measurable fun u : ℝ => u⁻¹ * (1 - Real.cos u)).aestronglyMeasurable)
    (ae_of_all _ fun u => by simp only [Real.norm_eq_abs]; exact abs_inv_mul_one_sub_cos_le u)

theorem integral_inv_mul_one_sub_cos_comp {b : ℝ} (hb : 0 < b) (R : ℝ) :
    ∫ t in (0 : ℝ)..R, t⁻¹ * (1 - Real.cos (b * t)) =
      ∫ u in (0 : ℝ)..b * R, u⁻¹ * (1 - Real.cos u) := by
  have hp : ∀ t : ℝ, t⁻¹ * (1 - Real.cos (b * t)) =
      b * (fun u => u⁻¹ * (1 - Real.cos u)) (b * t) := fun t => by
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · simp only; field_simp
  simp_rw [hp]
  have hc := intervalIntegral.integral_comp_mul_left (fun u => u⁻¹ * (1 - Real.cos u)) hb.ne'
    (a := 0) (b := R)
  rw [intervalIntegral.integral_const_mul, hc, mul_zero, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hb.ne', one_mul]

/-- `|∫_A^B cos u/u du| ≤ 2/A + 2/B + |B − A|/m²` for `0 < m ≤ A, B` (integration by parts). -/
theorem abs_integral_inv_mul_cos_le {A B m : ℝ} (hm : 0 < m) (hA : m ≤ A) (hB : m ≤ B) :
    |∫ u in A..B, u⁻¹ * Real.cos u| ≤ 1 / A + 1 / B + |B - A| / m ^ 2 := by
  have hpos : ∀ u ∈ uIcc A B, 0 < u := fun u hu => by
    rcases le_total A B with h | h
    · rw [uIcc_of_le h] at hu; linarith [hu.1]
    · rw [uIcc_of_ge h] at hu; linarith [hu.1]
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := A) (b := B)
    (u := fun u : ℝ => u⁻¹) (u' := fun u => -(u ^ 2)⁻¹) (v := Real.sin) (v' := Real.cos)
    (fun u hu => hasDerivAt_inv (hpos u hu).ne') (fun u _ => Real.hasDerivAt_sin u)
    ((ContinuousOn.inv₀ (continuousOn_pow 2) fun u hu =>
      pow_ne_zero 2 (hpos u hu).ne').neg.intervalIntegrable)
    (Real.continuous_cos.intervalIntegrable _ _)
  rw [hibp]
  have hA0 : 0 < A := hm.trans_le hA
  have hB0 : 0 < B := hm.trans_le hB
  have hI : |∫ u in A..B, -(u ^ 2)⁻¹ * Real.sin u| ≤ 1 / m ^ 2 * |B - A| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    have hu' : m ≤ u := by
      rcases le_total A B with h | h
      · rw [uIoc_of_le h] at hu; linarith [hu.1]
      · rw [uIoc_of_ge h] at hu; linarith [hu.1]
    have hu0 : 0 < u := hm.trans_le hu'
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_of_pos (by positivity)]
    calc (u ^ 2)⁻¹ * |Real.sin u| ≤ (u ^ 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one u) (by positivity)
      _ ≤ 1 / m ^ 2 := by
          rw [mul_one, one_div]; exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hm.le hu' 2)
  have hsA : |A⁻¹ * Real.sin A| ≤ 1 / A := by
    rw [abs_mul, abs_inv, abs_of_pos hA0, one_div]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one A)
  have hsB : |B⁻¹ * Real.sin B| ≤ 1 / B := by
    rw [abs_mul, abs_inv, abs_of_pos hB0, one_div]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one B)
  calc |B⁻¹ * Real.sin B - A⁻¹ * Real.sin A - ∫ u in A..B, -(u ^ 2)⁻¹ * Real.sin u|
      ≤ |B⁻¹ * Real.sin B| + |A⁻¹ * Real.sin A| + |∫ u in A..B, -(u ^ 2)⁻¹ * Real.sin u| := by
        have := abs_sub (B⁻¹ * Real.sin B - A⁻¹ * Real.sin A)
          (∫ u in A..B, -(u ^ 2)⁻¹ * Real.sin u)
        have := abs_sub (B⁻¹ * Real.sin B) (A⁻¹ * Real.sin A)
        linarith
    _ ≤ _ := by
        have : 1 / m ^ 2 * |B - A| = |B - A| / m ^ 2 := by ring
        linarith

/-- Frullani: `∫_0^R (cos(bt) − cos(ct))/t dt → ln(c/b)` (`b, c > 0`). -/
theorem tendsto_integral_cos_sub_cos {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, t⁻¹ * (Real.cos (b * t) - Real.cos (c * t))) atTop
      (𝓝 (Real.log (c / b))) := by
  set m := min b c
  have hm : 0 < m := lt_min hb hc
  have key : ∀ R, 0 < R → ∫ t in (0 : ℝ)..R, t⁻¹ * (Real.cos (b * t) - Real.cos (c * t)) =
      Real.log (c / b) - ∫ u in b * R..c * R, u⁻¹ * Real.cos u := fun R hR => by
    have hp : ∀ t : ℝ, t⁻¹ * (Real.cos (b * t) - Real.cos (c * t)) =
        t⁻¹ * (1 - Real.cos (c * t)) - t⁻¹ * (1 - Real.cos (b * t)) := fun t => by ring
    simp_rw [hp]
    have hi : ∀ d : ℝ, 0 < d → IntervalIntegrable (fun t => t⁻¹ * (1 - Real.cos (d * t)))
        volume 0 R := fun d hd => by
      refine ((by fun_prop : Continuous fun t : ℝ => d * (|d * t| / 2)).intervalIntegrable 0 R
        ).mono_fun' ((by fun_prop : Measurable fun t : ℝ => t⁻¹ * (1 - Real.cos (d * t)))
          |>.aestronglyMeasurable) (ae_of_all _ fun t => ?_)
      simp only [Real.norm_eq_abs]
      rcases eq_or_ne t 0 with rfl | ht
      · simp
      have e : t⁻¹ * (1 - Real.cos (d * t)) = d * ((d * t)⁻¹ * (1 - Real.cos (d * t))) := by
        field_simp
      rw [e, abs_mul, abs_of_pos hd]
      exact mul_le_mul_of_nonneg_left (abs_inv_mul_one_sub_cos_le _) hd.le
    rw [intervalIntegral.integral_sub (hi c hc) (hi b hb), integral_inv_mul_one_sub_cos_comp hc,
      integral_inv_mul_one_sub_cos_comp hb,
      intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_mul_one_sub_cos _ _)
        (intervalIntegrable_inv_mul_one_sub_cos _ _)]
    have hpos : ∀ u ∈ uIcc (b * R) (c * R), u ≠ 0 := fun u hu => by
      have : 0 < min (b * R) (c * R) := lt_min (by positivity) (by positivity)
      exact (this.trans_le hu.1).ne'
    have e : ∀ u : ℝ, u⁻¹ * (1 - Real.cos u) = u⁻¹ - u⁻¹ * Real.cos u := fun u => by ring
    simp_rw [e]
    have hinv := intervalIntegral.intervalIntegrable_inv (μ := volume) hpos continuousOn_id
    rw [intervalIntegral.integral_sub hinv
        (hinv.mul_continuousOn Real.continuous_cos.continuousOn),
      integral_inv_of_pos (by positivity) (by positivity)]
    congr 2
    field_simp
  have hbound : ∀ R, 0 < R → |∫ u in b * R..c * R, u⁻¹ * Real.cos u| ≤
      (1 / b + 1 / c + |c - b| / m ^ 2) * R⁻¹ := fun R hR => by
    have hbm : m * R ≤ b * R := mul_le_mul_of_nonneg_right (min_le_left _ _) hR.le
    have hcm : m * R ≤ c * R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
    refine (abs_integral_inv_mul_cos_le (by positivity) hbm hcm).trans (le_of_eq ?_)
    rw [← sub_mul, abs_mul, abs_of_pos hR]
    field_simp
  have h0 : Tendsto (fun R => ∫ u in b * R..c * R, u⁻¹ * Real.cos u) atTop (𝓝 0) := by
    have hz := tendsto_inv_atTop_zero.const_mul (1 / b + 1 / c + |c - b| / m ^ 2)
    rw [mul_zero] at hz
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [Real.norm_eq_abs]; exact hbound R hR
  have := (tendsto_const_nhds (x := Real.log (c / b))).sub h0
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [key R hR]

theorem cos_abs_mul (y t : ℝ) : Real.cos (|y| * t) = Real.cos (y * t) := by
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  rw [neg_mul, Real.cos_neg]

/-- **Table 1.14.3, row 11**: `𝓕_s[sin(at)/t](x) = (2π)^{−1/2} ln|(x + a)/(x − a)|` (`a > 0`,
`x > 0`, `x ≠ a`), as an improper integral. -/
theorem dlmf_table_1_14_3_r11 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hxa : x ≠ a) :
    Tendsto (fun R => ((√(2 / π) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..R, ((Real.sin (a * t) / t : ℝ) : ℂ) * ((Real.sin (x * t) : ℝ) : ℂ))
      atTop (𝓝 (((√(2 * π) : ℝ) : ℂ)⁻¹ * Real.log |(x + a) / (x - a)|)) := by
  have hb : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr hxa)
  have h := (tendsto_integral_cos_sub_cos hb (by linarith : 0 < x + a)).const_mul (1 / 2)
  have h2 := tendsto_sqrt_two_div_pi_ofReal (φ := fun t =>
    1 / 2 * (t⁻¹ * (Real.cos (|x - a| * t) - Real.cos ((x + a) * t)))) (by
      simpa only [intervalIntegral.integral_const_mul] using h)
  have hp : ∀ t : ℝ, ((Real.sin (a * t) / t : ℝ) : ℂ) * ((Real.sin (x * t) : ℝ) : ℂ) =
      ((1 / 2 * (t⁻¹ * (Real.cos (|x - a| * t) - Real.cos ((x + a) * t))) : ℝ) : ℂ) :=
    fun t => by
      rw [← ofReal_mul]
      congr 1
      rw [cos_abs_mul, sub_mul, add_mul, Real.cos_sub, Real.cos_add]
      ring
  simp_rw [hp]
  convert h2 using 2
  have e : Real.log |(x + a) / (x - a)| = Real.log ((x + a) / |x - a|) := by
    rw [abs_div, abs_of_pos (by linarith : 0 < x + a)]
  rw [e, ← sqrt_two_div_pi]
  push_cast
  ring

/-! ### Rows 2–3: powers, via `t = u²` and the Fresnel integrals -/

theorem rpow_neg_half_eq {t : ℝ} (ht : 0 ≤ t) : t ^ (-(1 / 2 : ℝ)) = (√t)⁻¹ := by
  rw [Real.rpow_neg ht, Real.sqrt_eq_rpow]

theorem rpow_neg_three_halves_eq {t : ℝ} (ht : 0 ≤ t) : t ^ (-(3 / 2 : ℝ)) = (t * √t)⁻¹ := by
  rw [Real.rpow_neg ht, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' ht (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]

theorem intervalIntegrable_inv_sqrt {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun t => (√t)⁻¹) volume 0 R :=
  (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2)) (by norm_num)).congr
    fun t ht => by
      rw [uIoc_of_le hR] at ht
      exact rpow_neg_half_eq ht.1.le

theorem intervalIntegrable_inv_sqrt_mul {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hb : ∀ y, |φ y| ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun t => (√t)⁻¹ * φ t) volume 0 R :=
  (intervalIntegrable_inv_sqrt hR).norm.mono_fun'
    ((by fun_prop : Measurable fun t : ℝ => (√t)⁻¹).mul hφ.measurable |>.aestronglyMeasurable)
    (ae_of_all _ fun t => by
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hb t))

/-- `∫_0^R φ(t)/√t dt = ∫_0^{√R} 2 φ(u²) du`. -/
theorem integral_inv_sqrt_mul_comp {φ : ℝ → ℝ} (hφ : Continuous φ) (hb : ∀ y, |φ y| ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0 : ℝ)..R, (√t)⁻¹ * φ t = ∫ u in (0 : ℝ)..√R, 2 * φ (u ^ 2) := by
  have hs := Real.sqrt_nonneg R
  have hsub := intervalIntegral.integral_comp_mul_deriv''' (a := 0) (b := √R)
    (f := fun u : ℝ => u ^ 2) (f' := fun u => 2 * u) (g := fun t => (√t)⁻¹ * φ t)
    (by fun_prop) (fun u _ => by
      have := (hasDerivAt_pow 2 u).hasDerivWithinAt (s := Ioi u)
      simpa using this)
    (by
      refine (((Real.continuous_sqrt.continuousOn.inv₀ fun t (ht : 0 < t) =>
        (Real.sqrt_pos.mpr ht).ne').mul hφ.continuousOn)).mono ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [min_eq_left hs] at hu
      exact pow_pos hu.1 2)
    (by
      have h := (intervalIntegrable_iff_integrableOn_Icc_of_le hR).mp
        (intervalIntegrable_inv_sqrt_mul hφ hb hR)
      refine h.mono_set ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [uIcc_of_le hs] at hu
      refine ⟨sq_nonneg u, ?_⟩
      calc u ^ 2 ≤ √R ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
        _ = R := Real.sq_sqrt hR)
    (by
      rw [uIcc_of_le hs, integrableOn_Icc_iff_integrableOn_Ioc]
      refine ((by fun_prop : Continuous fun u : ℝ => 2 * φ (u ^ 2)).integrableOn_Icc
        |>.mono_set Ioc_subset_Icc_self).congr_fun (fun u hu => ?_) measurableSet_Ioc
      simp only [Function.comp, Real.sqrt_sq hu.1.le]
      field_simp [hu.1.ne'])
  simp only [Function.comp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Real.sq_sqrt hR] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun u hu => ?_)
  rw [uIoc_of_le hs] at hu
  rw [Real.sqrt_sq hu.1.le]
  field_simp [hu.1.ne']

theorem sqrt_pi_div_two_mul_real : √(π / 2) * √(2 / π) = 1 := by
  rw [← Real.sqrt_mul (by positivity), show π / 2 * (2 / π) = 1 by field_simp, Real.sqrt_one]

theorem fresnel_value {a : ℝ} (ha : 0 < a) :
    √(π / 2) * (1 / √(2 * a) * (√2 / 2)) = √(π / 2) / (2 * √a) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : √2 ≠ 0 := by positivity
  have ha' : √a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  field_simp

/-- `∫_0^R sin(at²) dt → √(π/2)/(2√a)` (`a > 0`), from Table 1.14.2 row 7 at `x = 0`. -/
theorem tendsto_integral_sin_mul_sq {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.sin (a * t ^ 2)) atTop
      (𝓝 (√(π / 2) / (2 * √a))) := by
  have h := dlmf_table_1_14_2_r7 ha 0
  simp only [zero_mul, Real.cos_zero, ofReal_one, mul_one] at h
  simp_rw [intervalIntegral.integral_ofReal] at h
  have h' := ((Complex.continuous_re.tendsto _).comp h).const_mul (√(π / 2))
  simp only [Function.comp_def, ← ofReal_mul, ofReal_re] at h'
  simp_rw [← mul_assoc, sqrt_pi_div_two_mul_real, one_mul] at h'
  convert h' using 2
  rw [show (0 : ℝ) ^ 2 / (4 * a) - π / 4 = -(π / 4) by ring, Real.sin_neg,
    Real.sin_pi_div_four, ← fresnel_value ha]
  ring

/-- `∫_0^R cos(at²) dt → √(π/2)/(2√a)` (`a > 0`), from Table 1.14.2 row 8 at `x = 0`. -/
theorem tendsto_integral_cos_mul_sq {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.cos (a * t ^ 2)) atTop
      (𝓝 (√(π / 2) / (2 * √a))) := by
  have h := dlmf_table_1_14_2_r8 ha 0
  simp only [zero_mul, Real.cos_zero, ofReal_one, mul_one] at h
  simp_rw [intervalIntegral.integral_ofReal] at h
  have h' := ((Complex.continuous_re.tendsto _).comp h).const_mul (√(π / 2))
  simp only [Function.comp_def, ← ofReal_mul, ofReal_re] at h'
  simp_rw [← mul_assoc, sqrt_pi_div_two_mul_real, one_mul] at h'
  convert h' using 2
  rw [show (0 : ℝ) ^ 2 / (4 * a) - π / 4 = -(π / 4) by ring, Real.cos_neg,
    Real.cos_pi_div_four, ← fresnel_value ha]
  ring

/-- `∫_0^R φ(xt)/√t dt → √(π/2)/√x` from `∫_0^R φ(xt²) dt → √(π/2)/(2√x)` (`x > 0`). -/
theorem tendsto_integral_inv_sqrt_mul {φ : ℝ → ℝ} (hφ : Continuous φ) (hb : ∀ y, |φ y| ≤ 1)
    {x : ℝ} (hx : 0 < x)
    (hF : Tendsto (fun R => ∫ t in (0 : ℝ)..R, φ (x * t ^ 2)) atTop
      (𝓝 (√(π / 2) / (2 * √x)))) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, (√t)⁻¹ * φ (x * t)) atTop (𝓝 (√(π / 2) / √x)) := by
  have h := (hF.comp Real.tendsto_sqrt_atTop).const_mul 2
  rw [show 2 * (√(π / 2) / (2 * √x)) = √(π / 2) / √x by field_simp] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  rw [integral_inv_sqrt_mul_comp (φ := fun t => φ (x * t)) (by fun_prop)
    (fun y => hb _) hR, intervalIntegral.integral_const_mul]
  rfl

/-- **Table 1.14.3, row 2**: `𝓕_s[t^{−1/2}](x) = x^{−1/2}` (`x > 0`), as an improper integral. -/
theorem dlmf_table_1_14_3_r2 {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R => ((√(2 / π) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..R, ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((Real.sin (x * t) : ℝ) : ℂ)) atTop
      (𝓝 ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have h := tendsto_sqrt_two_div_pi_ofReal (tendsto_integral_inv_sqrt_mul Real.continuous_sin
    Real.abs_sin_le_one hx (tendsto_integral_sin_mul_sq hx))
  have hv : ((√(2 / π) : ℝ) : ℂ) * ((√(π / 2) / √x : ℝ) : ℂ) =
      ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← ofReal_mul, rpow_neg_half_eq hx.le, ← mul_div_assoc, mul_comm,
      sqrt_pi_div_two_mul_real, one_div]
  rw [← hv]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hR] at ht
  rw [rpow_neg_half_eq ht.1, ofReal_mul]

theorem integrableOn_rpow_neg_three_halves_mul_sin (x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) * Real.sin (x * t)) (Ioi 0) := by
  have hm : Measurable fun t : ℝ => t ^ (-(3 / 2 : ℝ)) * Real.sin (x * t) := by fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((intervalIntegrable_inv_sqrt zero_le_one).const_mul |x|)
    refine h.mono' hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun t ht => ?_))
    rw [Real.norm_eq_abs, rpow_neg_three_halves_eq ht.1.le, abs_mul,
      abs_of_pos (by have := ht.1; positivity)]
    have hs : |Real.sin (x * t)| ≤ |x| * t := by
      have := Real.abs_sin_le_abs (x := x * t); rwa [abs_mul, abs_of_pos ht.1] at this
    have hst : 0 < √t := Real.sqrt_pos.mpr ht.1
    have ht0 : t ≠ 0 := ht.1.ne'
    calc (t * √t)⁻¹ * |Real.sin (x * t)| ≤ (t * √t)⁻¹ * (|x| * t) :=
          mul_le_mul_of_nonneg_left hs (by have := ht.1; positivity)
      _ = |x| * (√t)⁻¹ := by field_simp
  · refine (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) one_pos).mono'
      hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ fun t ht => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans ht) _)]
    exact mul_le_of_le_one_right (Real.rpow_pos_of_pos (zero_lt_one.trans ht) _).le
      (Real.abs_sin_le_one _)

theorem continuousOn_neg_two_inv_sqrt_mul_sin (x R : ℝ) :
    ContinuousOn (fun t : ℝ => -2 * (√t)⁻¹ * Real.sin (x * t)) (Icc 0 R) := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | htp
  · show Tendsto _ (𝓝[Icc 0 R] 0) (𝓝 (-2 * (√0)⁻¹ * Real.sin (x * 0)))
    simp only [mul_zero, Real.sin_zero]
    have hs : Tendsto (fun t : ℝ => 2 * |x| * √t) (𝓝[Icc 0 R] 0) (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).const_mul (2 * |x|)).mono_left
        (nhdsWithin_le_nhds (s := Icc 0 R))
      simpa using this
    refine squeeze_zero_norm' ?_ hs
    filter_upwards [self_mem_nhdsWithin] with t ht
    rcases ht.1.eq_or_lt with rfl | htp
    · simp
    have hst : 0 < √t := Real.sqrt_pos.mpr htp
    have hsn : |Real.sin (x * t)| ≤ |x| * t := by
      have := Real.abs_sin_le_abs (x := x * t); rwa [abs_mul, abs_of_pos htp] at this
    have hsq : (√t)⁻¹ * t = √t := by
      rw [inv_mul_eq_div, div_eq_iff hst.ne', Real.mul_self_sqrt htp.le]
    simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_two, abs_inv, abs_of_pos hst]
    calc 2 * (√t)⁻¹ * |Real.sin (x * t)| ≤ 2 * (√t)⁻¹ * (|x| * t) :=
          mul_le_mul_of_nonneg_left hsn (by positivity)
      _ = 2 * |x| * ((√t)⁻¹ * t) := by ring
      _ = 2 * |x| * √t := by rw [hsq]
  · have hst : √t ≠ 0 := (Real.sqrt_pos.mpr htp).ne'
    exact ((((Real.continuous_sqrt.continuousAt).inv₀ hst).const_mul (-2)).mul
      (by fun_prop : Continuous fun t => Real.sin (x * t)).continuousAt).continuousWithinAt

/-- **Table 1.14.3, row 3**: `𝓕_s[t^{−3/2}](x) = 2 x^{1/2}` (`x > 0`). -/
theorem dlmf_table_1_14_3_r3 {x : ℝ} (hx : 0 < x) :
    dlmfFourierSin (fun t => ((t ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) x =
      ((2 * x ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  set h : ℝ → ℝ := fun t => t ^ (-(3 / 2 : ℝ)) * Real.sin (x * t)
  have hint := integrableOn_rpow_neg_three_halves_mul_sin x
  set F : ℝ → ℝ := fun t => -2 * (√t)⁻¹ * Real.sin (x * t)
  set F' : ℝ → ℝ := fun t =>
    (t * √t)⁻¹ * Real.sin (x * t) - 2 * x * ((√t)⁻¹ * Real.cos (x * t))
  have hcosI : ∀ R, 0 ≤ R →
      IntervalIntegrable (fun t => (√t)⁻¹ * Real.cos (x * t)) volume 0 R :=
    fun R hR => intervalIntegrable_inv_sqrt_mul (φ := fun t => Real.cos (x * t)) (by fun_prop)
      (fun _ => Real.abs_cos_le_one _) hR
  have hhI : ∀ R, 0 ≤ R → IntervalIntegrable h volume 0 R := fun R hR =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr (hint.mono_set Ioc_subset_Ioi_self)
  have hF'I : ∀ R, 0 ≤ R → IntervalIntegrable F' volume 0 R := fun R hR => by
    refine ((hhI R hR).congr fun t ht => ?_).sub ((hcosI R hR).const_mul (2 * x))
    rw [uIoc_of_le hR] at ht
    simp only [h, rpow_neg_three_halves_eq ht.1.le]
  have hF0 : F 0 = 0 := by simp [F]
  have key : ∀ R, 0 < R → ∫ t in (0 : ℝ)..R, h t =
      F R + 2 * x * ∫ t in (0 : ℝ)..R, (√t)⁻¹ * Real.cos (x * t) := fun R hR => by
    have hF : ∫ t in (0 : ℝ)..R, F' t = F R - F 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le
        (continuousOn_neg_two_inv_sqrt_mul_sin x R) (fun t ht => ?_) (hF'I R hR.le)
      have htp : 0 < t := ht.1
      have hst : √t ≠ 0 := (Real.sqrt_pos.mpr htp).ne'
      have h1 := (((Real.hasDerivAt_sqrt htp.ne').inv hst).const_mul (-2)).mul
        (((hasDerivAt_id t).const_mul x).sin)
      simp only [id, mul_one, Pi.inv_apply] at h1
      refine h1.congr_deriv ?_
      rw [Real.sq_sqrt htp.le]
      simp only [F']
      field_simp
      ring
    rw [hF0, sub_zero] at hF
    rw [← hF, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hF'I R hR.le) ((hcosI R hR.le).const_mul _)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hR.le] at ht
    simp only [h, F', rpow_neg_three_halves_eq ht.1]
    ring
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have hz : Tendsto (fun t : ℝ => 2 * (√t)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul 2
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [F, Real.norm_eq_abs, abs_mul, abs_neg, abs_two, abs_inv,
      abs_of_pos (Real.sqrt_pos.mpr ht)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  have hcos := tendsto_integral_inv_sqrt_mul Real.continuous_cos Real.abs_cos_le_one hx
    (tendsto_integral_cos_mul_sq hx)
  have hlim := hFlim.add (hcos.const_mul (2 * x))
  have hlim' : Tendsto (fun R => ∫ t in (0 : ℝ)..R, h t) atTop
      (𝓝 (0 + 2 * x * (√(π / 2) / √x))) :=
    hlim.congr' (by
      filter_upwards [eventually_gt_atTop 0] with R hR
      rw [key R hR])
  have hI := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hval := tendsto_nhds_unique hI hlim'
  unfold dlmfFourierSin
  have e : ∫ t in Ioi (0 : ℝ), ((t ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((Real.sin (x * t) : ℝ) : ℂ) =
      ((∫ t in Ioi (0 : ℝ), h t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [h, ofReal_mul]
  rw [e, hval, ← ofReal_mul]
  congr 1
  have hsx : √x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  rw [← Real.sqrt_eq_rpow]
  calc √(2 / π) * (0 + 2 * x * (√(π / 2) / √x))
      = 2 * (x / √x) * (√(π / 2) * √(2 / π)) := by ring
    _ = 2 * √x := by
        rw [sqrt_pi_div_two_mul_real, mul_one, Real.div_sqrt]

end Azurite.DLMF
