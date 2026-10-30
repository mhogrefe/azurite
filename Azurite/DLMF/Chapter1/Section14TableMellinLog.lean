/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableMellin

/-!
# DLMF Table 1.14.5: Mellin transforms by integration by parts (rows 5, 7, 8, 9)

* `mellin_by_parts`: `𝓜u(s) = −(1/s) ∫_0^∞ x^s u′(x) dx` when `x^s u(x) → 0` at both ends.
* Row 5 (`dlmf_table_1_14_5_r5`, `ln(1 + ax)`, `|ph a| < π`, `−1 < ℜs < 0`): by parts against
  `mellin_one_div_one_add_mul` at `s + 1`, with `|ln(1 + ax)| ≤ (|a|/c) ln(1 + x)`
  (`norm_log_one_add_mul_le`).
* Row 7 (`_r7`, `ln(1 + x)/x`): row 5 at `a = 1`, `s − 1`.
* Rows 8–9 (`_r8`, `_r9`, `arctan x` and `arccot x = arctan(1/x)`): by parts, with
  `∫_0^∞ x^s/(1 + x²) dx = (π/2) sec(πs/2)` (`x ↦ x²`), and `x ↦ 1/x` for row 9.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Integration by parts -/

/-- `𝓜u(s) = −(1/s) ∫_0^∞ x^s u′(x) dx` when the boundary terms `x^s u(x)` vanish. -/
theorem mellin_by_parts {u u' : ℝ → ℂ} {s : ℂ} (hs : s ≠ 0)
    (hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x) (h1 : MellinConvergent u s)
    (h2 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * u' x) (Ioi 0))
    (h0 : Tendsto (fun x : ℝ => (x : ℂ) ^ s * u x) (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto (fun x : ℝ => (x : ℂ) ^ s * u x) atTop (𝓝 0)) :
    mellin u s = -(1 / s) * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s * u' x := by
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => (y : ℂ) ^ s / s) ((x : ℂ) ^ (s - 1)) x :=
    fun x hx => by
      have := hasDerivAt_ofReal_cpow_const' (ne_of_gt hx) (r := s - 1)
        (by intro h; apply hs; linear_combination h)
      simpa only [sub_add_cancel] using this
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := 0) (b' := 0) hu hv
    (by
      refine IntegrableOn.congr_fun h1 (fun x _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul, Pi.mul_apply]; ring)
    (by
      have : IntegrableOn (fun x : ℝ => 1 / s * ((x : ℂ) ^ s * u' x)) (Ioi 0) := h2.const_mul _
      refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]; ring)
    (by
      have := h0.div_const s
      rw [zero_div] at this
      refine this.congr fun x => ?_
      simp only [Pi.mul_apply]; ring)
    (by
      have := hinf.div_const s
      rw [zero_div] at this
      refine this.congr fun x => ?_
      simp only [Pi.mul_apply]; ring)
  rw [mellin, show (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • u t) =
      ∫ t in Ioi (0 : ℝ), u t * (t : ℂ) ^ (s - 1) from
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [smul_eq_mul, mul_comm], h,
    sub_zero, zero_sub, ← integral_const_mul, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-! ### Real bounds -/

theorem integrableOn_rpow_div_one_add_sq {α : ℝ} (h1 : -1 < α) (h2 : α < 1) :
    IntegrableOn (fun x : ℝ => x ^ α / (1 + x ^ 2)) (Ioi 0) := by
  refine ((integrableOn_rpow_div_one_add_pow (k := 2) h1 (by push_cast; linarith)).const_mul
    2).mono' ((by fun_prop : Measurable fun x : ℝ => x ^ α / (1 + x ^ 2)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun x hx => ?_))
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
    abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
  have hp := Real.rpow_pos_of_pos hx0 α
  have : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith [sq_nonneg (x - 1)]
  calc x ^ α = 2 * (x ^ α / (1 + x) ^ 2) * ((1 + x) ^ 2 / 2) := by field_simp
    _ ≤ 2 * (x ^ α / (1 + x) ^ 2) * (1 + x ^ 2) := by gcongr; linarith

theorem log_one_add_le_rpow {σ x : ℝ} (hσ : σ < 0) (hx : 1 ≤ x) :
    Real.log (1 + x) ≤ 2 ^ (-σ / 2) / (-σ / 2) * x ^ (-σ / 2) := by
  have hδ : 0 < -σ / 2 := by linarith
  have h := Real.log_le_rpow_div (x := 1 + x) (by linarith) hδ
  calc Real.log (1 + x) ≤ (1 + x) ^ (-σ / 2) / (-σ / 2) := h
    _ ≤ (2 * x) ^ (-σ / 2) / (-σ / 2) := by gcongr; linarith
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith)]; ring

theorem integrableOn_rpow_mul_log_one_add {σ : ℝ} (h1 : -1 < σ) (h2 : σ < 0) :
    IntegrableOn (fun x : ℝ => x ^ (σ - 1) * Real.log (1 + x)) (Ioi 0) := by
  have hm : Measurable fun x : ℝ => x ^ (σ - 1) * Real.log (1 + x) := by fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) h1)
    refine h.mono' hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun x hx => ?_))
    have hx0 : 0 < x := hx.1
    have hl0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
    have hl : Real.log (1 + x) ≤ x := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc x ^ (σ - 1) * Real.log (1 + x) ≤ x ^ (σ - 1) * x :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = x ^ σ := by rw [← Real.rpow_add_one hx0.ne', sub_add_cancel]
  · refine ((integrableOn_Ioi_rpow_of_lt (by linarith : σ - 1 + -σ / 2 < -1) one_pos).const_mul
      (2 ^ (-σ / 2) / (-σ / 2))).mono' hm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := by linarith
    have hl0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_add hx0]
    calc x ^ (σ - 1) * Real.log (1 + x) ≤ x ^ (σ - 1) * (2 ^ (-σ / 2) / (-σ / 2) * x ^ (-σ / 2)) :=
          mul_le_mul_of_nonneg_left (log_one_add_le_rpow h2 hx1.le) (by positivity)
      _ = _ := by ring

theorem tendsto_rpow_mul_log_one_add_atTop {σ : ℝ} (h2 : σ < 0) :
    Tendsto (fun x : ℝ => x ^ σ * Real.log (1 + x)) atTop (𝓝 0) := by
  have hz := (tendsto_rpow_neg_atTop (by linarith : 0 < -σ / 2)).const_mul (2 ^ (-σ / 2) / (-σ / 2))
  rw [mul_zero] at hz
  refine squeeze_zero' ?_ ?_ hz
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    calc x ^ σ * Real.log (1 + x) ≤ x ^ σ * (2 ^ (-σ / 2) / (-σ / 2) * x ^ (-σ / 2)) :=
          mul_le_mul_of_nonneg_left (log_one_add_le_rpow h2 hx) (by positivity)
      _ = 2 ^ (-σ / 2) / (-σ / 2) * (x ^ σ * x ^ (-σ / 2)) := by ring
      _ = 2 ^ (-σ / 2) / (-σ / 2) * x ^ (-(-σ / 2)) := by
          rw [← Real.rpow_add hx0]; ring_nf

theorem tendsto_rpow_add_one_nhdsGT {σ : ℝ} (h1 : -1 < σ) :
    Tendsto (fun x : ℝ => x ^ (σ + 1)) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.continuousAt_rpow_const 0 (σ + 1) (Or.inr (by linarith))).tendsto
  rw [Real.zero_rpow (by linarith)] at this
  exact this.mono_left nhdsWithin_le_nhds

/-! ### Rows 8–9: `arctan x`, `arccot x` -/

theorem norm_cpow_mul_le {s : ℂ} {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ‖(x : ℂ) ^ s * z‖ = x ^ s.re * ‖z‖ := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]

/-- `∫_0^∞ x^s/(1 + x²) dx = (π/2) sec(πs/2)` for `−1 < ℜs < 1`. -/
theorem integral_cpow_div_one_add_sq {s : ℂ} (h1 : -1 < s.re) (h2 : s.re < 1) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s * (1 / (1 + (x : ℂ) ^ 2)) =
      π / 2 / Complex.cos (π * s / 2) := by
  have hm := mellin_comp_rpow (fun y : ℝ => 1 / (1 + (y : ℂ))) (s + 1) 2
  rw [mellin] at hm
  have e : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s * (1 / (1 + (x : ℂ) ^ 2))) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s + 1 - 1) • (1 / (1 + ((t ^ (2 : ℝ) : ℝ) : ℂ))) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by
      rw [add_sub_cancel_right, smul_eq_mul, Real.rpow_two]; push_cast; ring
  rw [e, hm, mellin_one_div_one_add (by simp; linarith) (by simp; linarith)]
  rw [abs_two, real_smul, show π * ((s + 1) / ((2 : ℝ) : ℂ)) = π * s / 2 + π / 2 by push_cast; ring,
    Complex.sin_add_pi_div_two]
  push_cast
  ring

theorem abs_arctan_le_min (x : ℝ) (hx : 0 ≤ x) : |Real.arctan x| ≤ min x (π / 2) := by
  refine le_min ?_ (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan x).le,
    (Real.arctan_lt_pi_div_two x).le⟩)
  have := Real.abs_arctan_le_abs (x := x)
  rwa [abs_of_nonneg hx] at this

/-- **Table 1.14.5, row 8**: `𝓜[arctan x](s) = −π sec(sπ/2)/(2s)` (`−1 < ℜs < 0`). -/
theorem dlmf_table_1_14_5_r8 {s : ℂ} (h1 : -1 < s.re) (h2 : s.re < 0) :
    mellin (fun x : ℝ => ((Real.arctan x : ℝ) : ℂ)) s =
      -(π / (2 * s * Complex.cos (s * π / 2))) := by
  have hs : s ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => ((Real.arctan x : ℝ) : ℂ))
      (1 / (1 + (x : ℂ) ^ 2)) x := fun x _ => by
    have := (Real.hasDerivAt_arctan x).ofReal_comp
    refine this.congr_deriv ?_
    push_cast; ring
  have h1' : MellinConvergent (fun x : ℝ => ((Real.arctan x : ℝ) : ℂ)) s := by
    have hb : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * min x (π / 2)) (Ioi 0) := by
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
      refine IntegrableOn.union ?_ ?_
      · have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
          (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) h1)
        refine h.congr_fun (fun x hx => ?_) measurableSet_Ioc
        rw [min_eq_left (by linarith [hx.2, Real.two_le_pi]),
          ← Real.rpow_add_one hx.1.ne', sub_add_cancel]
      · refine ((integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 1 < -1) one_pos).mul_const
          (π / 2)).mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).mpr
            (ae_of_all _ fun x hx => ?_))
        have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
          abs_of_pos (lt_min hx0 (by positivity))]
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_pos_of_pos hx0 _).le
    refine hb.mono' (by
        refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
        exact (((continuous_ofReal.continuousAt).cpow continuousAt_const
          (ofReal_mem_slitPlane.mpr hx)).smul (by fun_prop)).continuousWithinAt)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := hx
    rw [smul_eq_mul, norm_cpow_mul_le hx0, sub_re, one_re, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_arctan_le_min x hx0.le) (Real.rpow_pos_of_pos hx0 _).le
  have h2' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * (1 / (1 + (x : ℂ) ^ 2))) (Ioi 0) := by
    refine (integrableOn_rpow_div_one_add_sq h1 (by linarith)).mono' (by
        refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
        refine (((continuous_ofReal.continuousAt).cpow continuousAt_const
          (ofReal_mem_slitPlane.mpr hx)).mul (continuousAt_const.div (by fun_prop) ?_)
          ).continuousWithinAt
        exact_mod_cast (by positivity : (1 + x ^ 2 : ℝ) ≠ 0))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_cpow_mul_le hx0, show (1 + (x : ℂ) ^ 2) = ((1 + x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [mul_one_div]
  have hbound : ∀ x : ℝ, 0 < x → ‖(x : ℂ) ^ s * ((Real.arctan x : ℝ) : ℂ)‖ ≤
      x ^ s.re * min x (π / 2) := fun x hx => by
    rw [norm_cpow_mul_le hx, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_arctan_le_min x hx.le) (Real.rpow_pos_of_pos hx _).le
  have h0 : Tendsto (fun x : ℝ => (x : ℂ) ^ s * ((Real.arctan x : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_rpow_add_one_nhdsGT h1)
    filter_upwards [self_mem_nhdsWithin] with x hx
    refine (hbound x hx).trans ?_
    rw [Real.rpow_add_one (ne_of_gt hx)]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_pos_of_pos hx _).le
  have hinf : Tendsto (fun x : ℝ => (x : ℂ) ^ s * ((Real.arctan x : ℝ) : ℂ)) atTop (𝓝 0) := by
    have hz := (tendsto_rpow_neg_atTop (by linarith : 0 < -s.re)).mul_const (π / 2)
    rw [zero_mul, neg_neg] at hz
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact (hbound x hx).trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
      (Real.rpow_pos_of_pos hx _).le)
  rw [mellin_by_parts hs hu h1' h2' h0 hinf, integral_cpow_div_one_add_sq h1 (by linarith)]
  have hc : Complex.cos (π * s / 2) = Complex.cos (s * π / 2) := by ring_nf
  rw [hc]
  field_simp

/-- **Table 1.14.5, row 9**: `𝓜[arccot x](s) = π sec(sπ/2)/(2s)` (`0 < ℜs < 1`), with
`arccot x = arctan(1/x)` (DLMF 4.23.9). -/
theorem dlmf_table_1_14_5_r9 {s : ℂ} (h1 : 0 < s.re) (h2 : s.re < 1) :
    mellin (fun x : ℝ => ((Real.arctan x⁻¹ : ℝ) : ℂ)) s =
      π / (2 * s * Complex.cos (s * π / 2)) := by
  rw [mellin_comp_inv (fun x : ℝ => ((Real.arctan x : ℝ) : ℂ)),
    dlmf_table_1_14_5_r8 (by simp; linarith) (by simp; linarith)]
  have : Complex.cos (-s * π / 2) = Complex.cos (s * π / 2) := by
    rw [show -s * π / 2 = -(s * π / 2) by ring, Complex.cos_neg]
  rw [this]
  field_simp

/-! ### Rows 5 and 7: `ln(1 + ax)`, `ln(1 + x)/x` -/

theorem one_add_mul_mem_slitPlane {a : ℂ} (ha : a ∈ slitPlane) {x : ℝ} (hx : 0 ≤ x) :
    1 + a * x ∈ slitPlane := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rw [mem_slitPlane_iff] at ha ⊢
  rcases ha with h | h
  · left; simp only [add_re, one_re, re_mul_ofReal]; positivity
  · right; simp only [add_im, one_im, im_mul_ofReal, zero_add]; exact mul_ne_zero h hx.ne'

theorem hasDerivAt_log_one_add_mul {a : ℂ} (ha : a ∈ slitPlane) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun x : ℝ => Complex.log (1 + a * x)) (a / (1 + a * x)) x := by
  have h := (((hasDerivAt_id x).ofReal_comp.const_mul a).const_add 1).clog_real
    (one_add_mul_mem_slitPlane ha hx)
  simp only [id, ofReal_one, mul_one] at h
  exact h

/-- `|ln(1 + ax)| ≤ (|a|/c) ln(1 + x)` on `x ≥ 0`, when `|1 + at| ≥ c(1 + t)` there. -/
theorem norm_log_one_add_mul_le {a : ℂ} (ha : a ∈ slitPlane) {c : ℝ} (hc : 0 < c)
    (h : ∀ x : ℝ, 0 ≤ x → c * (1 + x) ≤ ‖1 + a * x‖) {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.log (1 + a * x)‖ ≤ ‖a‖ / c * Real.log (1 + x) := by
  have hne : ∀ t : ℝ, 0 ≤ t → 1 + a * t ≠ 0 := fun t ht e => by
    have := h t ht; rw [e, norm_zero] at this; nlinarith
  have hd : ∀ t ∈ uIcc (0 : ℝ) x, HasDerivAt (fun x : ℝ => Complex.log (1 + a * x))
      (a / (1 + a * t)) t := fun t ht => by
    rw [uIcc_of_le hx] at ht; exact hasDerivAt_log_one_add_mul ha ht.1
  have hcont : ContinuousOn (fun t : ℝ => a / (1 + a * t)) (uIcc 0 x) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => hne t ?_
    rw [uIcc_of_le hx] at ht; exact ht.1
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  simp only [ofReal_zero, mul_zero, add_zero, Complex.log_one, sub_zero] at hI
  rw [← hI]
  have hb : IntervalIntegrable (fun t : ℝ => ‖a‖ / c * (1 + t)⁻¹) volume 0 x :=
    (ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun t ht => by
      rw [uIcc_of_le hx] at ht; linarith [ht.1])).intervalIntegrable
  refine (intervalIntegral.norm_integral_le_of_norm_le hx (ae_of_all _ fun t ht => ?_) hb).trans
    (le_of_eq ?_)
  · rw [norm_div]
    have h1 := h t ht.1.le
    have h1t : (1 : ℝ) + t ≠ 0 := by linarith [ht.1]
    rw [div_le_iff₀ (by nlinarith [ht.1] : 0 < ‖1 + a * t‖)]
    calc ‖a‖ = ‖a‖ / c * (1 + t)⁻¹ * (c * (1 + t)) := by
          field_simp
      _ ≤ ‖a‖ / c * (1 + t)⁻¹ * ‖1 + a * t‖ :=
          mul_le_mul_of_nonneg_left h1 (by have := ht.1; positivity)
  · rw [intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) (1 : ℝ) (a := 0) (b := x)
    simp only [add_zero] at this
    rw [this, integral_inv_of_pos one_pos (by linarith), div_one]

theorem mellinConvergent_log_one_add_mul {a : ℂ} (ha : a ∈ slitPlane) {s : ℂ} (h1 : -1 < s.re)
    (h2 : s.re < 0) : MellinConvergent (fun x : ℝ => Complex.log (1 + a * x)) s := by
  obtain ⟨c, hc, hcb⟩ := exists_norm_one_add_mul_ge ha
  have hlog := fun x (hx : (0 : ℝ) ≤ x) => norm_log_one_add_mul_le ha hc hcb hx
  have hcontlog : ∀ x : ℝ, 0 ≤ x → ContinuousAt (fun x : ℝ => Complex.log (1 + a * x)) x :=
    fun x hx => (hasDerivAt_log_one_add_mul ha hx).continuousAt
  refine ((integrableOn_rpow_mul_log_one_add h1 h2).const_mul (‖a‖ / c)).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    exact (((continuous_ofReal.continuousAt).cpow continuousAt_const
      (ofReal_mem_slitPlane.mpr hx)).smul (hcontlog x (le_of_lt hx))).continuousWithinAt
  · have hx0 : (0 : ℝ) < x := hx
    rw [smul_eq_mul, norm_cpow_mul_le hx0, sub_re, one_re]
    calc x ^ (s.re - 1) * ‖Complex.log (1 + a * x)‖ ≤
        x ^ (s.re - 1) * (‖a‖ / c * Real.log (1 + x)) :=
          mul_le_mul_of_nonneg_left (hlog x hx0.le) (Real.rpow_pos_of_pos hx0 _).le
      _ = _ := by ring

theorem sin_pi_mul_ne_zero_of {s : ℂ} {m : ℤ} (h1 : (m : ℝ) < s.re) (h2 : s.re < m + 1) :
    Complex.sin (π * s) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : s = k := mul_left_cancel₀ hπ (by rw [hk]; ring)
  have hre : s.re = k := by rw [hs]; simp
  rw [hre] at h1 h2
  have : m < k := by exact_mod_cast h1
  have : k < m + 1 := by exact_mod_cast h2
  omega

/-- **Table 1.14.5, row 5**: `𝓜[ln(1 + ax)](s) = π csc(sπ)/(s a^s)` (`|ph a| < π`,
`−1 < ℜs < 0`; principal branches). -/
theorem dlmf_table_1_14_5_r5 {a : ℂ} (ha : a ∈ slitPlane) {s : ℂ} (h1 : -1 < s.re)
    (h2 : s.re < 0) :
    mellin (fun x : ℝ => Complex.log (1 + a * x)) s = π / Complex.sin (s * π) / (s * a ^ s) := by
  have hs : s ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have ha0 := slitPlane_ne_zero ha
  obtain ⟨c, hc, hcb⟩ := exists_norm_one_add_mul_ge ha
  have hne : ∀ t : ℝ, 0 ≤ t → 1 + a * t ≠ 0 := fun t ht e => by
    have := hcb t ht; rw [e, norm_zero] at this; nlinarith
  have hlog := fun x (hx : (0 : ℝ) ≤ x) => norm_log_one_add_mul_le ha hc hcb hx
  have hcontlog : ∀ x : ℝ, 0 ≤ x → ContinuousAt (fun x : ℝ => Complex.log (1 + a * x)) x :=
    fun x hx => (hasDerivAt_log_one_add_mul ha hx).continuousAt
  have hu := fun x (hx : x ∈ Ioi (0 : ℝ)) => hasDerivAt_log_one_add_mul ha (le_of_lt hx)
  have h1' := mellinConvergent_log_one_add_mul ha h1 h2
  have h2' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * (a / (1 + a * x))) (Ioi 0) := by
    refine ((integrableOn_rpow_div_one_add_pow (k := 1) h1 (by push_cast; linarith)).const_mul
      (‖a‖ / c)).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      exact (((continuous_ofReal.continuousAt).cpow continuousAt_const
        (ofReal_mem_slitPlane.mpr hx)).mul (continuousAt_const.div (by fun_prop)
          (hne x (le_of_lt hx)))).continuousWithinAt
    · have hx0 : (0 : ℝ) < x := hx
      have hb := hcb x hx0.le
      rw [norm_cpow_mul_le hx0, norm_div, pow_one]
      calc x ^ s.re * (‖a‖ / ‖1 + a * x‖) ≤ x ^ s.re * (‖a‖ / (c * (1 + x))) := by
            gcongr
        _ = _ := by field_simp
  have hbound : ∀ x : ℝ, 0 < x → ‖(x : ℂ) ^ s * Complex.log (1 + a * x)‖ ≤
      ‖a‖ / c * (x ^ s.re * Real.log (1 + x)) := fun x hx => by
    rw [norm_cpow_mul_le hx]
    calc x ^ s.re * ‖Complex.log (1 + a * x)‖ ≤ x ^ s.re * (‖a‖ / c * Real.log (1 + x)) :=
          mul_le_mul_of_nonneg_left (hlog x hx.le) (Real.rpow_pos_of_pos hx _).le
      _ = _ := by ring
  have h0 : Tendsto (fun x : ℝ => (x : ℂ) ^ s * Complex.log (1 + a * x)) (𝓝[>] 0) (𝓝 0) := by
    have hz := (tendsto_rpow_add_one_nhdsGT h1).const_mul (‖a‖ / c)
    rw [mul_zero] at hz
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [self_mem_nhdsWithin] with x hx
    refine (hbound x hx).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [Real.rpow_add_one (ne_of_gt hx)]
    have hx1 : (0 : ℝ) < 1 + x := by linarith [show (0 : ℝ) < x from hx]
    have hl := Real.log_le_sub_one_of_pos hx1
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hx _).le
  have hinf : Tendsto (fun x : ℝ => (x : ℂ) ^ s * Complex.log (1 + a * x)) atTop (𝓝 0) := by
    have hz := (tendsto_rpow_mul_log_one_add_atTop h2).const_mul (‖a‖ / c)
    rw [mul_zero] at hz
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact hbound x hx
  have hM : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s * (a / (1 + a * x)) =
      a * mellin (fun x : ℝ => 1 / (1 + a * x)) (s + 1) := by
    rw [mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [add_sub_cancel_right, smul_eq_mul]; ring
  rw [mellin_by_parts hs hu h1' h2' h0 hinf, hM,
    mellin_one_div_one_add_mul ha (by simp; linarith) (by simp; linarith),
    show -(s + 1) = -s + -1 by ring, cpow_add _ _ ha0, cpow_neg_one,
    show (π : ℂ) * (s + 1) = π * s + π by ring, Complex.sin_add_pi, cpow_neg,
    mul_comm s (π : ℂ)]
  have hsin : Complex.sin (π * s) ≠ 0 := sin_pi_mul_ne_zero_of (m := -1) (by simpa using h1)
    (by simpa using h2)
  have has : a ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  field_simp

/-- **Table 1.14.5, row 7**: `𝓜[ln(1 + x)/x](s) = π csc(sπ)/(1 − s)` (`0 < ℜs < 1`). -/
theorem dlmf_table_1_14_5_r7 {s : ℂ} (h1 : 0 < s.re) (h2 : s.re < 1) :
    mellin (fun x : ℝ => Complex.log (1 + x) / x) s = π / Complex.sin (s * π) / (1 - s) := by
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have e : mellin (fun x : ℝ => Complex.log (1 + x) / x) s =
      mellin (fun x : ℝ => Complex.log (1 + 1 * x)) (s - 1) := by
    rw [mellin, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    simp only [smul_eq_mul, one_mul]
    conv_rhs => rw [cpow_sub _ _ hx0, cpow_one]
    field_simp
  rw [e, dlmf_table_1_14_5_r5 (by simp) (by simp; linarith) (by simp; linarith), one_cpow,
    mul_one, show (s - 1) * π = s * π - π by ring, Complex.sin_sub_pi]
  have hsin : Complex.sin (s * π) ≠ 0 := by
    rw [mul_comm]; exact sin_pi_mul_ne_zero_of (m := 0) (by simpa using h1) (by simpa using h2)
  have h1s : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  field_simp
  ring

end Azurite.DLMF
