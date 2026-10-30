/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Mellin
import Azurite.DLMF.Chapter1.Section14TableLaplace
import Azurite.DLMF.Chapter1.Section10Continuation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected

/-!
# DLMF Table 1.14.5: Mellin transforms

Rows of <https://dlmf.nist.gov/1.14.T5> for Mathlib's `mellin f s = ∫_0^∞ x^{s−1} f(x) dx`.
Rows 5, 7, 8, 9: `Section14TableMellinLog.lean`; rows 3, 6: `Section14TableMellinPV.lean`.

* Rows 1–2 (`dlmf_table_1_14_5_r1`, `_r2`): `x = e^{−u}` turns them into the Laplace transforms of
  `1` and `t` (Table 1.14.4), and `x ↦ x/a` scales (`mellin_comp_div`). Row 2 holds for `ℜs > 0`;
  DLMF states `ℜs > 1`.
* `mellin_one_div_one_add`: `∫_0^∞ x^{s−1}/(1 + x) dx = Γ(s)Γ(1 − s) = π/sin(πs)` (`0 < ℜs < 1`), by
  Fubini with `1/(1 + x) = ∫_0^∞ e^{−(1+x)t} dt` and the Gamma integral.
* `mellin_one_div_one_add_mul`: `∫_0^∞ x^{s−1}/(1 + ax) dx = a^{−s} π/sin(πs)` for `|ph a| < π`:
  scaling for `a > 0`, then continuation in `a` on the slit plane
  (`differentiableOn_mellin_one_div_one_add_mul`, by dominated differentiation with
  `|1 + ax| ≥ c(1 + x)` locally uniformly; `dlmf_1_10_ii_functional`).
* Rows 4, 10, 11 (`_r4`, `_r10`, `_r11`): `a = 1` and `a = e^{±iθ}`, using
  `1 + 2x cos θ + x² = (1 + e^{iθ}x)(1 + e^{−iθ}x)`.
-/

open Set Filter Topology MeasureTheory Complex Metric
open scoped Real

namespace Azurite.DLMF

/-! ### Rows 1–2: truncated powers and logarithms -/

theorem ofReal_inv_cpow_neg {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((a⁻¹ : ℝ) : ℂ) ^ (-s) = (a : ℂ) ^ s := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg ha.le]; exact Real.pi_pos.ne),
    cpow_neg, inv_inv]

/-- `𝓜[g(x/a)](s) = a^s 𝓜g(s)` for `a > 0`. -/
theorem mellin_comp_div {g : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (s : ℂ) :
    mellin (fun x => g (a⁻¹ * x)) s = (a : ℂ) ^ s * mellin g s := by
  rw [mellin_comp_mul_left g s (inv_pos.mpr ha), ofReal_inv_cpow_neg ha, smul_eq_mul]

theorem mellin_eq_laplace_of_lt_one {g : ℝ → ℂ} {h : ℝ → ℂ}
    (hg : ∀ x, 0 < x → g x = if x < 1 then h (-Real.log x) else 0) (s : ℂ) :
    mellin g s = laplace h s := by
  rw [mellin_eq_integral_exp, laplace, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [indicator, mem_Ioi]
  rw [hg _ (Real.exp_pos _), Real.log_exp, neg_neg]
  by_cases hu : 0 < u
  · have h1 : rexp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    simp only [h1, hu, ite_true]
  · have h1 : ¬ rexp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    simp only [h1, hu, ite_false, mul_zero]

theorem mellin_eq_zero_of_eqOn {g : ℝ → ℂ} (hg : ∀ x, 0 < x → g x = 0) (s : ℂ) :
    mellin g s = 0 := by
  rw [mellin]
  refine (setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_).trans (integral_zero _ _)
  rw [hg x hx, smul_zero]

/-- **Table 1.14.5, row 1**: `𝓜[1_{x<a}](s) = a^s/s` (`a ≥ 0`, `ℜs > 0`). -/
theorem dlmf_table_1_14_5_r1 {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => if x < a then (1 : ℂ) else 0) s = (a : ℂ) ^ s / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  rcases ha.eq_or_lt with rfl | ha
  · rw [mellin_eq_zero_of_eqOn (fun x hx => by simp only [show ¬ x < 0 by linarith, ite_false]),
      ofReal_zero, zero_cpow hs0,
      zero_div]
  have e : (fun x : ℝ => if x < a then (1 : ℂ) else 0) =
      fun x => (fun y : ℝ => if y < 1 then (1 : ℂ) else 0) (a⁻¹ * x) := by
    funext x
    have hiff : a⁻¹ * x < 1 ↔ x < a := by rw [inv_mul_lt_iff₀ ha, mul_one]
    by_cases hx : x < a
    · simp only [hx, hiff.mpr hx, ite_true]
    · simp only [hx, mt hiff.mp hx, ite_false]
  rw [e, mellin_comp_div (g := fun y : ℝ => if y < 1 then (1 : ℂ) else 0) ha,
    mellin_eq_laplace_of_lt_one (h := fun _ => 1) (fun x _ => rfl), dlmf_table_1_14_4_r1 hs]
  ring

/-- **Table 1.14.5, row 2**: `𝓜[ln(a/x) 1_{x<a}](s) = a^s/s²` (`a ≥ 0`; DLMF states `ℜs > 1`, and
`ℜs > 0` suffices). -/
theorem dlmf_table_1_14_5_r2 {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => if x < a then ((Real.log (a / x) : ℝ) : ℂ) else 0) s =
      (a : ℂ) ^ s / s ^ 2 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  rcases ha.eq_or_lt with rfl | ha
  · rw [mellin_eq_zero_of_eqOn (fun x hx => by simp only [show ¬ x < 0 by linarith, ite_false]),
      ofReal_zero, zero_cpow hs0,
      zero_div]
  have e : (fun x : ℝ => if x < a then ((Real.log (a / x) : ℝ) : ℂ) else 0) =
      fun x => (fun y : ℝ => if y < 1 then ((-Real.log y : ℝ) : ℂ) else 0) (a⁻¹ * x) := by
    funext x
    have hiff : a⁻¹ * x < 1 ↔ x < a := by rw [inv_mul_lt_iff₀ ha, mul_one]
    by_cases hx : x < a
    · simp only [hx, hiff.mpr hx, ite_true]
      rw [← Real.log_inv, mul_inv, inv_inv, ← div_eq_mul_inv]
    · simp only [hx, mt hiff.mp hx, ite_false]
  have h2 := dlmf_table_1_14_4_r2 hs 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h2
  rw [e, mellin_comp_div (g := fun y : ℝ => if y < 1 then ((-Real.log y : ℝ) : ℂ) else 0) ha,
    mellin_eq_laplace_of_lt_one (h := fun t => (t : ℂ)) (fun x _ => by push_cast; rfl), h2]
  ring

/-! ### `∫_0^∞ x^{s−1}/(1 + x) dx = Γ(s)Γ(1 − s)` -/

theorem integrableOn_rpow_div_one_add_pow {α : ℝ} {k : ℕ} (h1 : -1 < α) (h2 : α < k - 1) :
    IntegrableOn (fun x : ℝ => x ^ α / (1 + x) ^ k) (Ioi 0) := by
  have hm : Measurable fun x : ℝ => x ^ α / (1 + x) ^ k := by fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) h1)
    refine h.mono' hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun x hx => ?_))
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
      abs_of_pos (by positivity)]
    exact div_le_self (Real.rpow_pos_of_pos hx0 _).le (one_le_pow₀ (by linarith))
  · refine (integrableOn_Ioi_rpow_of_lt (by linarith : α - k < -1) one_pos).mono'
      hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ fun x hx => ?_))
    have hx0 : 0 < x := zero_lt_one.trans hx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
      abs_of_pos (by positivity), Real.rpow_sub hx0, Real.rpow_natCast]
    exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hx0 _).le (by positivity)
      (pow_le_pow_left₀ hx0.le (by linarith) k)

/-- `∫_0^∞ x^{s−1}/(1 + x) dx = Γ(s)Γ(1 − s) = π/sin(πs)` for `0 < ℜs < 1` (Fubini with
`1/(1 + x) = ∫_0^∞ e^{−(1+x)t} dt`). -/
theorem mellin_one_div_one_add {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x : ℝ => 1 / (1 + (x : ℂ))) s = π / Complex.sin (π * s) := by
  rw [← Complex.Gamma_mul_Gamma_one_sub]
  set μ := volume.restrict (Ioi (0 : ℝ))
  set H : ℝ → ℝ → ℂ := fun x t => (x : ℂ) ^ (s - 1) * ((Real.exp (-((1 + x) * t)) : ℝ) : ℂ)
  have hHc : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ Ioi 0) := by
    refine ContinuousOn.mul (fun p hp => ?_) (by fun_prop)
    exact ((continuous_ofReal.comp continuous_fst).continuousAt.cpow continuousAt_const
      (ofReal_mem_slitPlane.mpr hp.1)).continuousWithinAt
  have hHm : AEStronglyMeasurable (Function.uncurry H) (μ.prod μ) := by
    rw [Measure.prod_restrict]
    exact hHc.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  have hnorm : ∀ x t : ℝ, 0 < x → ‖H x t‖ = Real.exp (-t) * (x ^ (s.re - 1) * Real.exp (-(t * x)))
      := fun x t hx => by
    simp only [H, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
    rw [show -((1 + x) * t) = -t + -(t * x) by ring, Real.exp_add]
    ring
  have hinner_int : ∀ t ∈ Ioi (0 : ℝ),
      Integrable (fun x => ‖H x t‖) μ := fun t ht => by
    have := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (by linarith)
      one_pos ht).const_mul (Real.exp (-t))
    refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Ioi
    rw [hnorm x t hx, Real.rpow_one, neg_mul]
  have hinner_val : ∀ t ∈ Ioi (0 : ℝ), ∫ x, ‖H x t‖ ∂μ =
      Real.Gamma s.re * (Real.exp (-t) * t ^ (-s.re)) := fun t ht => by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hnorm x t hx), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 ht, one_div, Real.inv_rpow (le_of_lt ht),
      ← Real.rpow_neg (le_of_lt ht)]
    ring
  have hHx : ∀ t, AEStronglyMeasurable (fun x => H x t) μ := fun t =>
    (ContinuousOn.mul (fun x hx => ((continuous_ofReal.continuousAt).cpow continuousAt_const
      (ofReal_mem_slitPlane.mpr hx)).continuousWithinAt) (by fun_prop)).aestronglyMeasurable
      measurableSet_Ioi
  have hHi : Integrable (Function.uncurry H) (μ.prod μ) := by
    refine (integrable_prod_iff' hHm).mpr ⟨?_, ?_⟩
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht =>
        (hinner_int t ht).mono' (hHx t) (ae_of_all _ fun x => le_rfl))
    · have := ((integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -s.re) (b := 1)
        (by linarith) one_pos one_pos).const_mul (Real.Gamma s.re))
      refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
      simp only [Function.uncurry_apply_pair]
      rw [hinner_val t ht, Real.rpow_one, neg_mul, one_mul]
      ring
  have hx_inner : ∀ x ∈ Ioi (0 : ℝ), ∫ t, H x t ∂μ = (x : ℂ) ^ (s - 1) • (1 / (1 + (x : ℂ))) :=
    fun x hx => by
      have hx0 : 0 < 1 + x := by linarith [show (0 : ℝ) < x from hx]
      simp only [μ, H]
      rw [integral_const_mul, integral_complex_ofReal]
      have := integral_exp_neg_mul_Ioi_zero hx0
      simp only [neg_mul] at this
      rw [this, smul_eq_mul]
      push_cast; ring
  have ht_inner : ∀ t ∈ Ioi (0 : ℝ), ∫ x, H x t ∂μ =
      Gamma s * ((t : ℂ) ^ ((1 - s) - 1) * cexp (-((1 : ℝ) * t))) := fun t ht => by
    have ht0 : (0 : ℝ) < t := ht
    have e : ∀ x : ℝ, H x t = cexp (-((1 : ℝ) * t)) * ((x : ℂ) ^ (s - 1) * cexp (-(t * x))) :=
      fun x => by
        simp only [H]
        rw [ofReal_exp, ← mul_assoc, mul_comm (cexp _), mul_assoc, ← Complex.exp_add]
        push_cast; ring_nf
    simp only [μ]
    simp_rw [e]
    rw [integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi hs0 ht0, one_div,
      inv_cpow _ _ (by rw [arg_ofReal_of_nonneg ht0.le]; exact Real.pi_pos.ne), ← cpow_neg,
      show (1 - s) - 1 = -s by ring]
    ring
  rw [mellin, ← setIntegral_congr_fun measurableSet_Ioi hx_inner, integral_integral_swap hHi,
    setIntegral_congr_fun measurableSet_Ioi ht_inner, integral_const_mul,
    integral_cpow_mul_exp_neg_mul_Ioi (by simpa using hs1) one_pos]
  simp

/-! ### `∫_0^∞ x^{s−1}/(1 + ax) dx = a^{−s} π/sin(πs)` for `a` off the negative axis -/

theorem mellin_one_div_one_add_mul_pos {a : ℝ} (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    mellin (fun x : ℝ => 1 / (1 + (a : ℂ) * x)) s = (a : ℂ) ^ (-s) * (π / Complex.sin (π * s)) := by
  have h := mellin_comp_mul_left (fun y : ℝ => 1 / (1 + (y : ℂ))) s ha
  simp only [ofReal_mul] at h
  rw [h, mellin_one_div_one_add hs0 hs1, smul_eq_mul]

/-- For `w` off the closed negative axis, `|1 + wx| ≥ c(1 + x)` on `x ≥ 0`. -/
theorem exists_norm_one_add_mul_ge {w : ℂ} (hw : w ∈ slitPlane) :
    ∃ c > 0, ∀ x : ℝ, 0 ≤ x → c * (1 + x) ≤ ‖1 + w * x‖ := by
  rcases lt_or_ge 0 w.re with hre | hre
  · refine ⟨min 1 w.re, lt_min one_pos hre, fun x hx => ?_⟩
    have h := Complex.re_le_norm (1 + w * x)
    simp only [add_re, one_re, re_mul_ofReal] at h
    have h1 := min_le_left 1 w.re
    have h2 := min_le_right 1 w.re
    nlinarith
  · have him : w.im ≠ 0 := by
      rw [mem_slitPlane_iff] at hw; rcases hw with h | h; · linarith
      · exact h
    set m := |w.im|
    set K := ‖w‖
    have hm : 0 < m := abs_pos.mpr him
    have hmK : m ≤ K := abs_im_le_norm w
    refine ⟨m / (2 * K + 2 * m + 1), by positivity, fun x hx => ?_⟩
    have hden : 0 < 2 * K + 2 * m + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have hn1 : 1 - K * x ≤ ‖1 + w * x‖ := by
      have := norm_add_le (1 + w * (x : ℂ)) (-(w * x))
      rw [add_neg_cancel_right, norm_one, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hx] at this
      linarith
    have hn2 : m * x ≤ ‖1 + w * x‖ := by
      have := abs_im_le_norm (1 + w * (x : ℂ))
      simp only [add_im, one_im, im_mul_ofReal, zero_add, abs_mul, abs_of_nonneg hx] at this
      linarith
    rcases le_or_gt (K * x) (1 / 2) with h | h
    · nlinarith
    · nlinarith

theorem exists_ball_norm_one_add_mul_ge {w : ℂ} (hw : w ∈ slitPlane) :
    ∃ c > 0, ∀ a ∈ ball w c, ∀ x : ℝ, 0 ≤ x → c * (1 + x) ≤ ‖1 + a * x‖ := by
  obtain ⟨c, hc, h⟩ := exists_norm_one_add_mul_ge hw
  refine ⟨c / 2, by positivity, fun a ha x hx => ?_⟩
  have h1 := h x hx
  have h2 : ‖1 + w * x‖ ≤ ‖1 + a * x‖ + ‖a - w‖ * x := by
    have := norm_add_le (1 + a * (x : ℂ)) ((w - a) * x)
    rw [show 1 + a * (x : ℂ) + (w - a) * x = 1 + w * x by ring, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hx, norm_sub_rev] at this
    exact this
  have h3 : ‖a - w‖ < c / 2 := by rwa [← dist_eq_norm]
  nlinarith

theorem integrableOn_mellin_one_div_one_add_mul {a : ℂ} {c : ℝ} (hc : 0 < c)
    (h : ∀ x : ℝ, 0 ≤ x → c * (1 + x) ≤ ‖1 + a * x‖) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fun x : ℝ => 1 / (1 + a * x)) s := by
  have hb := (integrableOn_rpow_div_one_add_pow (α := s.re - 1) (k := 1) (by linarith)
    (by push_cast; linarith)).const_mul c⁻¹
  refine Integrable.mono' hb ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun x hx => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hne : 1 + a * x ≠ 0 := fun e => by
      have := h x (le_of_lt hx); rw [e, norm_zero] at this
      nlinarith [show (0 : ℝ) < x from hx]
    exact (((continuous_ofReal.continuousAt).cpow continuousAt_const
      (ofReal_mem_slitPlane.mpr hx)).smul (continuousAt_const.div (by fun_prop)
        hne)).continuousWithinAt
  · have hx0 : (0 : ℝ) < x := hx
    have h1 := h x hx0.le
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, one_re, norm_div, norm_one, pow_one]
    rw [show c⁻¹ * (x ^ (s.re - 1) / (1 + x)) = x ^ (s.re - 1) * (1 / (c * (1 + x))) by
      field_simp]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) h1)
      (Real.rpow_pos_of_pos hx0 _).le

theorem differentiableOn_mellin_one_div_one_add_mul {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    DifferentiableOn ℂ (fun a : ℂ => mellin (fun x : ℝ => 1 / (1 + a * x)) s) slitPlane := by
  intro w hw
  obtain ⟨c, hc, hball⟩ := exists_ball_norm_one_add_mul_ge hw
  have hne : ∀ a ∈ ball w c, ∀ x : ℝ, 0 ≤ x → 1 + a * x ≠ 0 := fun a ha x hx e => by
    have := hball a ha x hx; rw [e, norm_zero] at this; nlinarith
  have hbound := (integrableOn_rpow_div_one_add_pow (α := s.re) (k := 2) (by linarith)
    (by push_cast; linarith)).const_mul (c ^ 2)⁻¹
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun a : ℂ => fun x : ℝ => (x : ℂ) ^ (s - 1) • (1 / (1 + a * x)))
    (F' := fun a : ℂ => fun x : ℝ => (x : ℂ) ^ (s - 1) • (-(x : ℂ) / (1 + a * x) ^ 2))
    (x₀ := w) (bound := fun x : ℝ => (c ^ 2)⁻¹ * (x ^ s.re / (1 + x) ^ 2))
    (ball_mem_nhds w hc)
    (by
      filter_upwards [ball_mem_nhds w hc] with a ha
      exact (integrableOn_mellin_one_div_one_add_mul hc (hball a ha) hs0 hs1).aestronglyMeasurable)
    (integrableOn_mellin_one_div_one_add_mul hc (hball w (mem_ball_self hc)) hs0 hs1)
    (by
      refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      exact (((continuous_ofReal.continuousAt).cpow continuousAt_const
        (ofReal_mem_slitPlane.mpr hx)).smul
          ((by fun_prop : ContinuousAt (fun x : ℝ => -(x : ℂ)) x).div (by fun_prop)
            (pow_ne_zero 2 (hne w (mem_ball_self hc) x (le_of_lt hx))))).continuousWithinAt)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx a ha => ?_))
    hbound
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx a ha => ?_))
  · exact hd.2.differentiableAt.differentiableWithinAt
  · have hx0 : (0 : ℝ) < x := hx
    have h1 := hball a ha x hx0.le
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, one_re, norm_div, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg hx0.le, norm_pow]
    have hp : x ^ (s.re - 1) * x = x ^ s.re := by
      rw [← Real.rpow_add_one hx0.ne', sub_add_cancel]
    have h2 : (c * (1 + x)) ^ 2 ≤ ‖1 + a * x‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    calc x ^ (s.re - 1) * (x / ‖1 + a * x‖ ^ 2) = x ^ s.re / ‖1 + a * x‖ ^ 2 := by
          rw [← hp]; ring
      _ ≤ x ^ s.re / (c * (1 + x)) ^ 2 :=
          div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hx0 _).le (by positivity) h2
      _ = (c ^ 2)⁻¹ * (x ^ s.re / (1 + x) ^ 2) := by field_simp
  · have hx0 : (0 : ℝ) < x := hx
    have h1 := (hasDerivAt_const a (1 : ℂ)).div
      (((hasDerivAt_id a).mul_const (x : ℂ)).const_add 1) (hne a ha x hx0.le)
    simp only [id] at h1
    refine (h1.const_smul ((x : ℂ) ^ (s - 1))).congr_deriv ?_
    simp only [smul_eq_mul]; ring

/-- `∫_0^∞ x^{s−1}/(1 + ax) dx = a^{−s} π/sin(πs)` for `a ∉ (−∞, 0]` (`|ph a| < π`) and
`0 < ℜs < 1`, by continuation in `a` from `a > 0`. -/
theorem mellin_one_div_one_add_mul {a : ℂ} (ha : a ∈ slitPlane) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    mellin (fun x : ℝ => 1 / (1 + a * x)) s = a ^ (-s) * (π / Complex.sin (π * s)) := by
  have hG : DifferentiableOn ℂ (fun a : ℂ => a ^ (-s) * (π / Complex.sin (π * s))) slitPlane :=
    fun w hw => ((differentiableAt_id.cpow (differentiableAt_const _) hw).mul_const
      _).differentiableWithinAt
  exact dlmf_1_10_ii_functional isOpen_slitPlane
    (starConvex_one_slitPlane.isPathConnected
      (mem_slitPlane_iff.mpr (Or.inl one_pos))).isConnected.isPreconnected
    (differentiableOn_mellin_one_div_one_add_mul hs0 hs1) hG one_lt_two
    (fun x hx => ofReal_mem_slitPlane.mpr (by linarith [hx.1]))
    (fun x hx => mellin_one_div_one_add_mul_pos (by linarith [hx.1]) hs0 hs1) ha

theorem mellinConvergent_one_div_one_add_mul {a : ℂ} (ha : a ∈ slitPlane) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) : MellinConvergent (fun x : ℝ => 1 / (1 + a * x)) s := by
  obtain ⟨c, hc, h⟩ := exists_norm_one_add_mul_ge ha
  exact integrableOn_mellin_one_div_one_add_mul hc h hs0 hs1

/-! ### Rows 4, 10, 11 -/

theorem mellin_add' {f g : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (fun x => f x + g x) s = mellin f s + mellin g s := by
  simp only [mellin, smul_add]
  exact integral_add hf hg

theorem mellin_sub' {f g : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (fun x => f x - g x) s = mellin f s - mellin g s := by
  simp only [mellin, smul_sub]
  exact integral_sub hf hg

/-- **Table 1.14.5, row 4**: `𝓜[1/(1 + x)](s) = π csc(sπ)` (`0 < ℜs < 1`). -/
theorem dlmf_table_1_14_5_r4 {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x : ℝ => 1 / (1 + (x : ℂ))) s = π / Complex.sin (s * π) := by
  rw [mellin_one_div_one_add hs0 hs1, mul_comm]

theorem mellin_const_mul' (c : ℂ) (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun t => c * f t) s = c * mellin f s := by
  simpa only [smul_eq_mul] using mellin_const_smul f s c

theorem cexp_mul_I_mem_slitPlane {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) :
    cexp (θ * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg]
  refine ⟨?_, Complex.exp_ne_zero _⟩
  rw [Complex.exp_mul_I, arg_cos_add_sin_mul_I ⟨h1, h2.le⟩]
  exact h2.ne

theorem cexp_mul_I_cpow {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) (s : ℂ) :
    cexp (θ * I) ^ (-s) = cexp (-(s * θ) * I) := by
  rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp (by simpa using h1)
    (by simpa using h2.le)]
  ring_nf

theorem one_add_cexp_mul_ne_zero {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) {x : ℝ} (hx : 0 ≤ x) :
    1 + cexp (θ * I) * x ≠ 0 := by
  obtain ⟨c, hc, h⟩ := exists_norm_one_add_mul_ge (cexp_mul_I_mem_slitPlane h1 h2)
  intro e; have := h x hx; rw [e, norm_zero] at this; nlinarith

theorem one_add_two_mul_cos_add_sq {θ x : ℝ} :
    ((1 + 2 * x * Real.cos θ + x ^ 2 : ℝ) : ℂ) =
      (1 + cexp (θ * I) * x) * (1 + cexp ((-θ : ℝ) * I) * x) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  linear_combination (-(x : ℂ) ^ 2) * Complex.sin_sq_add_cos_sq (θ : ℂ) +
    Complex.sin (θ : ℂ) ^ 2 * (x : ℂ) ^ 2 * I_sq

theorem cexp_add_cexp_neg (θ : ℝ) :
    cexp (θ * I) + cexp ((-θ : ℝ) * I) = 2 * Real.cos θ := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]; push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]; ring

theorem cexp_sub_cexp_neg (θ : ℝ) :
    cexp (θ * I) - cexp ((-θ : ℝ) * I) = 2 * I * Real.sin θ := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]; push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]; ring

/-- **Table 1.14.5, row 10**: `𝓜[(1 + x cos θ)/(1 + 2x cos θ + x²)](s) = π cos(sθ)/sin(sπ)`
(`−π < θ < π`, `0 < ℜs < 1`). -/
theorem dlmf_table_1_14_5_r10 {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    mellin (fun x : ℝ => (((1 + x * Real.cos θ) / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ)) s =
      π * Complex.cos (s * θ) / Complex.sin (s * π) := by
  have h1' : -π < -θ := by linarith
  have h2' : -θ < π := by linarith
  have e : ∀ x : ℝ, 0 < x →
      (((1 + x * Real.cos θ) / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ) =
        1 / 2 * (1 / (1 + cexp (θ * I) * x)) + 1 / 2 * (1 / (1 + cexp ((-θ : ℝ) * I) * x)) :=
    fun x hx => by
      have hp := one_add_cexp_mul_ne_zero h1 h2 hx.le
      have hm := one_add_cexp_mul_ne_zero h1' h2' hx.le
      have hn : ((1 + x * Real.cos θ : ℝ) : ℂ) =
          ((1 + cexp (θ * I) * x) + (1 + cexp ((-θ : ℝ) * I) * x)) / 2 := by
        rw [show (1 + cexp (θ * I) * x) + (1 + cexp ((-θ : ℝ) * I) * x) =
          2 + (cexp (θ * I) + cexp ((-θ : ℝ) * I)) * x by ring, cexp_add_cexp_neg]
        push_cast; ring
      rw [ofReal_div, one_add_two_mul_cos_add_sq, hn]
      generalize 1 + cexp (θ * I) * x = p at hp ⊢
      generalize 1 + cexp ((-θ : ℝ) * I) * x = q at hm ⊢
      field_simp
      ring
  have hc1 : MellinConvergent (fun x : ℝ => 1 / 2 * (1 / (1 + cexp (θ * I) * x))) s := by
    simpa only [smul_eq_mul] using (mellinConvergent_one_div_one_add_mul
      (cexp_mul_I_mem_slitPlane h1 h2) hs0 hs1).const_smul (1 / 2 : ℂ)
  have hc2 : MellinConvergent (fun x : ℝ => 1 / 2 * (1 / (1 + cexp ((-θ : ℝ) * I) * x))) s := by
    simpa only [smul_eq_mul] using (mellinConvergent_one_div_one_add_mul
      (cexp_mul_I_mem_slitPlane h1' h2') hs0 hs1).const_smul (1 / 2 : ℂ)
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [e x hx]), ← mellin,
    mellin_add' hc1 hc2, mellin_const_mul', mellin_const_mul',
    mellin_one_div_one_add_mul (cexp_mul_I_mem_slitPlane h1 h2) hs0 hs1,
    mellin_one_div_one_add_mul (cexp_mul_I_mem_slitPlane h1' h2') hs0 hs1,
    cexp_mul_I_cpow h1 h2, cexp_mul_I_cpow h1' h2', Complex.cos, mul_comm s (π : ℂ)]
  push_cast
  ring_nf

theorem sin_eq_exp_div (z : ℂ) : Complex.sin z = (cexp (z * I) - cexp (-z * I)) / (2 * I) := by
  rw [Complex.sin]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Table 1.14.5, row 11**: `𝓜[x sin θ/(1 + 2x cos θ + x²)](s) = π sin(sθ)/sin(sπ)`
(`−π < θ < π`, `0 < ℜs < 1`). -/
theorem dlmf_table_1_14_5_r11 {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    mellin (fun x : ℝ => ((x * Real.sin θ / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ)) s =
      π * Complex.sin (s * θ) / Complex.sin (s * π) := by
  have h1' : -π < -θ := by linarith
  have h2' : -θ < π := by linarith
  have e : ∀ x : ℝ, 0 < x →
      ((x * Real.sin θ / (1 + 2 * x * Real.cos θ + x ^ 2) : ℝ) : ℂ) =
        (1 / (2 * I)) * (1 / (1 + cexp ((-θ : ℝ) * I) * x)) -
          (1 / (2 * I)) * (1 / (1 + cexp (θ * I) * x)) :=
    fun x hx => by
      have hp := one_add_cexp_mul_ne_zero h1 h2 hx.le
      have hm := one_add_cexp_mul_ne_zero h1' h2' hx.le
      have hn : ((x * Real.sin θ : ℝ) : ℂ) =
          ((1 + cexp (θ * I) * x) - (1 + cexp ((-θ : ℝ) * I) * x)) / (2 * I) := by
        rw [show (1 + cexp (θ * I) * x) - (1 + cexp ((-θ : ℝ) * I) * x) =
          (cexp (θ * I) - cexp ((-θ : ℝ) * I)) * x by ring, cexp_sub_cexp_neg]
        push_cast; field_simp
      rw [ofReal_div, one_add_two_mul_cos_add_sq, hn]
      generalize 1 + cexp (θ * I) * x = p at hp ⊢
      generalize 1 + cexp ((-θ : ℝ) * I) * x = q at hm ⊢
      field_simp
  have hc1 : MellinConvergent (fun x : ℝ => 1 / (2 * I) * (1 / (1 + cexp ((-θ : ℝ) * I) * x)))
      s := by
    simpa only [smul_eq_mul] using (mellinConvergent_one_div_one_add_mul
      (cexp_mul_I_mem_slitPlane h1' h2') hs0 hs1).const_smul (1 / (2 * I) : ℂ)
  have hc2 : MellinConvergent (fun x : ℝ => 1 / (2 * I) * (1 / (1 + cexp (θ * I) * x))) s := by
    simpa only [smul_eq_mul] using (mellinConvergent_one_div_one_add_mul
      (cexp_mul_I_mem_slitPlane h1 h2) hs0 hs1).const_smul (1 / (2 * I) : ℂ)
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [e x hx]), ← mellin,
    mellin_sub' hc1 hc2, mellin_const_mul', mellin_const_mul',
    mellin_one_div_one_add_mul (cexp_mul_I_mem_slitPlane h1 h2) hs0 hs1,
    mellin_one_div_one_add_mul (cexp_mul_I_mem_slitPlane h1' h2') hs0 hs1,
    cexp_mul_I_cpow h1 h2, cexp_mul_I_cpow h1' h2', mul_comm s (π : ℂ), sin_eq_exp_div (s * θ)]
  push_cast
  ring_nf

end Azurite.DLMF
