/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section23
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# DLMF §4.23(viii) Gudermannian Function

## Inverse hyperbolic functions of a real variable

4.23.42 uses the principal inverse hyperbolic functions, which DLMF defines only in §4.37. As
with the inverse trigonometric functions in §4.15, we use DLMF's own definitions (4.37.1–4.37.3,
4.37.7–4.37.9), here for real arguments, where the integration path is the real segment and the
square roots are principal. We then bridge to Mathlib.

* `arcsinhR x = ∫₀ˣ dt/(1 + t²)^{1/2}` (`arcsinhR_eq`: `= Real.arsinh x`).
* `arccoshR x = ∫₁ˣ dt/(t² − 1)^{1/2}`, `x ≥ 1` (`arccoshR_eq`: `= Real.arcosh x`).
* `arctanhR x = ∫₀ˣ dt/(1 − t²)`, `|x| < 1` (`arctanhR_eq`: `= Real.artanh x`).
* `arccschR`, `arcsechR`, `arccothR` via `1/x`.

## §4.23(viii)

* 4.23.39: `gd x = ∫₀ˣ sech t dt`.
* 4.23.40: `dlmf_4_23_40` (`2 arctan(eˣ) − ½π`, `arcsin(tanh x)`, `arccsc(coth x)`,
  `arctan(sinh x)`, `arccot(csch x)`). **Erratum**: `arccos(sech x)` and `arcsec(cosh x)` equal
  `gd |x|`, not `gd x` (`dlmf_4_23_40_cos`; true for `x ≥ 0`, `dlmf_4_23_40_cos_nonneg`; false
  for `x < 0`, `dlmf_4_23_40_cos_neg`).
* 4.23.41: `gdInv x = ∫₀ˣ sec t dt`, `−½π < x < ½π`. It is the inverse of `gd`: `gd_mem`,
  `gdInv_gd`, `gd_gdInv`.
* 4.23.42: `dlmf_4_23_42` (`ln tan(½x + ¼π)`, `ln(sec x + tan x)`, `arcsinh(tan x)`,
  `arccsch(cot x)`, `arctanh(sin x)`, `arccoth(csc x)`). **Erratum**: `arccosh(sec x)` and
  `arcsech(cos x)` equal `gd⁻¹ |x|` (`dlmf_4_23_42_cosh`; true for `x ≥ 0`, false for `x < 0`).
-/

open Set Filter MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### Inverse hyperbolic functions of a real variable (DLMF 4.37) -/

/-- **DLMF 4.37.1** (principal value, real `x`): `arcsinh x = ∫₀ˣ dt/(1 + t²)^{1/2}`. -/
noncomputable def arcsinhR (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, 1 / √(1 + t ^ 2)

/-- **DLMF 4.37.2** (principal value, real `x ≥ 1`): `arccosh x = ∫₁ˣ dt/(t² − 1)^{1/2}`. -/
noncomputable def arccoshR (x : ℝ) : ℝ := ∫ t in (1 : ℝ)..x, 1 / √(t ^ 2 - 1)

/-- **DLMF 4.37.3** (principal value, real `|x| < 1`): `arctanh x = ∫₀ˣ dt/(1 − t²)`. -/
noncomputable def arctanhR (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, 1 / (1 - t ^ 2)

/-- **DLMF 4.37.7**: `arccsch x = arcsinh(1/x)`. -/
noncomputable def arccschR (x : ℝ) : ℝ := arcsinhR (1 / x)

/-- **DLMF 4.37.8**: `arcsech x = arccosh(1/x)`. -/
noncomputable def arcsechR (x : ℝ) : ℝ := arccoshR (1 / x)

/-- **DLMF 4.37.9**: `arccoth x = arctanh(1/x)`. -/
noncomputable def arccothR (x : ℝ) : ℝ := arctanhR (1 / x)

theorem arcsinhR_eq (x : ℝ) : arcsinhR x = Real.arsinh x := by
  have hc : Continuous fun t : ℝ => 1 / √(1 + t ^ 2) :=
    continuous_const.div (by fun_prop) fun t => (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [arcsinhR, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.arsinh)
    (fun t _ => by simpa [one_div] using Real.hasDerivAt_arsinh t) (hc.intervalIntegrable _ _),
    Real.arsinh_zero, sub_zero]

theorem arccoshR_eq {x : ℝ} (hx : 1 ≤ x) : arccoshR x = Real.arcosh x := by
  have hcont : ContinuousOn Real.arcosh (Icc 1 x) :=
    Real.continuousOn_arcosh.mono fun t ht => ht.1
  have hd : ∀ t ∈ Ioo 1 x, HasDerivAt Real.arcosh (1 / √(t ^ 2 - 1)) t := fun t ht => by
    simpa [one_div] using Real.hasDerivAt_arcosh ht.1
  have hint : IntervalIntegrable (fun t : ℝ => 1 / √(t ^ 2 - 1)) volume 1 x :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := Real.arcosh)
      (by rwa [uIcc_of_le hx]) (fun t ht => hd t (by rwa [min_eq_left hx, max_eq_right hx] at ht))
      (fun t _ => by positivity)
  rw [arccoshR, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx hcont hd hint,
    Real.arcosh_zero, sub_zero]

theorem arctanhR_eq {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : arctanhR x = Real.artanh x := by
  have hs : [[(0 : ℝ), x]] ⊆ Ioo (-1) 1 :=
    ordConnected_Ioo.uIcc_subset ⟨by norm_num, by norm_num⟩ hx
  have hd : ∀ t ∈ [[(0 : ℝ), x]], HasDerivAt
      (fun t => 1 / 2 * (Real.log (1 + t) - Real.log (1 - t))) (1 / (1 - t ^ 2)) t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hs ht
    have h1' : (1 + t) ≠ 0 := by linarith
    have h2' : (1 - t) ≠ 0 := by linarith
    have := (((hasDerivAt_id t).const_add 1).log h1').sub (((hasDerivAt_id t).const_sub 1).log h2')
    have h3 : 1 - t ^ 2 ≠ 0 := by
      rw [show 1 - t ^ 2 = (1 - t) * (1 + t) by ring]; exact mul_ne_zero h2' h1'
    refine (this.const_mul (1 / 2)).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (1 - t ^ 2)) volume 0 x := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div (by fun_prop) fun t ht => ?_
    obtain ⟨h1, h2⟩ := hs ht
    nlinarith
  rw [arctanhR, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint,
    Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩, Real.log_div (by linarith [hx.1])
      (by linarith [hx.2])]
  simp

/-! ### 4.23.39–4.23.40 -/

/-- **DLMF 4.23.39**: the Gudermannian `gd x = ∫₀ˣ sech t dt`. -/
noncomputable def gd (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, 1 / Real.cosh t

theorem gd_eq_arctan (x : ℝ) : gd x = 2 * Real.arctan (Real.exp x) - π / 2 := by
  have hc : Continuous fun t : ℝ => 1 / Real.cosh t :=
    continuous_const.div Real.continuous_cosh fun t => (Real.cosh_pos t).ne'
  have hd : ∀ t ∈ [[(0 : ℝ), x]], HasDerivAt (fun t => 2 * Real.arctan (Real.exp t))
      (1 / Real.cosh t) t := by
    intro t _
    refine ((Real.hasDerivAt_exp t).arctan.const_mul 2).congr_deriv ?_
    rw [Real.cosh_eq, Real.exp_neg]
    have := Real.exp_pos t
    field_simp
    ring
  rw [gd, intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _),
    Real.exp_zero, Real.arctan_one]
  ring

/-- `gd x ∈ (−½π, ½π)`, `sin(gd x) = tanh x`, `cos(gd x) = sech x`. -/
theorem gd_trig (x : ℝ) :
    gd x ∈ Ioo (-(π / 2)) (π / 2) ∧ Real.sin (gd x) = Real.tanh x ∧
      Real.cos (gd x) = 1 / Real.cosh x := by
  have ha0 := Real.arctan_pos.mpr (Real.exp_pos x)
  have ha1 := Real.arctan_lt_pi_div_two (Real.exp x)
  have he := Real.exp_pos x
  have hs : 0 < √(1 + Real.exp x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : √(1 + Real.exp x ^ 2) ^ 2 = 1 + Real.exp x ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨⟨by rw [gd_eq_arctan]; linarith, by rw [gd_eq_arctan]; linarith⟩, ?_, ?_⟩
  · rw [gd_eq_arctan, Real.sin_sub_pi_div_two, Real.cos_two_mul, Real.cos_arctan,
      Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, div_pow, hs2]
    field_simp
    ring
  · rw [gd_eq_arctan, Real.cos_sub_pi_div_two, Real.sin_two_mul, Real.cos_arctan,
      Real.sin_arctan, Real.cosh_eq, Real.exp_neg]
    field_simp
    rw [hs2]
    ring

theorem gd_mem (x : ℝ) : gd x ∈ Ioo (-(π / 2)) (π / 2) := (gd_trig x).1

theorem sin_mem_Ioo {θ : ℝ} (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) : Real.sin θ ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · have h : Real.sin (-(π / 2)) = -1 := by rw [Real.sin_neg, Real.sin_pi_div_two]
    rw [← h]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two le_rfl (by linarith [hθ.2]) hθ.1
  · rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hθ.1]) le_rfl hθ.2

theorem gd_eq_arcsin (x : ℝ) : gd x = Real.arcsin (Real.tanh x) := by
  obtain ⟨hm, hs, -⟩ := gd_trig x
  rw [← hs, Real.arcsin_sin hm.1.le hm.2.le]

theorem tan_gd (x : ℝ) : Real.tan (gd x) = Real.sinh x := by
  obtain ⟨-, hs, hc⟩ := gd_trig x
  have := Real.cosh_pos x
  rw [Real.tan_eq_sin_div_cos, hs, hc, Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem gd_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gd x := by
  rw [gd_eq_arctan]
  have : π / 4 ≤ Real.arctan (Real.exp x) := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono.monotone (Real.one_le_exp hx)
  linarith

theorem gd_neg_of_neg {x : ℝ} (hx : x < 0) : gd x < 0 := by
  rw [gd_eq_arctan]
  have : Real.arctan (Real.exp x) < π / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hx)
  linarith

/-- **DLMF 4.23.40**: `gd x = 2 arctan(eˣ) − ½π = arcsin(tanh x) = arccsc(coth x)
= arctan(sinh x) = arccot(csch x)` (principal values §4.23(ii)). -/
theorem dlmf_4_23_40 (x : ℝ) :
    gd x = 2 * Real.arctan (Real.exp x) - π / 2 ∧
      (gd x : ℂ) = arcsinD (Real.tanh x : ℝ) ∧
      (gd x : ℂ) = arccscD (Real.cosh x / Real.sinh x : ℝ) ∧
      (gd x : ℂ) = arctanD (Real.sinh x : ℝ) ∧
      (gd x : ℂ) = arccotD (1 / Real.sinh x : ℝ) := by
  obtain ⟨hm, hs, -⟩ := gd_trig x
  have hS : (gd x : ℂ) = arcsinD (Real.tanh x : ℝ) := by
    rw [arcsinD_ofReal (hs ▸ sin_mem_Ioo hm), gd_eq_arcsin]
  have hT : (gd x : ℂ) = arctanD (Real.sinh x : ℝ) := by
    rw [arctanD_ofReal, ← tan_gd, Real.arctan_tan hm.1 hm.2]
  refine ⟨gd_eq_arctan x, hS, ?_, hT, ?_⟩
  · rw [hS, arccscD, ← Complex.ofReal_one, ← Complex.ofReal_div, one_div_div,
      ← Real.tanh_eq_sinh_div_cosh]
  · rw [hT, arccotD, ← Complex.ofReal_one, ← Complex.ofReal_div, one_div_one_div]

/-- **DLMF 4.23.40**, the `arccos` and `arcsec` forms (corrected): `arccos(sech x)
= arcsec(cosh x) = gd |x|`. -/
theorem dlmf_4_23_40_cos (x : ℝ) :
    arccosD (1 / Real.cosh x : ℝ) = (gd |x| : ℂ) ∧ arcsecD (Real.cosh x : ℝ) = (gd |x| : ℂ) := by
  obtain ⟨hm, -, hc⟩ := gd_trig |x|
  rw [Real.cosh_abs] at hc
  have hb : 1 / Real.cosh x ∈ Icc (-1 : ℝ) 1 := by
    rw [← hc]; exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hC : arccosD (1 / Real.cosh x : ℝ) = (gd |x| : ℂ) := by
    rw [arccosD_ofReal_Icc hb, ← hc,
      Real.arccos_cos (gd_nonneg (abs_nonneg x)) (by linarith [hm.2, Real.pi_pos])]
  refine ⟨hC, ?_⟩
  rw [arcsecD, ← Complex.ofReal_one, ← Complex.ofReal_div, hC]

/-- **DLMF 4.23.40**, the `arccos` and `arcsec` forms as printed, for `x ≥ 0`. -/
theorem dlmf_4_23_40_cos_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (gd x : ℂ) = arccosD (1 / Real.cosh x : ℝ) ∧ (gd x : ℂ) = arcsecD (Real.cosh x : ℝ) := by
  obtain ⟨h1, h2⟩ := dlmf_4_23_40_cos x
  rw [h1, h2, abs_of_nonneg hx]
  exact ⟨rfl, rfl⟩

/-- **Erratum**: for `x < 0`, `gd x ≠ arccos(sech x)` (and `≠ arcsec(cosh x)`). -/
theorem dlmf_4_23_40_cos_neg {x : ℝ} (hx : x < 0) :
    (gd x : ℂ) ≠ arccosD (1 / Real.cosh x : ℝ) ∧ (gd x : ℂ) ≠ arcsecD (Real.cosh x : ℝ) := by
  obtain ⟨h1, h2⟩ := dlmf_4_23_40_cos x
  have hne : (gd x : ℂ) ≠ (gd |x| : ℂ) := by
    rw [Ne, Complex.ofReal_inj]
    linarith [gd_neg_of_neg hx, gd_nonneg (abs_nonneg x)]
  rw [h1, h2]
  exact ⟨hne, hne⟩

/-! ### 4.23.41–4.23.42 -/

/-- **DLMF 4.23.41**: the inverse Gudermannian `gd⁻¹ x = ∫₀ˣ sec t dt`, `−½π < x < ½π`. -/
noncomputable def gdInv (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, 1 / Real.cos t

theorem gdInv_eq_artanh {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    gdInv x = Real.artanh (Real.sin x) := by
  have hs : [[(0 : ℝ), x]] ⊆ Ioo (-(π / 2)) (π / 2) :=
    ordConnected_Ioo.uIcc_subset ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hx
  have hd : ∀ t ∈ [[(0 : ℝ), x]], HasDerivAt
      (fun t => 1 / 2 * (Real.log (1 + Real.sin t) - Real.log (1 - Real.sin t)))
      (1 / Real.cos t) t := by
    intro t ht
    have hm := sin_mem_Ioo (hs ht)
    have hc := Real.cos_pos_of_mem_Ioo (hs ht)
    have h1' : (1 + Real.sin t) ≠ 0 := by linarith [hm.1]
    have h2' : (1 - Real.sin t) ≠ 0 := by linarith [hm.2]
    have := (((Real.hasDerivAt_sin t).const_add 1).log h1').sub
      (((Real.hasDerivAt_sin t).const_sub 1).log h2')
    refine (this.const_mul (1 / 2)).congr_deriv ?_
    have hsc := Real.sin_sq_add_cos_sq t
    field_simp
    linear_combination (2 : ℝ) * hsc
  have hint : IntervalIntegrable (fun t : ℝ => 1 / Real.cos t) volume 0 x := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.div Real.continuous_cos.continuousOn fun t ht =>
      (Real.cos_pos_of_mem_Ioo (hs ht)).ne'
  have hm := sin_mem_Ioo hx
  rw [gdInv, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint,
    Real.artanh_eq_half_log ⟨hm.1.le, hm.2.le⟩, Real.log_div (by linarith [hm.1])
      (by linarith [hm.2])]
  simp

theorem gdInv_gd (x : ℝ) : gdInv (gd x) = x := by
  rw [gdInv_eq_artanh (gd_mem x), (gd_trig x).2.1, Real.artanh_tanh]

theorem gd_gdInv {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) : gd (gdInv x) = x := by
  rw [gd_eq_arcsin, gdInv_eq_artanh hx, Real.tanh_artanh (sin_mem_Ioo hx),
    Real.arcsin_sin hx.1.le hx.2.le]

/-- `gd⁻¹ x = ln((1 + sin x)/cos x)`. -/
theorem gdInv_eq_log {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    gdInv x = Real.log ((1 + Real.sin x) / Real.cos x) := by
  have hm := sin_mem_Ioo hx
  have hc := Real.cos_pos_of_mem_Ioo hx
  have hsc := Real.sin_sq_add_cos_sq x
  have hc2 : Real.cos x ^ 2 = (1 - Real.sin x) * (1 + Real.sin x) := by linarith
  have hq : (1 + Real.sin x) / (1 - Real.sin x) = ((1 + Real.sin x) / Real.cos x) ^ 2 := by
    have : 1 - Real.sin x ≠ 0 := by linarith [hm.2]
    have : 1 + Real.sin x ≠ 0 := by linarith [hm.1]
    rw [div_pow, hc2]
    field_simp
  rw [gdInv_eq_artanh hx, Real.artanh_eq_half_log ⟨hm.1.le, hm.2.le⟩, hq, Real.log_pow]
  push_cast
  ring

theorem tan_half_add_pi_div_four {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    Real.tan (x / 2 + π / 4) = (1 + Real.sin x) / Real.cos x := by
  have hc := Real.cos_pos_of_mem_Ioo hx
  set u := x / 2 + π / 4 with hu
  have hπ := Real.pi_pos
  have hcu : 0 < Real.cos u :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
    (by linarith [hx.2])
  have hx' : x = 2 * u - π / 2 := by rw [hu]; ring
  have hs : 1 + Real.sin x = 2 * Real.sin u ^ 2 := by
    rw [hx', Real.sin_sub_pi_div_two, Real.cos_two_mul]
    linear_combination (-(2 : ℝ)) * Real.sin_sq_add_cos_sq u
  have hcx : Real.cos x = 2 * Real.sin u * Real.cos u := by
    rw [hx', Real.cos_sub_pi_div_two, Real.sin_two_mul]
  rw [Real.tan_eq_sin_div_cos, hcx, hs]
  field_simp

/-- **DLMF 4.23.42**: for `−½π < x < ½π`, `gd⁻¹ x = ln tan(½x + ¼π) = ln(sec x + tan x)
= arcsinh(tan x) = arccsch(cot x) = arctanh(sin x) = arccoth(csc x)`. -/
theorem dlmf_4_23_42 {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    gdInv x = Real.log (Real.tan (1 / 2 * x + 1 / 4 * π)) ∧
      gdInv x = Real.log (1 / Real.cos x + Real.tan x) ∧
      gdInv x = arcsinhR (Real.tan x) ∧ gdInv x = arccschR (Real.cot x) ∧
      gdInv x = arctanhR (Real.sin x) ∧ gdInv x = arccothR (1 / Real.sin x) := by
  have hm := sin_mem_Ioo hx
  have hc := Real.cos_pos_of_mem_Ioo hx
  have hL := gdInv_eq_log hx
  have hsec : 1 / Real.cos x + Real.tan x = (1 + Real.sin x) / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]; field_simp
  have hA : gdInv x = arcsinhR (Real.tan x) := by
    have hsq : √(1 + Real.tan x ^ 2) = 1 / Real.cos x := by
      refine sqrt_eq_of_eq_sq (by positivity) ?_
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      linarith [Real.sin_sq_add_cos_sq x]
    rw [arcsinhR_eq, Real.arsinh, hsq, add_comm, hsec, hL]
  have hT : gdInv x = arctanhR (Real.sin x) := by rw [arctanhR_eq hm, gdInv_eq_artanh hx]
  refine ⟨?_, by rw [hsec, hL], hA, ?_, hT, ?_⟩
  · rw [show 1 / 2 * x + 1 / 4 * π = x / 2 + π / 4 by ring, tan_half_add_pi_div_four hx, hL]
  · rw [arccschR, Real.cot_eq_cos_div_sin, one_div_div, ← Real.tan_eq_sin_div_cos, hA]
  · rw [arccothR, one_div_one_div, hT]

/-- **DLMF 4.23.42**, the `arccosh` and `arcsech` forms (corrected): for `−½π < x < ½π`,
`arccosh(sec x) = arcsech(cos x) = gd⁻¹ |x|`; so DLMF's form holds for `0 ≤ x` and fails for
`x < 0`. -/
theorem dlmf_4_23_42_cosh {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    arccoshR (1 / Real.cos x) = gdInv |x| ∧ arcsechR (Real.cos x) = gdInv |x| ∧
      (0 ≤ x → gdInv x = arccoshR (1 / Real.cos x) ∧ gdInv x = arcsechR (Real.cos x)) ∧
      (x < 0 → gdInv x ≠ arccoshR (1 / Real.cos x) ∧ gdInv x ≠ arcsechR (Real.cos x)) := by
  have hc := Real.cos_pos_of_mem_Ioo hx
  have hax : |x| ∈ Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [abs_nonneg x, Real.pi_pos], abs_lt.mpr hx⟩
  have hc1 : Real.cos x ≤ 1 := Real.cos_le_one x
  have hge : 1 ≤ 1 / Real.cos x := by rw [le_div_iff₀ hc]; linarith
  have hsx : |Real.sin x| = Real.sin |x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h
        (by linarith [hx.2, Real.pi_pos]))]
    · rw [abs_of_nonpos h, Real.sin_neg, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h
        (by linarith [hx.1, Real.pi_pos]))]
  have hK : arccoshR (1 / Real.cos x) = gdInv |x| := by
    have hsq : √((1 / Real.cos x) ^ 2 - 1) = |Real.sin x| / Real.cos x := by
      refine sqrt_eq_of_eq_sq (by positivity) ?_
      rw [div_pow, div_pow, sq_abs]
      field_simp
      linarith [Real.sin_sq_add_cos_sq x]
    rw [arccoshR_eq hge, Real.arcosh, hsq, gdInv_eq_log hax, Real.cos_abs, ← hsx]
    congr 1
    field_simp
  have hS : arcsechR (Real.cos x) = gdInv |x| := hK
  refine ⟨hK, hS, fun h => ?_, fun h => ?_⟩
  · rw [hK, hS, abs_of_nonneg h]; exact ⟨rfl, rfl⟩
  · have h1 : gdInv x < 0 := by
      rw [gdInv_eq_artanh hx]
      exact Real.artanh_neg ⟨(sin_mem_Ioo hx).1,
        Real.sin_neg_of_neg_of_neg_pi_lt h (by linarith [hx.1, Real.pi_pos])⟩
    have h2 : 0 ≤ gdInv |x| := by
      rw [gdInv_eq_artanh hax]
      exact Real.artanh_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg x)
        (by linarith [hax.2, Real.pi_pos]))
    rw [hK, hS]
    exact ⟨ne_of_lt (by linarith), ne_of_lt (by linarith)⟩

end Azurite.DLMF
