/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section12Fourier

/-!
# DLMF §5.12: 5.12.5, 5.12.6 and 5.12.9 from 5.12.8

* 5.12.9 is 5.12.8 on the line `t = c + iy` with `w = c`, `z = 1 − c` and `b + 1` in place of `b`
  (`dlmf_5_12_9`; `dlmf_5_12_9_gamma` is the form `Γ(a + b)/(Γ(a)Γ(b + 1))`, valid also at
  `b = 0`, where DLMF's `1/(bB(a, b))` is read as its limit).
* 5.12.5 is 5.12.8 with `w = z = 1` under `t = tan θ`, which turns the integrand into
  `cos^{a−1}θ e^{ibθ}` on `(−½π, ½π)` (`integral_cos_cpow_mul_cexp`), followed by evenness;
  5.12.6 is 5.12.5 shifted by `½π`.

`b` is arbitrary in 5.12.5–5.12.6. The reciprocal `1/B(·, ·)` is the entire function
`Γ(a + 1)/(Γ(·)Γ(·))`; with Mathlib's `Γ(−n) = 0` the DLMF expression is literally that function.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-! ### 5.12.9 -/

/-- 5.12.9 in Gamma form, for every `b` with `ℜ(a + b) > 0`. -/
theorem dlmf_5_12_9_gamma {a b : ℂ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hab : 0 < (a + b).re) :
    1 / (2 * π * I) * ∫ y : ℝ, (c + y * I) ^ (-a) * (1 - (c + y * I)) ^ (-1 - b) * I =
      Gamma (a + b) * (Gamma a)⁻¹ * (Gamma (b + 1))⁻¹ := by
  have h := fourierBeta_eq (w := c) (z := ((1 - c : ℝ) : ℂ)) (a := a) (b := 1 + b)
    (by simpa using hc0) (by simpa using hc1) (by simp only [add_re, one_re] at hab ⊢; linarith)
  have e : ∀ y : ℝ, (c + y * I) ^ (-a) * (1 - (c + y * I)) ^ (-1 - b) * I =
      fourierBetaF c ((1 - c : ℝ) : ℂ) a (1 + b) y * I := fun y => by
    simp only [fourierBetaF]
    congr 3
    · push_cast; ring
    · ring
  simp_rw [e]
  rw [integral_mul_const, h, fourierBetaG]
  rw [show (c : ℂ) + ((1 - c : ℝ) : ℂ) = 1 by push_cast; ring, one_cpow,
    show a + (1 + b) - 1 = a + b by ring, add_comm 1 b]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- **DLMF 5.12.9**: `(2πi)⁻¹ ∫_{c−i∞}^{c+i∞} t^{−a}(1 − t)^{−1−b} dt = 1/(bB(a, b))`,
`0 < c < 1`, `ℜ(a + b) > 0` (`b ≠ 0`; the path is `t = c + iy`, `dt = i dy`). -/
theorem dlmf_5_12_9 {a b : ℂ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hab : 0 < (a + b).re)
    (hb : b ≠ 0) :
    1 / (2 * π * I) * ∫ y : ℝ, (c + y * I) ^ (-a) * (1 - (c + y * I)) ^ (-1 - b) * I =
      1 / (b * dlmfBeta a b) := by
  rw [dlmf_5_12_9_gamma hc0 hc1 hab, Complex.Gamma_add_one _ hb, dlmfBeta, ← mul_div_assoc,
    one_div_div, div_eq_mul_inv, mul_inv, mul_inv]
  ring

/-! ### The substitution `t = tan θ` -/

theorem tan_image : Real.tan '' Ioo (-(π / 2)) (π / 2) = univ := by
  refine eq_univ_of_forall fun y => ⟨Real.arctan y, ?_, Real.tan_arctan y⟩
  exact ⟨Real.neg_pi_div_two_lt_arctan y, Real.arctan_lt_pi_div_two y⟩

theorem tan_injOn : InjOn Real.tan (Ioo (-(π / 2)) (π / 2)) :=
  Real.strictMonoOn_tan.injOn

theorem hasDerivWithinAt_tan {θ : ℝ} (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) :
    HasDerivWithinAt Real.tan (1 / Real.cos θ ^ 2) (Ioo (-(π / 2)) (π / 2)) θ :=
  (Real.hasDerivAt_tan (Real.cos_pos_of_mem_Ioo hθ).ne').hasDerivWithinAt

theorem cexp_cpow_of_im {ζ : ℂ} (h1 : -π < ζ.im) (h2 : ζ.im ≤ π) (w : ℂ) :
    cexp ζ ^ w = cexp (ζ * w) := by
  rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp h1 h2]

theorem one_add_tan_mul_I {θ : ℝ} (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) (σ : ℝ) :
    1 + ((σ * Real.tan θ : ℝ) : ℂ) * I = cexp (-(Real.log (Real.cos θ) : ℂ) + σ * θ * I) ↔
      1 + ((σ * Real.tan θ : ℝ) : ℂ) * I =
        (Complex.cos (σ * θ) + Complex.sin (σ * θ) * I) / Complex.cos θ := by
  have hc := Real.cos_pos_of_mem_Ioo hθ
  rw [Complex.exp_add, ← ofReal_neg, ← ofReal_exp, Real.exp_neg, Real.exp_log hc,
    show (σ : ℂ) * θ * I = ((σ * θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  push_cast
  rw [div_eq_inv_mul]

theorem one_add_tan_mul_I_eq {θ : ℝ} (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) :
    1 + (Real.tan θ : ℂ) * I = cexp (-(Real.log (Real.cos θ) : ℂ) + θ * I) := by
  have hc := Real.cos_pos_of_mem_Ioo hθ
  have hc' : Complex.cos θ ≠ 0 := by rw [← ofReal_cos]; exact_mod_cast hc.ne'
  have h := (one_add_tan_mul_I hθ 1).mpr (by
    simp only [one_mul, ofReal_one]
    rw [ofReal_tan, Complex.tan, eq_div_iff hc']
    ring_nf
    field_simp)
  simpa using h

theorem one_sub_tan_mul_I_eq {θ : ℝ} (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) :
    1 - (Real.tan θ : ℂ) * I = cexp (-(Real.log (Real.cos θ) : ℂ) + -θ * I) := by
  have hc := Real.cos_pos_of_mem_Ioo hθ
  have hc' : Complex.cos θ ≠ 0 := by rw [← ofReal_cos]; exact_mod_cast hc.ne'
  have h := (one_add_tan_mul_I hθ (-1)).mpr (by
    simp only [neg_mul, one_mul, ofReal_neg, ofReal_one, Complex.cos_neg, Complex.sin_neg]
    rw [ofReal_tan, Complex.tan, eq_div_iff hc']
    ring_nf
    field_simp)
  simp only [neg_mul, one_mul, ofReal_neg, ofReal_one] at h
  calc 1 - (Real.tan θ : ℂ) * I = 1 + -((Real.tan θ : ℂ) * I) := by ring
    _ = _ := h
    _ = _ := by rw [neg_mul]

/-- Under `t = tan θ`, `sec²θ · (1 + it)^{−A}(1 − it)^{−B} = cos^{A+B−2}θ e^{i(B−A)θ}`. -/
theorem fourierBetaF_tan (A B : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) :
    |1 / Real.cos θ ^ 2| • fourierBetaF 1 1 A B (Real.tan θ) =
      (Real.cos θ : ℂ) ^ (A + B - 2) * cexp ((B - A) * θ * I) := by
  have hc := Real.cos_pos_of_mem_Ioo hθ
  have hπ := Real.pi_pos
  rw [abs_of_pos (by positivity), Complex.real_smul, fourierBetaF, one_add_tan_mul_I_eq hθ,
    one_sub_tan_mul_I_eq hθ,
    cexp_cpow_of_im (by simp; linarith [hθ.1]) (by simp; linarith [hθ.2]),
    cexp_cpow_of_im (by simp; linarith [hθ.2]) (by simp; linarith [hθ.1]), cpow_pos_eq hc]
  rw [show ((1 / Real.cos θ ^ 2 : ℝ) : ℂ) = cexp (-2 * (Real.log (Real.cos θ) : ℂ)) by
    rw [show (-2 : ℂ) * (Real.log (Real.cos θ) : ℂ) = ((-(2 * Real.log (Real.cos θ))) : ℝ) by
        push_cast; ring, ← ofReal_exp, Real.exp_neg,
      show 2 * Real.log (Real.cos θ) = Real.log (Real.cos θ ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
    push_cast; ring]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- `∫_{−π/2}^{π/2} cos^{a−1}θ e^{ibθ} dθ = 2π Γ(a)2^{−a}/(Γ(½(a−b+1))Γ(½(a+b+1)))`, `ℜa > 0`. -/
theorem integral_cos_cpow_mul_cexp {a : ℂ} (ha : 0 < a.re) (b : ℂ) :
    IntegrableOn (fun θ : ℝ => (Real.cos θ : ℂ) ^ (a - 1) * cexp (b * θ * I))
      (Ioo (-(π / 2)) (π / 2)) ∧
    ∫ θ in Ioo (-(π / 2)) (π / 2), (Real.cos θ : ℂ) ^ (a - 1) * cexp (b * θ * I) =
      2 * π * fourierBetaG 1 1 ((a - b + 1) / 2) ((a + b + 1) / 2) := by
  set A := (a - b + 1) / 2
  set B := (a + b + 1) / 2
  have hAB : 1 < (A + B).re := by
    simp only [A, B, add_re, div_re, sub_re, one_re]; norm_num; linarith
  have e : ∀ θ ∈ Ioo (-(π / 2)) (π / 2), |1 / Real.cos θ ^ 2| • fourierBetaF 1 1 A B
      (Real.tan θ) = (Real.cos θ : ℂ) ^ (a - 1) * cexp (b * θ * I) := fun θ hθ => by
    rw [fourierBetaF_tan A B hθ, show A + B - 2 = a - 1 by simp only [A, B]; ring,
      show B - A = b by simp only [A, B]; ring]
  have hi := integrable_fourierBetaF (w := 1) (z := 1) one_pos one_pos hAB
  rw [← integrableOn_univ, ← tan_image, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo (fun θ hθ => hasDerivWithinAt_tan hθ) tan_injOn] at hi
  refine ⟨hi.congr_fun e measurableSet_Ioo, ?_⟩
  have h := fourierBeta_eq (w := 1) (z := 1) one_pos one_pos hAB
  rw [← setIntegral_univ, ← tan_image, integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo (fun θ hθ => hasDerivWithinAt_tan hθ) tan_injOn] at h
  rw [← h]
  exact (setIntegral_congr_fun measurableSet_Ioo e).symm

/-- DLMF's right side `π/(2^a aB(½(a+b+1), ½(a−b+1)))` in Gamma form. -/
theorem pi_div_beta_eq {a : ℂ} (ha : 0 < a.re) (b : ℂ) :
    π / 2 ^ a * (1 / (a * dlmfBeta ((a + b + 1) / 2) ((a - b + 1) / 2))) =
      π * fourierBetaG 1 1 ((a - b + 1) / 2) ((a + b + 1) / 2) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hs : (a + b + 1) / 2 + (a - b + 1) / 2 = a + 1 := by ring
  rw [dlmfBeta, hs, Complex.Gamma_add_one _ ha0, fourierBetaG,
    show (a - b + 1) / 2 + (a + b + 1) / 2 - 1 = a by ring,
    show 1 - (a - b + 1) / 2 - (a + b + 1) / 2 = -a by ring,
    show (1 : ℂ) + 1 = 2 by norm_num, cpow_neg]
  rw [show a * (Gamma ((a + b + 1) / 2) * Gamma ((a - b + 1) / 2) / (a * Gamma a)) =
    Gamma ((a + b + 1) / 2) * Gamma ((a - b + 1) / 2) / Gamma a by
      rw [mul_div_assoc', mul_div_mul_left _ _ ha0], one_div_div, div_eq_mul_inv,
    div_eq_mul_inv, mul_inv]
  ring

/-! ### 5.12.5 and 5.12.6 -/

/-- **DLMF 5.12.5**: `∫₀^{π/2} cos^{a−1}t cos(bt) dt = π/(2^a aB(½(a+b+1), ½(a−b+1)))`,
`ℜa > 0`, `b ∈ ℂ`. -/
theorem dlmf_5_12_5 {a : ℂ} (ha : 0 < a.re) (b : ℂ) :
    ∫ t in (0 : ℝ)..(π / 2), (Real.cos t : ℂ) ^ (a - 1) * Complex.cos (b * t) =
      π / 2 ^ a * (1 / (a * dlmfBeta ((a + b + 1) / 2) ((a - b + 1) / 2))) := by
  have hπ := Real.pi_pos
  set h : ℂ → ℝ → ℂ := fun b θ => (Real.cos θ : ℂ) ^ (a - 1) * cexp (b * θ * I)
  have hint : ∀ b, IntervalIntegrable (h b) volume (-(π / 2)) (π / 2) := fun b => by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
    exact (integral_cos_cpow_mul_cexp ha b).1
  have hfull : ∫ θ in (-(π / 2))..(π / 2), h b θ =
      2 * π * fourierBetaG 1 1 ((a - b + 1) / 2) ((a + b + 1) / 2) := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    exact (integral_cos_cpow_mul_cexp ha b).2
  have hneg : ∫ θ in (-(π / 2))..0, h b θ = ∫ θ in (0 : ℝ)..(π / 2), h (-b) θ := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π / 2) (fun θ => h b θ)
    rw [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [h, Real.cos_neg, ofReal_neg]
    ring_nf
  have h0mem : (0 : ℝ) ∈ uIcc (-(π / 2)) (π / 2) := by
    rw [mem_uIcc]; left; constructor <;> linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((hint b).mono_set (uIcc_subset_uIcc_left h0mem))
    ((hint b).mono_set (uIcc_subset_uIcc_right h0mem))
  rw [hneg, hfull] at hsplit
  have hcos : ∀ θ : ℝ, (Real.cos θ : ℂ) ^ (a - 1) * Complex.cos (b * θ) =
      (h b θ + h (-b) θ) / 2 := fun θ => by
    simp only [h, Complex.cos]
    ring_nf
  simp_rw [hcos]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((hint b).mono_set (uIcc_subset_uIcc_right h0mem))
    ((hint (-b)).mono_set (uIcc_subset_uIcc_right h0mem)), add_comm, hsplit, pi_div_beta_eq ha]
  ring

/-- **DLMF 5.12.6**: `∫₀^π sin^{a−1}t e^{ibt} dt = π e^{iπb/2}/(2^{a−1} aB(½(a+b+1), ½(a−b+1)))`,
`ℜa > 0`, `b ∈ ℂ`. -/
theorem dlmf_5_12_6 {a : ℂ} (ha : 0 < a.re) (b : ℂ) :
    ∫ t in (0 : ℝ)..π, (Real.sin t : ℂ) ^ (a - 1) * cexp (I * b * t) =
      π / 2 ^ (a - 1) * (cexp (I * π * b / 2) /
        (a * dlmfBeta ((a + b + 1) / 2) ((a - b + 1) / 2))) := by
  have hπ := Real.pi_pos
  have hshift := intervalIntegral.integral_comp_add_right
    (fun t : ℝ => (Real.sin t : ℂ) ^ (a - 1) * cexp (I * b * t)) (π / 2) (a := -(π / 2))
    (b := π / 2)
  rw [show -(π / 2) + π / 2 = 0 by ring, show π / 2 + π / 2 = π by ring] at hshift
  rw [← hshift]
  have e : ∀ s : ℝ, (Real.sin (s + π / 2) : ℂ) ^ (a - 1) * cexp (I * b * ((s + π / 2 : ℝ) : ℂ)) =
      cexp (I * π * b / 2) * ((Real.cos s : ℂ) ^ (a - 1) * cexp (b * s * I)) := fun s => by
    rw [Real.sin_add_pi_div_two, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by linarith),
    integral_Ioc_eq_integral_Ioo, (integral_cos_cpow_mul_cexp ha b).2,
    cpow_sub _ _ (two_ne_zero), cpow_one]
  have h := pi_div_beta_eq ha b
  rw [mul_one_div] at h
  rw [show (π : ℂ) / (2 ^ a / 2) * (cexp (I * π * b / 2) /
      (a * dlmfBeta ((a + b + 1) / 2) ((a - b + 1) / 2))) = 2 * cexp (I * π * b / 2) *
      (π / 2 ^ a / (a * dlmfBeta ((a + b + 1) / 2) ((a - b + 1) / 2))) by ring, h]
  ring

end Azurite.DLMF
