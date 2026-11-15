/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section7

/-!
# DLMF §6.7(ii): integral representations, sine and cosine integrals

Formalizations of <https://dlmf.nist.gov/6.7.ii>, equations 6.7.9–6.7.11.

For every complex `z`, `t ↦ Ein(z e^{±it})` has derivative `±i(1 − e^{−z e^{±it}})`
(`EinDeriv_mul_self`), so the integrals of `e^{−z e^{±it}}` over the quarter period are
`π/2 ± i(Ein(±iz) − Ein(z))` (`integral_exp_arc`); 6.7.9 and 6.7.10 are their half sum and half
difference, with `Ein(±iz) = Cin(z) ± i Si(z)` (`ein_I_mul_eq`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-- `Ein′(w) · w = 1 − e^{−w}` for every `w`. -/
theorem EinDeriv_mul_self (w : ℂ) : BZ.EinDeriv w * w = 1 - cexp (-w) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [BZ.EinDeriv]
  · rw [EinDeriv_of_ne hw]
    field_simp

/-- `Ein(±iz) = Cin(z) ± i Si(z)`. -/
theorem ein_I_mul_eq (z : ℂ) :
    ein (I * z) = Cin z + I * Si z ∧ ein (-I * z) = Cin z - I * Si z := by
  rw [Cin_eq, CinF, Si_eq, SiF]
  constructor <;> field_simp <;> ring

theorem exp_pi_div_two_mul_I' : cexp ((π / 2 : ℝ) * I) = I := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- The quarter-period integrals `∫_0^{π/2} e^{−z e^{±it}} dt = π/2 ± i(Ein(±iz) − Ein(z))`. -/
theorem integral_exp_arc (z : ℂ) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    ∫ t in (0 : ℝ)..π / 2, cexp (-(z * cexp (σ * t * I))) =
      π / 2 + σ * I * (ein (σ * I * z) - ein z) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- `d/dt Ein(z e^{iσt}) = iσ (1 − e^{−z e^{iσt}})`
  have hd : ∀ t ∈ uIcc (0 : ℝ) (π / 2), HasDerivAt (fun t : ℝ => ein (z * cexp (σ * t * I)))
      (σ * I * (1 - cexp (-(z * cexp (σ * t * I))))) t := by
    intro t _
    have h1 : HasDerivAt (fun v : ℂ => ein (z * cexp (σ * v * I)))
        (σ * I * (1 - cexp (-(z * cexp (σ * t * I))))) (t : ℂ) := by
      have he : HasDerivAt (fun v : ℂ => z * cexp (σ * v * I)) (z * (cexp (σ * t * I) * (σ * I)))
          (t : ℂ) := by
        have := (((hasDerivAt_id (t : ℂ)).const_mul σ).mul_const I).cexp.const_mul z
        simpa using this
      have := (hasDerivAt_ein _).comp (t : ℂ) he
      refine this.congr_deriv ?_
      rw [show BZ.EinDeriv (z * cexp (σ * t * I)) * (z * (cexp (σ * t * I) * (σ * I))) =
        σ * I * (BZ.EinDeriv (z * cexp (σ * t * I)) * (z * cexp (σ * t * I))) by ring,
        EinDeriv_mul_self]
    exact h1.comp_ofReal
  have hc : Continuous fun t : ℝ => σ * I * (1 - cexp (-(z * cexp (σ * t * I)))) := by
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)
  have hend : cexp (σ * ((π / 2 : ℝ) : ℂ) * I) = σ * I := by
    rcases hσ with rfl | rfl
    · rw [one_mul, exp_pi_div_two_mul_I', one_mul]
    · rw [show -1 * ((π / 2 : ℝ) : ℂ) * I = -(((π / 2 : ℝ) : ℂ) * I) by ring, exp_neg,
        exp_pi_div_two_mul_I', inv_I]
      ring
  rw [hend, ofReal_zero, mul_zero, zero_mul, exp_zero, mul_one,
    show z * (σ * I) = σ * I * z by ring] at hftc
  have hsplit : ∫ t in (0 : ℝ)..π / 2, σ * I * (1 - cexp (-(z * cexp (σ * t * I)))) =
      σ * I * (π / 2) - σ * I * ∫ t in (0 : ℝ)..π / 2, cexp (-(z * cexp (σ * t * I))) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const ((by fun_prop : Continuous fun t : ℝ =>
        cexp (-(z * cexp (σ * t * I)))).intervalIntegrable _ _), intervalIntegral.integral_const]
    simp only [sub_zero, real_smul, ofReal_div, mul_one]
    push_cast
    ring
  rw [hsplit] at hftc
  have hI : (σ * I) * (σ * I) = -1 := by
    rw [show σ * I * (σ * I) = σ * σ * (I * I) by ring, hσ2, I_mul_I, one_mul]
  linear_combination (σ * I) * hftc + ((∫ t in (0 : ℝ)..π / 2,
    cexp (-(z * cexp (σ * t * I)))) - (π / 2 : ℂ)) * hI

/-- `e^{−z cos t} cos(z sin t)` and `e^{−z cos t} sin(z sin t)` as half sum and half difference
of `e^{−z e^{±it}}`. -/
theorem exp_arc_decomp (z : ℂ) (t : ℝ) :
    cexp (-(z * Real.cos t)) * Complex.cos (z * Real.sin t) =
        (cexp (-(z * cexp (1 * t * I))) + cexp (-(z * cexp (-1 * t * I)))) / 2 ∧
      cexp (-(z * Real.cos t)) * Complex.sin (z * Real.sin t) =
        (cexp (-(z * cexp (-1 * t * I))) - cexp (-(z * cexp (1 * t * I)))) / (2 * I) := by
  have e1 : cexp (-(z * cexp (1 * t * I))) =
      cexp (-(z * Real.cos t)) * cexp (-(z * Real.sin t) * I) := by
    rw [one_mul, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← exp_add]
    ring_nf
  have e2 : cexp (-(z * cexp (-1 * t * I))) =
      cexp (-(z * Real.cos t)) * cexp ((z * Real.sin t) * I) := by
    rw [show (-1 : ℂ) * t * I = ((-t : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I, ← ofReal_cos,
      ← ofReal_sin, Real.cos_neg, Real.sin_neg, ← exp_add]
    push_cast
    ring_nf
  rw [e1, e2, Complex.cos, Complex.sin]
  constructor
  · ring
  · rw [eq_div_iff (mul_ne_zero two_ne_zero I_ne_zero)]
    linear_combination (cexp (-(z * ↑(Real.cos t))) * (cexp (-(z * ↑(Real.sin t)) * I) -
      cexp (z * ↑(Real.sin t) * I)) / 2 * 2) * I_sq

/-- **DLMF 6.7.9**: `si(z) = −∫_0^{π/2} e^{−z cos t} cos(z sin t) dt`, `z ∈ ℂ`. -/
theorem dlmf_6_7_9 (z : ℂ) :
    si z = -∫ t in (0 : ℝ)..π / 2, cexp (-(z * Real.cos t)) * Complex.cos (z * Real.sin t) := by
  have hp := integral_exp_arc z 1 (Or.inl rfl)
  have hm := integral_exp_arc z (-1) (Or.inr rfl)
  have hcp : Continuous fun t : ℝ => cexp (-(z * cexp (1 * t * I))) := by fun_prop
  have hcm : Continuous fun t : ℝ => cexp (-(z * cexp (-1 * t * I))) := by fun_prop
  rw [intervalIntegral.integral_congr fun t _ => (exp_arc_decomp z t).1,
    intervalIntegral.integral_div, intervalIntegral.integral_add (hcp.intervalIntegrable _ _)
      (hcm.intervalIntegrable _ _), hp, hm, (dlmf_6_2_10 z).2]
  obtain ⟨e1, e2⟩ := ein_I_mul_eq z
  rw [show (1 : ℂ) * I * z = I * z by ring, e1, show (-1 : ℂ) * I * z = -I * z by ring, e2]
  ring_nf
  rw [I_sq]
  ring

/-- **DLMF 6.7.10**: `Ein(z) − Cin(z) = ∫_0^{π/2} e^{−z cos t} sin(z sin t) dt`, `z ∈ ℂ`. -/
theorem dlmf_6_7_10 (z : ℂ) :
    ein z - Cin z =
      ∫ t in (0 : ℝ)..π / 2, cexp (-(z * Real.cos t)) * Complex.sin (z * Real.sin t) := by
  have hp := integral_exp_arc z 1 (Or.inl rfl)
  have hm := integral_exp_arc z (-1) (Or.inr rfl)
  have hcp : Continuous fun t : ℝ => cexp (-(z * cexp (1 * t * I))) := by fun_prop
  have hcm : Continuous fun t : ℝ => cexp (-(z * cexp (-1 * t * I))) := by fun_prop
  rw [intervalIntegral.integral_congr fun t _ => (exp_arc_decomp z t).2,
    intervalIntegral.integral_div, intervalIntegral.integral_sub (hcm.intervalIntegrable _ _)
      (hcp.intervalIntegrable _ _), hp, hm]
  obtain ⟨e1, e2⟩ := ein_I_mul_eq z
  rw [show (1 : ℂ) * I * z = I * z by ring, e1, show (-1 : ℂ) * I * z = -I * z by ring, e2]
  field_simp
  ring_nf

/-- `Cin(z)` as the integral of the continuous `cinC(zs) z`. -/
theorem cinC_mul_eq (z : ℂ) {s : ℝ} (hs : s ≠ 0) :
    cinC (z * s) * z = (1 - Complex.cos (z * s)) / s := by
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [cinC_of_ne (mul_ne_zero hz hs')]
    field_simp

theorem Cin_eq_integral_cinC (z : ℂ) : Cin z = ∫ s in (0 : ℝ)..1, cinC (z * s) * z := by
  rw [Cin]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [uIoc_of_le zero_le_one] at hs
  rw [cinC_mul_eq z hs.1.ne']
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · field_simp

/-- **DLMF 6.7.11**: `∫_0^1 (1 − e^{−at}) cos(bt)/t dt = ℜ Ein(a + ib) − Cin(b)`, `a, b ∈ ℝ`
(`Cin(b)` is real, `Cin_ofReal`). -/
theorem dlmf_6_7_11 (a b : ℝ) :
    ∫ t in (0 : ℝ)..1, (1 - Real.exp (-(a * t))) * Real.cos (b * t) / t =
      (ein (a + b * I)).re - (Cin b).re := by
  have hc1 : Continuous fun s : ℝ => BZ.EinDeriv (((a : ℂ) + b * I) * s) * (a + b * I) :=
    continuous_EinDeriv_mul_const _
  have hc2 : Continuous fun s : ℝ => cinC ((b : ℂ) * s) * b :=
    (continuous_cinC.comp (continuous_const.mul continuous_ofReal)).mul continuous_const
  have hi1 : IntervalIntegrable (fun x : ℝ => reCLM (BZ.EinDeriv (((a : ℂ) + b * I) * x) *
      (a + b * I))) volume 0 1 := (reCLM.continuous.comp hc1).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => reCLM (cinC ((b : ℂ) * x) * b)) volume 0 1 :=
    (reCLM.continuous.comp hc2).intervalIntegrable _ _
  rw [ein_eq_integral_EinDeriv, Cin_eq_integral_cinC, ← reCLM_apply, ← reCLM_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc1.intervalIntegrable _ _),
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc2.intervalIntegrable _ _),
    ← intervalIntegral.integral_sub hi1 hi2]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [uIoc_of_le zero_le_one] at hs
  simp only [reCLM_apply]
  rw [EinDeriv_mul_eq _ hs.1.ne', cinC_mul_eq _ hs.1.ne', div_ofReal_re, div_ofReal_re]
  simp [Complex.exp_re]
  rw [← ofReal_mul, ← ofReal_cos, ofReal_re, mul_comm b s]
  ring

end Azurite.DLMF
