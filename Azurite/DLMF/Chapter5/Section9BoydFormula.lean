/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9BoydCauchy

/-!
# DLMF §5.9(i): Boyd's formulas 5.9.11_1 and 5.9.11_2

Formalization of <https://dlmf.nist.gov/5.9>, equations 5.9.11_1 and 5.9.11_2 (added in DLMF
1.1.7, from Boyd (1994)), for `|ph z| < ½π`:

* `Γ*(z) = 1 − (2πi)⁻¹ ∫₀^∞ e^{−2πt} Γ*(t e^{iπ/2})/(t + iz) dt
    + (2πi)⁻¹ ∫₀^∞ e^{−2πt} Γ*(t e^{−iπ/2})/(t − iz) dt` (`dlmf_5_9_11_1`);
* `1/Γ*(z) = 1 − (2πi)⁻¹ ∫₀^∞ e^{−2πt} Γ*(t e^{iπ/2})/(t − iz) dt
    + (2πi)⁻¹ ∫₀^∞ e^{−2πt} Γ*(t e^{−iπ/2})/(t + iz) dt` (`dlmf_5_9_11_2`).

`Γ*` is the scaled gamma function of 5.11.3 (`scaledGamma`). Proof: `Γ* − 1` and `1/Γ* − 1`
satisfy the hypotheses of the half-plane Cauchy formula (`HalfPlaneDecay`, from Stieltjes' bound
and the behaviour at `0`); Cauchy's formula at `z` for one and at `−z` for the other, combined on
the imaginary axis, leave `Γ*(it) − 1/Γ*(−it) = e^{−2πt} Γ*(it)` by the reflection identity
`Γ*(it) Γ*(−it) = 1/(1 − e^{−2πt})`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-! ### `Γ* − 1` and `1/Γ* − 1` on the right half-plane -/

theorem scaledGamma_ne_zero {w : ℂ} (hw : 0 < w.re) : scaledGamma w ≠ 0 := by
  rw [scaledGamma_eq_exp hw]; exact Complex.exp_ne_zero _

theorem continuousAt_scaledGamma_I {y : ℝ} (hy : y ≠ 0) :
    ContinuousAt scaledGamma ((y : ℂ) * I) ∧ scaledGamma ((y : ℂ) * I) ≠ 0 := by
  have hslit : (y : ℂ) * I ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simpa using hy
  have hpole : ∀ m : ℕ, (y : ℂ) * I ≠ -m := fun m h => by
    have := congrArg im h; simp at this; exact hy this
  have h0 : (y : ℂ) * I ≠ 0 := slitPlane_ne_zero hslit
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hden : ((Real.sqrt (2 * π) : ℝ) : ℂ) * cexp (-((y : ℂ) * I)) *
      ((y : ℂ) * I) ^ ((y : ℂ) * I - 1 / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hs.ne') (Complex.exp_ne_zero _))
      (by rw [Ne, cpow_eq_zero_iff]; tauto)
  constructor
  · unfold scaledGamma
    refine (differentiableAt_Gamma _ hpole).continuousAt.div ?_ hden
    exact (continuousAt_const.mul (continuous_exp.continuousAt.comp continuousAt_id.neg)).mul
      (continuousAt_id.cpow (continuousAt_id.sub continuousAt_const) hslit)
  · unfold scaledGamma
    exact div_ne_zero (Gamma_ne_zero hpole) hden

theorem halfPlaneDecay_scaledGamma :
    ∃ C : ℝ, HalfPlaneDecay (fun w => scaledGamma w - 1) C ∧
      HalfPlaneDecay (fun w => (scaledGamma w)⁻¹ - 1) C := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_bound_scaledGamma_near_zero
  set C := max (1 / 3) (C₀ + 1) with hC
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hdiff : DifferentiableOn ℂ scaledGamma {w | 0 < w.re} := fun w hw =>
    ((differentiableOn_binetJ w hw).differentiableAt (hU.mem_nhds hw)).cexp
      |>.differentiableWithinAt.congr (fun v hv => scaledGamma_eq_exp hv)
        (scaledGamma_eq_exp hw)
  have hdiffinv : DifferentiableOn ℂ (fun w => (scaledGamma w)⁻¹) {w | 0 < w.re} := fun w hw =>
    ((hdiff w hw).differentiableAt (hU.mem_nhds hw)).inv (scaledGamma_ne_zero hw)
      |>.differentiableWithinAt
  have hrpow : ∀ w : ℂ, 0 < w.re → ‖w‖ ≤ 1 → 1 ≤ ‖w‖ ^ (-(1 / 2 : ℝ)) := fun w hw hw1 =>
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (lt_of_lt_of_le hw (Complex.re_le_norm w)) hw1
      (by norm_num)
  refine ⟨C, ⟨hCpos, hdiff.sub_const 1, fun w hw hw1 => ?_, fun w hw hw1 => ?_, fun y hy => ?_⟩,
    ⟨hCpos, hdiffinv.sub_const 1, fun w hw hw1 => ?_, fun w hw hw1 => ?_, fun y hy => ?_⟩⟩
  · refine (norm_scaledGamma_sub_one_le hw hw1).1.trans ?_
    rw [show 1 / (3 * ‖w‖) = (1 / 3) / ‖w‖ by field_simp]
    exact div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · have h := (hb w hw hw1).1
    have h1 := hrpow w hw hw1
    calc ‖scaledGamma w - 1‖ ≤ ‖scaledGamma w‖ + 1 := by
          have := norm_sub_le (scaledGamma w) 1; rwa [norm_one] at this
      _ ≤ C₀ * ‖w‖ ^ (-(1 / 2 : ℝ)) + 1 * ‖w‖ ^ (-(1 / 2 : ℝ)) := by linarith
      _ = (C₀ + 1) * ‖w‖ ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ C * ‖w‖ ^ (-(1 / 2 : ℝ)) := by gcongr; exact le_max_right _ _
  · exact ((continuousAt_scaledGamma_I hy).1.sub continuousAt_const)
  · refine (norm_scaledGamma_sub_one_le hw hw1).2.trans ?_
    rw [show 1 / (3 * ‖w‖) = (1 / 3) / ‖w‖ by field_simp]
    exact div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · have h := (hb w hw hw1).2
    have h1 := hrpow w hw hw1
    calc ‖(scaledGamma w)⁻¹ - 1‖ ≤ ‖(scaledGamma w)⁻¹‖ + 1 := by
          have := norm_sub_le (scaledGamma w)⁻¹ 1; rwa [norm_one] at this
      _ ≤ (C₀ + 1) * 1 := by linarith
      _ ≤ C * ‖w‖ ^ (-(1 / 2 : ℝ)) := by
          gcongr
          · exact le_max_right _ _
  · obtain ⟨hc, hne⟩ := continuousAt_scaledGamma_I hy
    exact (hc.inv₀ hne).sub continuousAt_const

/-! ### Combining Cauchy's formulas -/

theorem integral_eq_Ioi_add_comp_neg {H : ℝ → ℂ} (hH : Integrable H) :
    ∫ y, H y = (∫ t in Ioi (0 : ℝ), H t) + ∫ t in Ioi (0 : ℝ), H (-t) := by
  rw [integral_comp_neg_Ioi, neg_zero, add_comm,
    intervalIntegral.integral_Iic_add_Ioi hH.integrableOn hH.integrableOn]

/-- With `P − 1`, `Q − 1` satisfying the half-plane hypotheses, `ℜz > 0`:
`∫₀^∞ (P(it) − Q(−it))/(it − z) dt + ∫₀^∞ (P(−it) − Q(it))/(−it − z) dt = −2π(P(z) − 1)`. -/
theorem boyd_aux {P Q : ℂ → ℂ} {C : ℝ} (hP : HalfPlaneDecay (fun w => P w - 1) C)
    (hQ : HalfPlaneDecay (fun w => Q w - 1) C) {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), (P ((t : ℂ) * I) - Q (-((t : ℂ) * I))) / ((t : ℂ) * I - z)) +
      (∫ t in Ioi (0 : ℝ), (P (-((t : ℂ) * I)) - Q ((t : ℂ) * I)) / (-((t : ℂ) * I) - z)) =
      -(2 * π * (P z - 1)) := by
  have hA := integral_halfPlane_inside hP hz
  have hB := integral_halfPlane_outside hQ (z := -z) (by simp; linarith)
  have hAi := integrable_halfPlane hP hz.ne'
  have hBi := integrable_halfPlane hQ (z := -z) (by simp; linarith)
  rw [integral_eq_Ioi_add_comp_neg hAi] at hA
  rw [integral_eq_Ioi_add_comp_neg hBi] at hB
  have hA1 := hAi.integrableOn (s := Ioi 0)
  have hA2 := (hAi.comp_neg).integrableOn (s := Ioi 0)
  have hB1 := hBi.integrableOn (s := Ioi 0)
  have hB2 := (hBi.comp_neg).integrableOn (s := Ioi 0)
  have e1 : ∫ t in Ioi (0 : ℝ), (P ((t : ℂ) * I) - Q (-((t : ℂ) * I))) / ((t : ℂ) * I - z) =
      (∫ t in Ioi (0 : ℝ), (P ((t : ℂ) * I) - 1) / ((t : ℂ) * I - z)) +
        ∫ t in Ioi (0 : ℝ), (Q (((-t : ℝ) : ℂ) * I) - 1) / (((-t : ℝ) : ℂ) * I - -z) := by
    rw [← integral_add hA1 hB2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have h1 : (t : ℂ) * I - z ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    have h2 : ((-t : ℝ) : ℂ) * I - -z = -((t : ℂ) * I - z) := by push_cast; ring
    rw [h2, show (((-t : ℝ) : ℂ) * I) = -((t : ℂ) * I) by push_cast; ring]
    field_simp
    ring
  have e2 : ∫ t in Ioi (0 : ℝ), (P (-((t : ℂ) * I)) - Q ((t : ℂ) * I)) / (-((t : ℂ) * I) - z) =
      (∫ t in Ioi (0 : ℝ), (P (((-t : ℝ) : ℂ) * I) - 1) / (((-t : ℝ) : ℂ) * I - z)) +
        ∫ t in Ioi (0 : ℝ), (Q ((t : ℂ) * I) - 1) / ((t : ℂ) * I - -z) := by
    rw [← integral_add hA2 hB1]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have h1 : -((t : ℂ) * I) - z ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    have h2 : (t : ℂ) * I - -z = -(-((t : ℂ) * I) - z) := by ring
    rw [h2, show (((-t : ℝ) : ℂ) * I) = -((t : ℂ) * I) by push_cast; ring]
    field_simp
    ring
  rw [e1, e2]
  linear_combination hA + hB

/-! ### The formulas -/

theorem scaledGamma_inv_I {t : ℝ} (ht : 0 < t) :
    (scaledGamma (-((t : ℂ) * I)))⁻¹ = (1 - cexp (-(2 * π * t))) * scaledGamma ((t : ℂ) * I) ∧
      (scaledGamma ((t : ℂ) * I))⁻¹ =
        (1 - cexp (-(2 * π * t))) * scaledGamma (-((t : ℂ) * I)) := by
  have h := scaledGamma_mul_scaledGamma_neg ht
  have hn1 := (continuousAt_scaledGamma_I ht.ne').2
  have hn2 : scaledGamma (-((t : ℂ) * I)) ≠ 0 := by
    have := (continuousAt_scaledGamma_I (y := -t) (by linarith)).2
    rwa [show ((-t : ℝ) : ℂ) * I = -((t : ℂ) * I) by push_cast; ring] at this
  have hq : 1 - cexp (-(2 * π * (t : ℂ))) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    exact mul_ne_zero hn1 hn2 h
  have hm1 : (1 - cexp (-(2 * π * (t : ℂ)))) * scaledGamma ((t : ℂ) * I) *
      scaledGamma (-((t : ℂ) * I)) = 1 := by
    rw [mul_assoc, h]; field_simp
  have hm2 : (1 - cexp (-(2 * π * (t : ℂ)))) * scaledGamma (-((t : ℂ) * I)) *
      scaledGamma ((t : ℂ) * I) = 1 := by
    rw [mul_assoc, mul_comm (scaledGamma _), h]; field_simp
  exact ⟨(eq_inv_of_mul_eq_one_left hm1).symm, (eq_inv_of_mul_eq_one_left hm2).symm⟩

theorem cexp_pi_div_two_I_eq : cexp (π / 2 * I) = I ∧ cexp (-(π / 2 * I)) = -I := by
  refine ⟨exp_pi_div_two_mul_I, ?_⟩
  rw [Complex.exp_neg, exp_pi_div_two_mul_I, inv_I]

/-- **DLMF 5.9.11_1** (Boyd): for `|ph z| < ½π`,
`Γ*(z) = 1 − (2πi)⁻¹ ∫₀^∞ e^{−2πt} Γ*(t e^{iπ/2})/(t + iz) dt
  + (2πi)⁻¹ ∫₀^∞ e^{−2πt} Γ*(t e^{−iπ/2})/(t − iz) dt`. -/
theorem dlmf_5_9_11_1 {z : ℂ} (hz : 0 < z.re) :
    scaledGamma z = 1 - 1 / (2 * π * I) * (∫ t in Ioi (0 : ℝ),
      cexp (-(2 * π * t)) * scaledGamma (t * cexp (π / 2 * I)) / (t + I * z)) +
      1 / (2 * π * I) * ∫ t in Ioi (0 : ℝ),
        cexp (-(2 * π * t)) * scaledGamma (t * cexp (-(π / 2 * I))) / (t - I * z) := by
  obtain ⟨C, h1, h2⟩ := halfPlaneDecay_scaledGamma
  have hb := boyd_aux (P := scaledGamma) (Q := fun w => (scaledGamma w)⁻¹) h1 h2 hz
  rw [cexp_pi_div_two_I_eq.1, cexp_pi_div_two_I_eq.2]
  have hA : ∫ t in Ioi (0 : ℝ), (scaledGamma ((t : ℂ) * I) - (scaledGamma (-((t : ℂ) * I)))⁻¹) /
      ((t : ℂ) * I - z) = -I * ∫ t in Ioi (0 : ℝ),
        cexp (-(2 * π * t)) * scaledGamma (t * I) / (t + I * z) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have hd : (t : ℂ) + I * z ≠ 0 := fun h => by
      have := congrArg im h; simp at this; linarith
    rw [(scaledGamma_inv_I ht').1, show (t : ℂ) * I - z = I * ((t : ℂ) + I * z) by
      ring_nf; rw [I_sq]; ring]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hB : ∫ t in Ioi (0 : ℝ), (scaledGamma (-((t : ℂ) * I)) - (scaledGamma ((t : ℂ) * I))⁻¹) /
      (-((t : ℂ) * I) - z) = I * ∫ t in Ioi (0 : ℝ),
        cexp (-(2 * π * t)) * scaledGamma (t * -I) / (t - I * z) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have hd : (t : ℂ) - I * z ≠ 0 := fun h => by
      have := congrArg im h; simp at this; linarith
    rw [(scaledGamma_inv_I ht').2, show -((t : ℂ) * I) - z = -I * ((t : ℂ) - I * z) by
      ring_nf; rw [I_sq]; ring, show (t : ℂ) * -I = -((t : ℂ) * I) by ring]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hA, hB] at hb
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  generalize (∫ t in Ioi (0 : ℝ), cexp (-(2 * π * t)) * scaledGamma (t * I) / (t + I * z)) = A
    at hb ⊢
  generalize (∫ t in Ioi (0 : ℝ), cexp (-(2 * π * t)) * scaledGamma (t * -I) / (t - I * z)) = B
    at hb ⊢
  have hAB : B - A = 2 * π * I * (scaledGamma z - 1) := by
    linear_combination (-I) * hb + (B - A) * I_sq
  have hd : (2 * π * I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero
  rw [show 1 - 1 / (2 * π * I) * A + 1 / (2 * π * I) * B = 1 + (B - A) / (2 * π * I) by ring,
    hAB, mul_div_cancel_left₀ _ hd]
  ring

/-- **DLMF 5.9.11_2** (Boyd): for `|ph z| < ½π`,
`1/Γ*(z) = 1 − (2πi)⁻¹ ∫₀^∞ e^{−2πt} Γ*(t e^{iπ/2})/(t − iz) dt
  + (2πi)⁻¹ ∫₀^∞ e^{−2πt} Γ*(t e^{−iπ/2})/(t + iz) dt`. -/
theorem dlmf_5_9_11_2 {z : ℂ} (hz : 0 < z.re) :
    1 / scaledGamma z = 1 - 1 / (2 * π * I) * (∫ t in Ioi (0 : ℝ),
      cexp (-(2 * π * t)) * scaledGamma (t * cexp (π / 2 * I)) / (t - I * z)) +
      1 / (2 * π * I) * ∫ t in Ioi (0 : ℝ),
        cexp (-(2 * π * t)) * scaledGamma (t * cexp (-(π / 2 * I))) / (t + I * z) := by
  obtain ⟨C, h1, h2⟩ := halfPlaneDecay_scaledGamma
  have hb := boyd_aux (P := fun w => (scaledGamma w)⁻¹) (Q := scaledGamma) h2 h1 hz
  rw [cexp_pi_div_two_I_eq.1, cexp_pi_div_two_I_eq.2]
  have hA : ∫ t in Ioi (0 : ℝ), ((scaledGamma ((t : ℂ) * I))⁻¹ - scaledGamma (-((t : ℂ) * I))) /
      ((t : ℂ) * I - z) = I * ∫ t in Ioi (0 : ℝ),
        cexp (-(2 * π * t)) * scaledGamma (t * -I) / (t + I * z) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have hd : (t : ℂ) + I * z ≠ 0 := fun h => by
      have := congrArg im h; simp at this; linarith
    rw [(scaledGamma_inv_I ht').2, show (t : ℂ) * I - z = I * ((t : ℂ) + I * z) by
      ring_nf; rw [I_sq]; ring, show (t : ℂ) * -I = -((t : ℂ) * I) by ring]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hB : ∫ t in Ioi (0 : ℝ), ((scaledGamma (-((t : ℂ) * I)))⁻¹ - scaledGamma ((t : ℂ) * I)) /
      (-((t : ℂ) * I) - z) = -I * ∫ t in Ioi (0 : ℝ),
        cexp (-(2 * π * t)) * scaledGamma (t * I) / (t - I * z) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have hd : (t : ℂ) - I * z ≠ 0 := fun h => by
      have := congrArg im h; simp at this; linarith
    rw [(scaledGamma_inv_I ht').1, show -((t : ℂ) * I) - z = -I * ((t : ℂ) - I * z) by
      ring_nf; rw [I_sq]; ring]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hA, hB] at hb
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  generalize (∫ t in Ioi (0 : ℝ), cexp (-(2 * π * t)) * scaledGamma (t * I) / (t - I * z)) = A
    at hb ⊢
  generalize (∫ t in Ioi (0 : ℝ), cexp (-(2 * π * t)) * scaledGamma (t * -I) / (t + I * z)) = B
    at hb ⊢
  have hAB : B - A = 2 * π * I * ((scaledGamma z)⁻¹ - 1) := by
    linear_combination (-I) * hb + (B - A) * I_sq
  have hd : (2 * π * I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero
  rw [show 1 - 1 / (2 * π * I) * A + 1 / (2 * π * I) * B = 1 + (B - A) / (2 * π * I) by ring,
    hAB, mul_div_cancel_left₀ _ hd, one_div]
  ring

end Azurite.DLMF
