/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9Boyd

/-!
# DLMF §5.6(ii): 5.6.9

Formalization of <https://dlmf.nist.gov/5.6#E9>:
`|Γ(z)| ≤ (2π)^{1/2} |z|^{x−½} e^{−π|y|/2} exp(1/(6|z|))` for `ℜz ≥ 0`, `z ≠ 0`.

For `ℜz > 0`: `Γ(z) = √(2π) e^{−z} z^{z−½} Γ*(z)`, `Γ*(z) = e^{J(z)}` (`scaledGamma_eq_exp`) with
Stieltjes' bound `|J(z)| ≤ 1/(6|z|)` (`norm_binetJ_le_inv`), and
`|z^{z−½}| = |z|^{x−½} e^{−y ph z}` with `y ph z + x ≥ π|y|/2` (`pi_mul_abs_im_le`, from
`ψ cos ψ ≤ sin ψ` on `[0, π/2]`). The imaginary axis follows by continuity.
-/

open Complex Filter Topology Set
open scoped Real

namespace Azurite.DLMF

theorem mul_cos_le_sin {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π / 2) : ψ * Real.cos ψ ≤ Real.sin ψ := by
  rcases h1.lt_or_eq with h | h
  · have hc : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩
    have := Real.le_tan h0 h
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at this
    exact this
  · rw [h, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp

/-- `π|y|/2 ≤ y ph z + x` for `ℜz ≥ 0`. -/
theorem pi_mul_abs_im_le {z : ℂ} (hz : 0 ≤ z.re) :
    π * |z.im| / 2 ≤ z.im * arg z + z.re := by
  have ht := Complex.abs_arg_le_pi_div_two_iff.mpr hz
  rw [← Complex.norm_mul_sin_arg, ← Complex.norm_mul_cos_arg, abs_mul, abs_norm]
  set θ := arg z
  have hr := norm_nonneg z
  have key : (π / 2 - |θ|) * Real.sin |θ| ≤ Real.cos |θ| := by
    have := mul_cos_le_sin (ψ := π / 2 - |θ|) (by linarith) (by linarith [abs_nonneg θ])
    rwa [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at this
  have hs : |Real.sin θ| = Real.sin |θ| ∧ Real.sin θ * θ = Real.sin |θ| * |θ| ∧
      Real.cos θ = Real.cos |θ| := by
    have hsn : 0 ≤ Real.sin |θ| := Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg θ)
      (by linarith [Real.pi_pos])
    rcases abs_cases θ with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact ⟨abs_of_nonneg (h ▸ hsn), rfl, rfl⟩
    · rw [h, Real.sin_neg] at hsn
      rw [h, Real.sin_neg, Real.cos_neg]
      exact ⟨abs_of_nonpos (by linarith), by ring, rfl⟩
  obtain ⟨h1, h2, h3⟩ := hs
  rw [h1, h3, mul_assoc, h2]
  nlinarith [mul_le_mul_of_nonneg_left key hr]

/-- The bound for `ℜz > 0`. -/
theorem norm_Gamma_le_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ≤ Real.sqrt (2 * π) * ‖z‖ ^ (z.re - 1 / 2) * Real.exp (-(π * |z.im|) / 2) *
      Real.exp (1 / 6 * ‖z‖⁻¹) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz; exact lt_irrefl 0 hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hsq : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hcp : z ^ (z - 1 / 2) ≠ 0 := by
    rw [cpow_def_of_ne_zero hz0]; exact Complex.exp_ne_zero _
  have hden : (Real.sqrt (2 * π) : ℂ) * cexp (-z) * z ^ (z - 1 / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hsq.ne') (Complex.exp_ne_zero _)) hcp
  have hΓ : Gamma z = (Real.sqrt (2 * π) : ℂ) * cexp (-z) * z ^ (z - 1 / 2) *
      cexp (binetJ z) := by
    rw [← scaledGamma_eq_exp hz, scaledGamma, mul_div_assoc', mul_comm, mul_div_assoc,
      div_self hden, mul_one]
  have hJ : (binetJ z).re ≤ 1 / 6 * ‖z‖⁻¹ := by
    have := norm_binetJ_le_inv hz
    rw [show 1 / 6 * ‖z‖⁻¹ = 1 / (6 * ‖z‖) by field_simp]
    exact (Complex.re_le_norm _).trans this
  have harg := pi_mul_abs_im_le hz.le
  rw [hΓ, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
    Complex.norm_cpow_of_ne_zero hz0, Complex.norm_real, Real.norm_of_nonneg hsq.le]
  have hre : (z - 1 / 2).re = z.re - 1 / 2 := by simp
  have him : (z - 1 / 2).im = z.im := by simp
  rw [hre, him, Complex.neg_re]
  have hp := Real.rpow_pos_of_pos hzn (z.re - 1 / 2)
  calc Real.sqrt (2 * π) * Real.exp (-z.re) * (‖z‖ ^ (z.re - 1 / 2) /
        Real.exp (arg z * z.im)) * Real.exp (binetJ z).re
      = Real.sqrt (2 * π) * ‖z‖ ^ (z.re - 1 / 2) *
          Real.exp (-z.re - arg z * z.im + (binetJ z).re) := by
        rw [Real.exp_add, Real.exp_sub]; field_simp
    _ ≤ Real.sqrt (2 * π) * ‖z‖ ^ (z.re - 1 / 2) *
          Real.exp (-(π * |z.im|) / 2 + 1 / 6 * ‖z‖⁻¹) := by
        gcongr; linarith
    _ = _ := by rw [Real.exp_add, ← mul_assoc]

/-- **DLMF 5.6.9**: `|Γ(z)| ≤ (2π)^{1/2} |z|^{x−½} e^{−π|y|/2} exp(1/(6|z|))` for `ℜz ≥ 0`,
`z ≠ 0`. -/
theorem dlmf_5_6_9 {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    ‖Gamma z‖ ≤ Real.sqrt (2 * π) * ‖z‖ ^ (z.re - 1 / 2) * Real.exp (-(π * |z.im|) / 2) *
      Real.exp (1 / 6 * ‖z‖⁻¹) := by
  rcases hz.lt_or_eq with h | h
  · exact norm_Gamma_le_of_re_pos h
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hcΓ : ContinuousAt (fun w => ‖Gamma w‖) z :=
    (differentiableAt_Gamma z fun m hm => hz0 (by
      rw [hm] at h ⊢; simp at h; simp [h])).continuousAt.norm
  have h1 : ContinuousAt (fun w : ℂ => ‖w‖ ^ (w.re - 1 / 2)) z :=
    ContinuousAt.rpow continuous_norm.continuousAt
      (Complex.continuous_re.continuousAt.sub continuousAt_const) (Or.inl hn)
  have h2 : ContinuousAt (fun w : ℂ => ‖w‖⁻¹) z := continuous_norm.continuousAt.inv₀ hn
  have hcR : ContinuousAt (fun w : ℂ => Real.sqrt (2 * π) * ‖w‖ ^ (w.re - 1 / 2) *
      Real.exp (-(π * |w.im|) / 2) * Real.exp (1 / 6 * ‖w‖⁻¹)) z := by
    fun_prop
  have hpath : Tendsto (fun ε : ℝ => z + ε) (𝓝[>] 0) (𝓝 z) := by
    have hc : Continuous (fun ε : ℝ => z + ε) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  refine le_of_tendsto_of_tendsto (hcΓ.tendsto.comp hpath) (hcR.tendsto.comp hpath)
    (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  exact norm_Gamma_le_of_re_pos (by simp [← h]; exact hε)

/-- `|Γ(z)| = √(2π) |z|^{x−½} exp(−x − y ph z + ℜJ(z))` for `ℜz > 0`. -/
theorem norm_Gamma_eq_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ = Real.sqrt (2 * π) * ‖z‖ ^ (z.re - 1 / 2) *
      Real.exp (-z.re - arg z * z.im + (binetJ z).re) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz; exact lt_irrefl 0 hz
  have hsq : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hcp : z ^ (z - 1 / 2) ≠ 0 := by
    rw [cpow_def_of_ne_zero hz0]; exact Complex.exp_ne_zero _
  have hden : (Real.sqrt (2 * π) : ℂ) * cexp (-z) * z ^ (z - 1 / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hsq.ne') (Complex.exp_ne_zero _)) hcp
  have hΓ : Gamma z = (Real.sqrt (2 * π) : ℂ) * cexp (-z) * z ^ (z - 1 / 2) *
      cexp (binetJ z) := by
    rw [← scaledGamma_eq_exp hz, scaledGamma, mul_div_assoc', mul_comm, mul_div_assoc,
      div_self hden, mul_one]
  rw [hΓ, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
    Complex.norm_cpow_of_ne_zero hz0, Complex.norm_real, Real.norm_of_nonneg hsq.le]
  have hre : (z - 1 / 2).re = z.re - 1 / 2 := by simp
  have him : (z - 1 / 2).im = z.im := by simp
  rw [hre, him, Complex.neg_re, Real.exp_add, Real.exp_sub]
  field_simp

/-- Lower bound for `|Γ|` in `ℜw ≥ 1`, `ℑw ≥ 0`:
`|Γ(w)|⁻¹ ≤ e^{1/6} (2π)^{−1/2} |w|^{½−ℜw} e^{ℜw + πℑw/2}`. -/
theorem norm_inv_Gamma_le {w : ℂ} (hw : 1 ≤ w.re) (him : 0 ≤ w.im) :
    ‖(Gamma w)⁻¹‖ ≤ Real.exp (1 / 6) / Real.sqrt (2 * π) * ‖w‖ ^ (1 / 2 - w.re) *
      Real.exp (w.re + π / 2 * w.im) := by
  have hw0 : 0 < w.re := by linarith
  have hwn : 1 ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  have hsq : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have harg : 0 ≤ arg w ∧ arg w ≤ π / 2 :=
    ⟨Complex.arg_nonneg_iff.mpr him, (abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hw0.le)).2⟩
  have hJ : -(1 / 6) ≤ (binetJ w).re := by
    have h1 := norm_binetJ_le_inv hw0
    have h2 : 1 / (6 * ‖w‖) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have := Complex.abs_re_le_norm (binetJ w)
    linarith [(abs_le.mp this).1]
  have hE : -w.re - π / 2 * w.im - 1 / 6 ≤ -w.re - arg w * w.im + (binetJ w).re := by
    nlinarith [mul_le_mul_of_nonneg_right harg.2 him]
  rw [norm_inv, norm_Gamma_eq_of_re_pos hw0]
  have hp := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < ‖w‖) (w.re - 1 / 2)
  have hp' : ‖w‖ ^ (1 / 2 - w.re) = (‖w‖ ^ (w.re - 1 / 2))⁻¹ := by
    rw [← Real.rpow_neg (by linarith)]; ring_nf
  rw [hp', mul_inv, mul_inv]
  have hlow : Real.exp (-w.re - π / 2 * w.im - 1 / 6) ≤
      Real.exp (-w.re - arg w * w.im + (binetJ w).re) := Real.exp_le_exp.mpr hE
  have hpos := Real.exp_pos (-w.re - π / 2 * w.im - 1 / 6)
  calc (Real.sqrt (2 * π))⁻¹ * (‖w‖ ^ (w.re - 1 / 2))⁻¹ *
        (Real.exp (-w.re - arg w * w.im + (binetJ w).re))⁻¹
      ≤ (Real.sqrt (2 * π))⁻¹ * (‖w‖ ^ (w.re - 1 / 2))⁻¹ *
        (Real.exp (-w.re - π / 2 * w.im - 1 / 6))⁻¹ := by
        gcongr
    _ = _ := by
        rw [show -w.re - π / 2 * w.im - 1 / 6 = -(w.re + π / 2 * w.im) + -(1 / 6) by ring,
          Real.exp_add, Real.exp_neg, Real.exp_neg]
        field_simp

end Azurite.DLMF
