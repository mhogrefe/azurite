/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11BoydRotate
import Azurite.DLMF.Chapter5.Section11RatioWatson
import Azurite.DLMF.Chapter5.Section12Loop
import Azurite.DLMF.Chapter2.Section1BorelRitt

/-!
# DLMF 5.6.8: `|Γ(z + a)/Γ(z + b)| ≤ |z|^{a−b}`

Formalization of <https://dlmf.nist.gov/5.6.E8>: for `b − a ≥ 1`, `a ≥ 0` and `ℜz > 0`,
`|Γ(z + a)/Γ(z + b)| ≤ 1/|z|^{b−a}` (`dlmf_5_6_8`).

Proof. Put `w = z + a`, `c = b − a ≥ 1`. Euler's beta integral (5.12.1) with `s = e^{−u}` gives
`Γ(w)/Γ(w + c) = Γ(c)⁻¹ ∫₀^∞ e^{−wu}(1 − e^{−u})^{c−1} du` (`gamma_ratio_eq_integral`). The
integrand is holomorphic on `ℜu > 0` with `|·| ≤ e^{−ℜw·r} r^{c−1}` on the sector between `ph u = 0`
and `ph u = −ph w` (because `|1 − e^{−u}| ≤ |u|` for `ℜu ≥ 0`, `norm_one_sub_exp_neg_le`), so the
ray can be rotated to `u = re^{−i ph w}` (`integral_rotRay_eq`), where `wu = |w|r`. Hence
`|Γ(w)/Γ(w + c)| ≤ Γ(c)⁻¹ ∫₀^∞ e^{−|w|r} r^{c−1} dr = |w|^{−c} ≤ |z|^{−c}`, since `|w| ≥ |z|`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- The integrand `e^{−wu}(1 − e^{−u})^{c−1}`. -/
noncomputable def ratioIntegrand (w : ℂ) (c : ℝ) (u : ℂ) : ℂ :=
  cexp (-(w * u)) * (1 - cexp (-u)) ^ ((c - 1 : ℝ) : ℂ)

theorem one_sub_exp_neg_mem_slitPlane {u : ℂ} (hu : 0 < u.re) : 1 - cexp (-u) ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have h1 := re_le_norm (cexp (-u))
  have h2 : ‖cexp (-u)‖ < 1 := by
    rw [Complex.norm_exp, neg_re]
    calc Real.exp (-u.re) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  simp only [sub_re, one_re]
  linarith

/-- `Γ(w)/Γ(w + c) = Γ(c)⁻¹ ∫₀^∞ e^{−wu}(1 − e^{−u})^{c−1} du`. -/
theorem gamma_ratio_eq_integral {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    Gamma w / Gamma (w + c) =
      (Gamma c)⁻¹ * ∫ u in Ioi (0 : ℝ), ratioIntegrand w c u := by
  have hc' : 0 < (c : ℂ).re := by simpa using hc
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hw hc'
  have hG0 : Gamma (w + c) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGc : Gamma (c : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hc'
  have hB : Complex.betaIntegral w c = ∫ u in Ioi (0 : ℝ), ratioIntegrand w c u := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioo_eq_integral_exp_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [ratioIntegrand, Complex.real_smul]
    rw [cpow_pos_eq (Real.exp_pos _), Real.log_exp, ofReal_exp, ofReal_neg,
      show ((c : ℂ) - 1) = ((c - 1 : ℝ) : ℂ) by push_cast; ring, ← mul_assoc,
      ← Complex.exp_add]
    congr 2
    ring
  rw [← hB, div_eq_iff hG0]
  field_simp
  linear_combination hbeta

/-- `r^s ≤ 1 + r^p` for `0 ≤ s ≤ p`, `r ≥ 0`. -/
theorem rpow_le_one_add_pow {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) {p : ℕ} (hp : s ≤ p) :
    r ^ s ≤ 1 + r ^ p := by
  rcases le_total r 1 with h | h
  · have := Real.rpow_le_one hr h hs
    linarith [pow_nonneg hr p]
  · have := Real.rpow_le_rpow_of_exponent_le h hp
    rw [Real.rpow_natCast] at this
    linarith

/-- The bound on the sector: `|e^{−wu}(1 − e^{−u})^{c−1}| ≤ e^{−ℜ(wu)}|u|^{c−1}`, `ℜu ≥ 0`. -/
theorem norm_ratioIntegrand_le {w u : ℂ} (hu : 0 < u.re) {c : ℝ} (hc : 1 ≤ c) :
    ‖ratioIntegrand w c u‖ ≤ Real.exp (-(w * u).re) * ‖u‖ ^ (c - 1) := by
  have h0 : 1 - cexp (-u) ≠ 0 := slitPlane_ne_zero (one_sub_exp_neg_mem_slitPlane hu)
  rw [ratioIntegrand, norm_mul, Complex.norm_exp, neg_re, norm_cpow_of_ne_zero h0]
  simp only [ofReal_re, ofReal_im, mul_zero, Real.exp_zero, div_one]
  gcongr
  exact norm_one_sub_exp_neg_le hu.le

/-- For `ψ` between `0` and `−ph w`, `ℜ(w e^{iψ}) ≥ ℜw` and `cos ψ > 0`. -/
theorem sector_facts {w : ℂ} (hw : 0 < w.re) {ψ : ℝ} (hψ : ψ ∈ uIcc 0 (-arg w)) :
    w.re ≤ (w * cexp (ψ * I)).re ∧ 0 < Real.cos ψ := by
  have hφ : |arg w| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have hbd : |arg w + ψ| ≤ |arg w| ∧ |ψ| ≤ |arg w| := by
    rw [mem_uIcc] at hψ
    rcases hψ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> (rw [abs_le]; constructor <;> cases abs_cases (arg w) <;> linarith)
    · constructor <;> (rw [abs_le]; constructor <;> cases abs_cases (arg w) <;> linarith)
  have hπ := Real.pi_pos
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← norm_mul_cos_arg w]
    conv_rhs => rw [← norm_mul_exp_arg_mul_I w]
    rw [mul_assoc, ← Complex.exp_add, show (arg w : ℂ) * I + ψ * I = ((arg w + ψ : ℝ) : ℂ) * I by
      push_cast; ring, re_ofReal_mul, exp_ofReal_mul_I_re]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← Real.cos_abs (arg w + ψ), ← Real.cos_abs (arg w)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hbd.1
  · rw [← Real.cos_abs]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg ψ], by linarith [hbd.2]⟩

/-- `|Γ(w)/Γ(w + c)| ≤ |w|^{−c}` for `ℜw > 0`, `c ≥ 1`. -/
theorem norm_gamma_ratio_le {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 1 ≤ c) :
    ‖Gamma w / Gamma (w + c)‖ ≤ ‖w‖ ^ (-c) := by
  have hc0 : 0 < c := by linarith
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr fun h => by rw [h] at hw; simp at hw
  set f := ratioIntegrand w c
  set p := Nat.ceil (c - 1)
  have hu : ∀ r ψ : ℝ, 0 < r → ψ ∈ uIcc 0 (-arg w) → 0 < ((r : ℂ) * cexp (ψ * I)).re :=
    fun r ψ hr hψ => by
      rw [re_ofReal_mul, exp_ofReal_mul_I_re]; exact mul_pos hr (sector_facts hw hψ).2
  have hrot := integral_rotRay_eq (f := f) (θ := 0) (θ' := -arg w) (C := 1) (c := w.re) (p := p)
    (fun r ψ hr hψ => by
      have h := hu r ψ hr hψ
      have h1 : DifferentiableAt ℂ (fun u : ℂ => cexp (-(w * u))) ((r : ℂ) * cexp (ψ * I)) := by
        fun_prop
      have h2 : DifferentiableAt ℂ (fun u : ℂ => (1 - cexp (-u)) ^ ((c - 1 : ℝ) : ℂ))
          ((r : ℂ) * cexp (ψ * I)) :=
        (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1 - cexp (-u)) _).cpow_const
          (one_sub_exp_neg_mem_slitPlane h)
      exact h1.mul h2)
    hw
    (fun r ψ hr hψ => by
      refine (norm_ratioIntegrand_le (hu r ψ hr hψ) hc).trans ?_
      rw [norm_ofReal_mul_cexp hr.le, one_mul, mul_comm]
      refine mul_le_mul (rpow_le_one_add_pow hr.le (by linarith) (Nat.le_ceil _))
        (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
      have := (sector_facts hw hψ).1
      rw [show w * ((r : ℂ) * cexp (ψ * I)) = r * (w * cexp (ψ * I)) by ring, re_ofReal_mul]
      nlinarith)
  simp only [rotRay, ofReal_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at hrot
  -- on the rotated ray `wu = |w|r`
  have hpt : ∀ r : ℝ, 0 < r → ‖rotRay f (-arg w) r‖ ≤ r ^ (c - 1) * Real.exp (-(‖w‖ * r)) :=
    fun r hr => by
      have hψ : -arg w ∈ uIcc 0 (-arg w) := right_mem_uIcc
      rw [rotRay, norm_mul, norm_exp_ofReal_mul_I, one_mul]
      refine (norm_ratioIntegrand_le (hu r _ hr hψ) hc).trans (le_of_eq ?_)
      rw [norm_ofReal_mul_cexp hr.le, mul_comm]
      have hwe : w * cexp (((-arg w : ℝ) : ℂ) * I) = (‖w‖ : ℂ) := by
        conv_lhs => arg 1; rw [← norm_mul_exp_arg_mul_I w]
        rw [mul_assoc, ← Complex.exp_add, show (arg w : ℂ) * I + ((-arg w : ℝ) : ℂ) * I = 0 by
          push_cast; ring, Complex.exp_zero, mul_one]
      congr 2
      rw [show w * ((r : ℂ) * cexp (((-arg w : ℝ) : ℂ) * I)) =
        r * (w * cexp (((-arg w : ℝ) : ℂ) * I)) by ring, hwe, re_ofReal_mul, ofReal_re, mul_comm]
  have hint : IntegrableOn (fun r : ℝ => r ^ (c - 1) * Real.exp (-(‖w‖ * r))) (Ioi 0) := by
    have h2 := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := c - 1) (p := 1) (b := ‖w‖)
      (by linarith) (by norm_num) hw0)
    simpa using h2
  have hbound : ‖∫ r in Ioi (0 : ℝ), rotRay f (-arg w) r‖ ≤ ‖w‖ ^ (-c) * Real.Gamma c := by
    refine (norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioi
      fun r hr => hpt r hr)).trans (le_of_eq ?_)
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hc0 hw0, one_div, Real.inv_rpow hw0.le,
      Real.rpow_neg hw0.le]
  have hGc : (Gamma (c : ℂ)) = (Real.Gamma c : ℂ) := Complex.Gamma_ofReal c
  have hGpos : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc0
  rw [gamma_ratio_eq_integral hw hc0, hrot, norm_mul, norm_inv, hGc, norm_real,
    Real.norm_of_nonneg hGpos.le, inv_mul_le_iff₀ hGpos]
  exact hbound.trans_eq (mul_comm _ _)

/-- **DLMF 5.6.8**: `|Γ(z + a)/Γ(z + b)| ≤ 1/|z|^{b−a}` for `b − a ≥ 1`, `a ≥ 0`, `ℜz > 0`. -/
theorem dlmf_5_6_8 {a b : ℝ} (hab : 1 ≤ b - a) (ha : 0 ≤ a) {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma (z + a) / Gamma (z + b)‖ ≤ 1 / ‖z‖ ^ (b - a) := by
  have hw : 0 < (z + a).re := by simp; linarith
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h => by rw [h] at hz; simp at hz
  have h := norm_gamma_ratio_le hw hab
  rw [show z + (a : ℂ) + ((b - a : ℝ) : ℂ) = z + b by push_cast; ring] at h
  refine h.trans ?_
  have hle : ‖z‖ ≤ ‖z + a‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
    nlinarith
  rw [Real.rpow_neg (norm_nonneg _), one_div]
  exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hz0.le hle (by linarith))

end Azurite.DLMF
