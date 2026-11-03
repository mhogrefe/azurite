/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11ExpintAsymp
import Azurite.DLMF.Chapter2.Section4Watson

/-!
# DLMF 2.11.5: the integral representation of `E_p(z)`

For `ℜp > 0` and `|ph z| < π/2` (`z = e^w`, `|ℑw| < π/2`),
`E_p(z) = e^{−z} z^{p−1}/Γ(p) ∫_0^∞ e^{−zt} t^{p−1}/(1 + t) dt` (`dlmf_2_11_5`), with principal
powers. So `genExpInt` (entire in `w`) is the analytic continuation of 2.11.5.

Proof: the ray `t = z + σ` (`eiP_eq_ray` with `e = 1/z`) gives
`E_p(z) = z^{p−1} e^{−z} ∫_0^∞ e^{−σ} (z + σ)^{−p} dσ`; then
`Γ(p)(z + σ)^{−p} = ∫_0^∞ t^{p−1} e^{−(z+σ)t} dt` and Fubini, with
`∫_0^∞ e^{−σ(1+t)} dσ = 1/(1 + t)`.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

theorem arg_cexp_of_abs_lt {w : ℂ} (hw : |w.im| < π) : arg (cexp w) = w.im := by
  rw [← Complex.log_im, Complex.log_exp (by rw [abs_lt] at hw; linarith) (by
    rw [abs_lt] at hw; linarith)]

theorem cexp_cpow_of_abs_lt {w : ℂ} (hw : |w.im| < π) (c : ℂ) : cexp w ^ c = cexp (c * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero w), Complex.log_exp (by
    rw [abs_lt] at hw; linarith) (by rw [abs_lt] at hw; linarith), mul_comm]

theorem mul_cpow_of_arg {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (h : arg a + arg b ∈ Ioc (-π) π)
    (c : ℂ) : (a * b) ^ c = a ^ c * b ^ c := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero ha hb), Complex.cpow_def_of_ne_zero ha,
    Complex.cpow_def_of_ne_zero hb, (Complex.log_mul_eq_add_log_iff ha hb).mpr h, add_mul,
    Complex.exp_add]

/-- `Γ(p) ∫_0^∞ e^{−σ}(z + σ)^{−p} dσ = ∫_0^∞ e^{−zt} t^{p−1}/(1 + t) dt` (Fubini). -/
theorem gamma_mul_integral_eq {p z : ℂ} (hp : 0 < p.re) (hz : 0 < z.re) :
    Complex.Gamma p * ∫ σ in Ioi (0 : ℝ), cexp (-σ) * (z + σ) ^ (-p) =
      ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (t : ℂ) ^ (p - 1) / (1 + t) := by
  set F : ℝ → ℝ → ℂ := fun σ t => cexp (-σ) * ((t : ℂ) ^ (p - 1) * cexp (-((z + σ) * t)))
  -- the inner integrals
  have hin1 : ∀ σ ∈ Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), F σ t =
      Complex.Gamma p * (cexp (-σ) * (z + σ) ^ (-p)) := fun σ hσ => by
    have hre : 0 < (z + σ).re := by simp; linarith [show (0 : ℝ) < σ from hσ]
    simp only [F]
    rw [MeasureTheory.integral_const_mul, integral_cpow_mul_cexp_neg_complex hp hre,
      one_div_cpow_of_re_pos hre]
    ring
  have hin2 : ∀ t ∈ Ioi (0 : ℝ), ∫ σ in Ioi (0 : ℝ), F σ t =
      cexp (-(z * t)) * (t : ℂ) ^ (p - 1) / (1 + t) := fun t ht => by
    have ht' : (0 : ℝ) < t := ht
    have hne : (1 : ℂ) + t ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have e : ∀ σ : ℝ, F σ t = cexp (-(z * t)) * (t : ℂ) ^ (p - 1) * cexp (-(1 + t) * σ) := by
      intro σ
      simp only [F]
      rw [show cexp (-(1 + (t : ℂ)) * σ) = cexp (-(σ : ℂ)) * cexp (-(σ * t)) by
        rw [← Complex.exp_add]; ring_nf, show -((z + σ) * t) = -(z * t) + -(σ * t) by ring,
        Complex.exp_add]
      ring
    simp only [e]
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_complex_Ioi (by simp; linarith) 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
  -- integrability on the product
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have h1 : Integrable (fun σ : ℝ => Real.exp (-σ)) (volume.restrict (Ioi (0 : ℝ))) := by
      have := exp_neg_integrableOn_Ioi 0 (one_pos (α := ℝ))
      simp only [neg_mul, one_mul] at this
      exact this
    have h2 : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (p - 1) * cexp (-(z * t))‖)
        (volume.restrict (Ioi (0 : ℝ))) := (integrableOn_cpow_mul_cexp_neg hp hz).norm
    refine (h1.mul_prod h2).mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      simp only [F, Function.uncurry_def]
      fun_prop
    · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
      refine Eventually.of_forall fun q hq => ?_
      obtain ⟨hs, ht⟩ := hq
      have hs' : (0 : ℝ) < q.1 := hs
      have ht' : (0 : ℝ) < q.2 := ht
      simp only [F, Function.uncurry_def]
      rw [norm_mul, norm_mul, norm_mul]
      have e1 : ‖cexp (-(q.1 : ℂ))‖ = Real.exp (-q.1) := by
        rw [Complex.norm_exp]; simp
      have e2 : ‖cexp (-((z + q.1) * q.2))‖ ≤ ‖cexp (-(z * q.2))‖ := by
        rw [Complex.norm_exp, Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have a1 : (-((z + q.1) * q.2)).re = -(z.re * q.2) - q.1 * q.2 := by simp; ring
        have a2 : (-(z * q.2)).re = -(z.re * q.2) := by simp
        rw [a1, a2]
        nlinarith
      rw [e1]
      gcongr
  have hswap := integral_integral_swap hint
  rw [setIntegral_congr_fun measurableSet_Ioi hin1, setIntegral_congr_fun measurableSet_Ioi hin2,
    MeasureTheory.integral_const_mul] at hswap
  exact hswap

/-- **DLMF 2.11.5**: for `ℜp > 0` and `|ph z| < π/2`,
`E_p(z) = e^{−z} z^{p−1}/Γ(p) ∫_0^∞ e^{−zt} t^{p−1}/(1 + t) dt` (principal `z^{p−1}`). -/
theorem dlmf_2_11_5 {p : ℂ} (hp : 0 < p.re) {w : ℂ} (hw : |w.im| < π / 2) :
    genExpInt p w = cexp (-cexp w) * cexp w ^ (p - 1) / Complex.Gamma p *
      ∫ t in Ioi (0 : ℝ), cexp (-(cexp w * t)) * (t : ℂ) ^ (p - 1) / (1 + t) := by
  set z := cexp w
  have hw' : |w.im| < π := by linarith [Real.pi_pos]
  have hz0 : z ≠ 0 := Complex.exp_ne_zero w
  have hzre : 0 < z.re := by
    simp only [z, Complex.exp_re]
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (by rw [abs_lt] at hw; constructor <;>
      linarith))
  have hargz : arg z = w.im := arg_cexp_of_abs_lt hw'
  -- the ray `t = z + σ`
  set e := z⁻¹
  have hre_e : 0 < e.re := by
    simp only [e, Complex.inv_re]; exact div_pos hzre (Complex.normSq_pos.mpr hz0)
  have hray : ∀ σ : ℝ, 0 ≤ σ → 1 ≤ (1 + σ * e).re := fun σ hσ => by
    simp; nlinarith
  have hargu : ∀ σ : ℝ, 0 ≤ σ → |arg (1 + σ * e)| < π / 2 := fun σ hσ =>
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith [hray σ hσ]))
  have he_slit : e ∈ slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre_e)
  have harg_e : arg e = -w.im := by
    have hne : w.im ≠ π := by
      intro h; rw [h, abs_of_pos Real.pi_pos] at hw'; linarith
    rw [Complex.arg_inv, hargz]
    simp only [hne, ↓reduceIte]
  have h := eiP_eq_ray (le_of_lt hp) (fun σ hσ => Complex.mem_slitPlane_iff.mpr
    (Or.inl (by linarith [hray σ hσ]))) one_pos (fun σ hσ => (hray σ hσ).trans
      (Complex.re_le_norm _)) he_slit (by simp only [z, e]; rw [mul_inv_cancel₀ hz0]; simp)
    (by rw [harg_e]; simp [Real.pi_pos])
  -- `(1 + σ/z)^{−p}/z = z^{p−1} (z + σ)^{−p}`
  have hpow : ∀ σ : ℝ, 0 ≤ σ → (1 + σ * e) ^ (-p) = z ^ p * (z + σ) ^ (-p) := fun σ hσ => by
    have hu0 : (1 : ℂ) + σ * e ≠ 0 := fun h0 => by
      have := hray σ hσ; rw [h0] at this; norm_num at this
    have hmul : z + σ = z * (1 + σ * e) := by simp only [e]; field_simp
    rw [hmul, mul_cpow_of_arg hz0 hu0 ?_ (-p), ← mul_assoc, ← Complex.cpow_add _ _ hz0,
      add_neg_cancel, Complex.cpow_zero, one_mul]
    have := hargu σ hσ
    rw [hargz, abs_lt] at *
    constructor <;> linarith
  have hE : genExpInt p w = cexp ((p - 1) * w) * cexp (-z) *
      ∫ σ in Ioi (0 : ℝ), cexp (-σ) * (z + σ) ^ (-p) := by
    rw [genExpInt, h]
    have hcongr : ∫ σ in Ioi (0 : ℝ), cexp (-(z * (1 + σ * e))) * (1 + σ * e) ^ (-p) =
        z ^ p * cexp (-z) * ∫ σ in Ioi (0 : ℝ), cexp (-σ) * (z + σ) ^ (-p) := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_
      rw [hpow σ (le_of_lt hσ), show -(z * (1 + σ * e)) = -z + -σ by
        simp only [e]; field_simp; ring, Complex.exp_add]
      ring
    rw [hcongr, cexp_cpow_of_abs_lt hw', show e = cexp (-w) by simp [e, z, Complex.exp_neg] ]
    have : cexp ((p - 1) * w) * (cexp ((1 - p) * w) * cexp (-w) * (cexp (p * w))) =
        cexp ((p - 1) * w) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; ring_nf
    linear_combination (∫ σ in Ioi (0 : ℝ), cexp (-σ) * (z + σ) ^ (-p)) * cexp (-z) * this
  rw [hE, ← gamma_mul_integral_eq hp hzre, cexp_cpow_of_abs_lt hw']
  have hG : Complex.Gamma p ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hp
  field_simp

end Azurite.DLMF
