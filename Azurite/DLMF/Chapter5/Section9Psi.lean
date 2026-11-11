/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9BinetArctan
import Azurite.DLMF.Chapter1.Section14TableLaplaceLog

/-!
# DLMF §5.9(ii): the psi function (Binet forms)

Formalizations of <https://dlmf.nist.gov/5.9>, equations 5.9.12, 5.9.13, 5.9.15, the first
equality of 5.9.16 and the last form of 5.9.18, all for `ℜz > 0`. `ψ` is Mathlib's
`Complex.digamma` (`Γ′/Γ`).

* `digamma_add_eq_deriv`: if `Γ(w + a) = exp(E(w))` on an open set, then `ψ(z + a) = E′(z)` there
  (the exponentiated `Ln Γ` formulas of §5.9(i) differentiate to formulas for `ψ`).
* 5.9.13 (`dlmf_5_9_13`): Binet's first formula 5.9.10_2 differentiated, `J′ = −ℒ(tφ)` (1.14.23).
* 5.9.15 (`dlmf_5_9_15`): Binet's second formula 5.9.10 differentiated under the integral sign
  (`hasDerivAt_binetArctanInt`), `∂/∂z arctan(t/z) = −t/(t² + z²)`.
* 5.9.12 (`dlmf_5_9_12`): 5.9.13 plus Frullani's `ln z = ∫₀^∞ (e^{−t} − e^{−zt})/t dt`
  (Table 1.14.4, row 13, at `s = 0`).
* 5.9.16 (`dlmf_5_9_16`, first equality): 5.9.12 at `z` minus 5.9.12 at `1`, `ψ(1) = −γ`.
* 5.9.18 (`dlmf_5_9_18_4`, last form): 5.9.12 at `z = 1`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### `ψ` from an exponentiated `Ln Γ` -/

/-- If `Γ(w + a) = exp(E(w))` on an open set `U ∋ z` and `E` is differentiable at `z`, then
`ψ(z + a) = E′(z)`. -/
theorem digamma_add_eq_deriv {U : Set ℂ} (hU : IsOpen U) {E : ℂ → ℂ} {a z : ℂ} (hz : z ∈ U)
    (hE : DifferentiableAt ℂ E z) (h : ∀ w ∈ U, Gamma (w + a) = cexp (E w)) :
    digamma (z + a) = deriv E z := by
  have hev : (fun w => Gamma (w + a)) =ᶠ[𝓝 z] fun w => cexp (E w) :=
    eventually_of_mem (hU.mem_nhds hz) h
  have hd : HasDerivAt (fun w => Gamma (w + a)) (cexp (E z) * deriv E z) z :=
    hE.hasDerivAt.cexp.congr_of_eventuallyEq hev
  have hd' : deriv Gamma (z + a) = cexp (E z) * deriv E z := by
    rw [← hd.deriv, deriv_comp_add_const]
  rw [digamma_def, logDeriv_apply, hd', h z hz]
  field_simp [Complex.exp_ne_zero]

/-! ### 5.9.13 -/

/-- The integrand `(1/t − 1/(1 − e^{−t})) e^{−tz}` of 5.9.13. -/
noncomputable def psiLaplaceIntegrand (z : ℂ) (t : ℝ) : ℂ :=
  ((1 / t - 1 / (1 - Real.exp (-t)) : ℝ) : ℂ) * cexp (-(t * z))

theorem expGrowth_mul_binetPhi {ε : ℝ} (hε : 0 < ε) :
    ∃ M, ExpGrowth M ε (fun t : ℝ => (t : ℂ) * (binetPhi t : ℂ)) := by
  have := expGrowth_binetPhi.pow_mul 1 hε
  simp only [pow_one, zero_add] at this
  exact ⟨_, this⟩

theorem aestronglyMeasurable_mul_binetPhi :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * (binetPhi t : ℂ)) (volume.restrict (Ioi 0)) := by
  simpa only [pow_one] using aestronglyMeasurable_pow_mul aestronglyMeasurable_binetPhi 1

theorem expGrowth_const_half : ExpGrowth (1 / 2) 0 (fun _ => (1 / 2 : ℂ)) := fun t _ => by
  simp

/-- `−(ℒ(tφ)(z) + ℒ(½)(z))` is the integral of 5.9.13. -/
theorem psiLaplace_eq {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (psiLaplaceIntegrand z) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), psiLaplaceIntegrand z t =
        -(laplace (fun t => (t : ℂ) * (binetPhi t : ℂ)) z + laplace (fun _ => (1 / 2 : ℂ)) z) := by
  obtain ⟨M, hM⟩ := expGrowth_mul_binetPhi (half_pos hz)
  have h1 := integrableOn_laplace aestronglyMeasurable_mul_binetPhi hM (s := z) (by linarith)
  have h2 := integrableOn_laplace aestronglyMeasurable_const.restrict expGrowth_const_half
    (s := z) (by simpa using hz)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), psiLaplaceIntegrand z t =
      -(cexp (-(z * t)) * ((t : ℂ) * (binetPhi t : ℂ)) + cexp (-(z * t)) * (1 / 2 : ℂ)) :=
    fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have he : Real.exp t - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht')).ne'
      have he' : 1 - Real.exp (-t) ≠ 0 :=
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
      have hfrac : (1 / t - 1 / (1 - Real.exp (-t)) : ℝ) =
          -(t * binetPhi t + 1 / 2) := by
        rw [binetPhi, Real.exp_neg]
        have hx := Real.exp_pos t
        field_simp
        ring
      rw [psiLaplaceIntegrand, hfrac, mul_comm (t : ℂ) z]
      push_cast
      ring
  refine ⟨((h1.add h2).neg).congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_neg, integral_add h1 h2]
  rfl

/-- **DLMF 5.9.13**: for `ℜz > 0`, `ψ(z) = ln z + ∫₀^∞ (1/t − 1/(1 − e^{−t})) e^{−tz} dt`. -/
theorem dlmf_5_9_13 {z : ℂ} (hz : 0 < z.re) :
    digamma z = Complex.log z +
      ∫ t in Ioi (0 : ℝ), ((1 / t - 1 / (1 - Real.exp (-t)) : ℝ) : ℂ) * cexp (-(t * z)) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  set E : ℂ → ℂ := fun w => (w - 1 / 2) * Complex.log w - w + 1 / 2 * Complex.log (2 * π) +
    binetJ w with hE
  have hJ := hasDerivAt_laplace aestronglyMeasurable_binetPhi expGrowth_binetPhi
    (s₀ := z) (by simpa using hz)
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hD : HasDerivAt E (Complex.log z + (z - 1 / 2) / z - 1 +
      -laplace (fun t => (t : ℂ) * (binetPhi t : ℂ)) z) z := by
    have hl := hasDerivAt_log (Or.inl hz : z ∈ slitPlane)
    have h1 : HasDerivAt (fun w => (w - 1 / 2) * Complex.log w) (1 * Complex.log z +
        (z - 1 / 2) * z⁻¹) z := ((hasDerivAt_id' z).sub_const _).mul hl
    have := ((h1.sub (hasDerivAt_id' z)).add_const (1 / 2 * Complex.log (2 * π))).add hJ
    refine HasDerivAt.congr_deriv (f := E) this ?_
    field_simp
  have key := digamma_add_eq_deriv (a := 0) hUo (show z ∈ U from hz) hD.differentiableAt
    (fun w hw => by rw [add_zero]; exact dlmf_5_9_10_2 hw)
  rw [add_zero] at key
  rw [key, hD.deriv]
  have h := (psiLaplace_eq hz).2
  simp only [psiLaplaceIntegrand] at h
  rw [h, show laplace (fun _ => (1 / 2 : ℂ)) z = 1 / 2 * laplace (fun _ => 1) z by
    rw [laplace, laplace, ← integral_const_mul]; simp_rw [mul_one, mul_comm],
    dlmf_table_1_14_4_r1 hz]
  field_simp
  ring

/-! ### 5.9.12: Frullani -/

/-- **Frullani**: `ln z = ∫₀^∞ (e^{−t} − e^{−zt})/t dt` for `ℜz > 0`. -/
theorem log_eq_integral_frullani {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (cexp (-t) - cexp (-(z * t))) / t) (Ioi 0) ∧
      Complex.log z = ∫ t in Ioi (0 : ℝ), (cexp (-t) - cexp (-(z * t))) / t := by
  have h := laplace_exp_sub_exp_div (s := 0) (a := z) (b := 1) (by simpa using hz) (by simp)
  simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul, zero_add, Complex.log_one,
    sub_zero] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2, laplace]
  simp

/-- The integrand `e^{−t}/t − e^{−zt}/(1 − e^{−t})` of 5.9.12. -/
noncomputable def psiFrullaniIntegrand (z : ℂ) (t : ℝ) : ℂ :=
  cexp (-t) / t - cexp (-(z * t)) / (1 - cexp (-t))

theorem psiFrullani_eq {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (psiFrullaniIntegrand z) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), psiFrullaniIntegrand z t = digamma z := by
  obtain ⟨hi1, hl⟩ := log_eq_integral_frullani hz
  obtain ⟨hi2, -⟩ := psiLaplace_eq hz
  have hpt : ∀ t ∈ Ioi (0 : ℝ), psiFrullaniIntegrand z t =
      (cexp (-t) - cexp (-(z * t))) / t + psiLaplaceIntegrand z t := fun t ht => by
    have ht' : (0 : ℝ) < t := ht
    have he' : 1 - Real.exp (-t) ≠ 0 :=
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
    have he'' : (1 : ℂ) - cexp (-t) ≠ 0 := by
      rw [← ofReal_neg, ← ofReal_exp]; exact_mod_cast he'
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht'.ne'
    rw [psiFrullaniIntegrand, psiLaplaceIntegrand]
    push_cast
    rw [mul_comm (t : ℂ) z]
    field_simp
    ring
  refine ⟨(hi1.add hi2).congr_fun (fun t ht => (hpt t ht).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hi1 hi2, ← hl,
    dlmf_5_9_13 hz]
  rfl

/-- **DLMF 5.9.12**: for `ℜz > 0`, `ψ(z) = ∫₀^∞ (e^{−t}/t − e^{−zt}/(1 − e^{−t})) dt`. -/
theorem dlmf_5_9_12 {z : ℂ} (hz : 0 < z.re) :
    digamma z = ∫ t in Ioi (0 : ℝ), (cexp (-t) / t - cexp (-(z * t)) / (1 - cexp (-t))) :=
  (psiFrullani_eq hz).2.symm

/-- The integrand of 5.9.12 is integrable on `(0, ∞)`. -/
theorem integrableOn_dlmf_5_9_12 {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => cexp (-t) / t - cexp (-(z * t)) / (1 - cexp (-t))) (Ioi 0) :=
  (psiFrullani_eq hz).1

/-! ### 5.9.16 and 5.9.18 -/

/-- **DLMF 5.9.16** (first equality): for `ℜz > 0`,
`ψ(z) + γ = ∫₀^∞ (e^{−t} − e^{−zt})/(1 − e^{−t}) dt`. -/
theorem dlmf_5_9_16 {z : ℂ} (hz : 0 < z.re) :
    digamma z + γ = ∫ t in Ioi (0 : ℝ), (cexp (-t) - cexp (-(z * t))) / (1 - cexp (-t)) := by
  obtain ⟨hi, hv⟩ := psiFrullani_eq hz
  obtain ⟨hi1, hv1⟩ := psiFrullani_eq (z := 1) (by simp)
  have hpt : ∀ t : ℝ, (cexp (-t) - cexp (-(z * t))) / (1 - cexp (-t)) =
      psiFrullaniIntegrand z t - psiFrullaniIntegrand 1 t := fun t => by
    rw [psiFrullaniIntegrand, psiFrullaniIntegrand, one_mul]
    ring
  simp_rw [hpt]
  rw [integral_sub hi hi1, hv, hv1, digamma_one]
  ring

/-- The integrand of 5.9.16 is integrable on `(0, ∞)`. -/
theorem integrableOn_dlmf_5_9_16 {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (cexp (-t) - cexp (-(z * t))) / (1 - cexp (-t))) (Ioi 0) := by
  have h := (psiFrullani_eq hz).1.sub (psiFrullani_eq (z := 1) (by simp)).1
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, psiFrullaniIntegrand, one_mul]
  ring

/-- **DLMF 5.9.18** (last form): `γ = ∫₀^∞ (e^{−t}/(1 − e^{−t}) − e^{−t}/t) dt`. -/
theorem dlmf_5_9_18_4 :
    γ = ∫ t in Ioi (0 : ℝ), (Real.exp (-t) / (1 - Real.exp (-t)) - Real.exp (-t) / t) := by
  have h := (psiFrullani_eq (z := 1) (by simp)).2
  rw [digamma_one] at h
  have e : ∫ t in Ioi (0 : ℝ), psiFrullaniIntegrand 1 t = ((-∫ t in Ioi (0 : ℝ),
      (Real.exp (-t) / (1 - Real.exp (-t)) - Real.exp (-t) / t) : ℝ) : ℂ) := by
    rw [ofReal_neg, ← integral_complex_ofReal, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [psiFrullaniIntegrand, one_mul]
    push_cast
    ring
  rw [e] at h
  have := congrArg Complex.re h
  simp only [ofReal_re, neg_re] at this
  linarith

/-! ### 5.9.15 -/

theorem div_mem_arctanCut {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) / w ∈ arctanCut := by
  left
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hn : 0 < normSq w := normSq_pos.mpr hw0
  have : ((t : ℂ) / w).re = t * w.re / normSq w := by simp [div_re]
  rw [this]
  positivity

/-- `∂/∂w arctan(t/w) = −t/(w² + t²)` for `ℜw > 0`, `t > 0`. -/
theorem hasDerivAt_arctan_div_param {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun w => Complex.arctan (t / w)) (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) w := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h1 : HasDerivAt (fun w : ℂ => (t : ℂ) / w) ((t : ℂ) * -(w ^ 2)⁻¹) w := by
    have := (hasDerivAt_inv hw0).const_mul (t : ℂ)
    simp only [div_eq_mul_inv]
    exact this
  have h2 := (hasDerivAt_arctan_of_mem (div_mem_arctanCut hw ht)).comp w h1
  have h0 := sq_add_sq_ne_zero hw t
  have h3 : 1 + ((t : ℂ) / w) ^ 2 ≠ 0 := by
    rw [show 1 + ((t : ℂ) / w) ^ 2 = (w ^ 2 + (t : ℂ) ^ 2) / w ^ 2 by field_simp]
    exact div_ne_zero h0 (pow_ne_zero 2 hw0)
  refine h2.congr_deriv ?_
  field_simp

/-- Binet's second-formula integral `∫₀^∞ arctan(t/w)/(e^{2πt} − 1) dt`. -/
noncomputable def binetArctanInt (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.arctan (t / w) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)

theorem exp_two_pi_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp (2 * π * t) - 1 :=
  sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))

theorem div_exp_two_pi_sub_one_le {t : ℝ} (ht : 0 < t) :
    t / (Real.exp (2 * π * t) - 1) ≤ 1 / π * Real.exp (-(π * t)) := by
  have := two_mul_div_exp_sub_one_le ht
  have e1 : 2 * t / (Real.exp (2 * π * t) - 1) = 2 * (t / (Real.exp (2 * π * t) - 1)) := by ring
  have e2 : 2 / π * Real.exp (-(π * t)) = 2 * (1 / π * Real.exp (-(π * t))) := by ring
  linarith

theorem hasDerivAt_binetArctanInt {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt binetArctanInt (∫ t in Ioi (0 : ℝ),
      -(t : ℂ) / (z ^ 2 + (t : ℂ) ^ 2) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)) z := by
  have hπ := Real.pi_pos
  set r := z.re / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hre : ∀ w ∈ Metric.ball z r, r < w.re := fun w hw => by
    have := (Complex.abs_re_le_norm (w - z)).trans_lt (by rwa [← dist_eq_norm])
    rw [sub_re, abs_lt] at this
    linarith [this.1]
  set F : ℂ → ℝ → ℂ := fun w t => Complex.arctan (t / w) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)
    with hF
  set F' : ℂ → ℝ → ℂ := fun w t =>
    -(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ) with hF'
  have hden : ∀ t : ℝ, 0 < t → ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ) ≠ 0 := fun t ht =>
    ofReal_ne_zero.mpr (exp_two_pi_sub_one_pos ht).ne'
  have hcontF : ∀ w : ℂ, 0 < w.re → ContinuousOn (F w) (Ioi 0) := fun w hw t ht => by
    have ht' : (0 : ℝ) < t := ht
    exact ((hasDerivAt_complex_arctan_div hw ht'.le).continuousAt.div
      (by fun_prop) (hden t ht')).continuousWithinAt
  have hcontF' : ∀ w : ℂ, 0 < w.re → ContinuousOn (F' w) (Ioi 0) := fun w hw t ht => by
    have ht' : (0 : ℝ) < t := ht
    exact (((by fun_prop : Continuous fun t : ℝ => -(t : ℂ)).continuousAt.div
      (by fun_prop : Continuous fun t : ℝ => w ^ 2 + (t : ℂ) ^ 2).continuousAt
      (sq_add_sq_ne_zero hw t)).div (by fun_prop) (hden t ht')).continuousWithinAt
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(π * t))) (Ioi 0) := by
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hπ
  have hbound_int : IntegrableOn (fun t : ℝ => 1 / r ^ 2 * (1 / π * Real.exp (-(π * t))))
      (Ioi 0) := (hexp.const_mul (1 / π)).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := z) (bound := fun t => 1 / r ^ 2 * (1 / π * Real.exp (-(π * t))))
    (Metric.ball_mem_nhds z hr0)
    (eventually_of_mem (Metric.ball_mem_nhds z hr0) fun w hw =>
      (hcontF w (by linarith [hre w hw])).aestronglyMeasurable measurableSet_Ioi)
    (by
      refine Integrable.mono' ((hexp.const_mul (1 / π)).const_mul (‖z‖ / z.re ^ 2))
        ((hcontF z hz).aestronglyMeasurable measurableSet_Ioi)
        ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
      have ht' : (0 : ℝ) < t := ht
      have he := exp_two_pi_sub_one_pos ht'
      simp only [hF]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg he.le]
      calc ‖Complex.arctan (t / z)‖ / (Real.exp (2 * π * t) - 1)
          ≤ ‖z‖ / z.re ^ 2 * t / (Real.exp (2 * π * t) - 1) := by
            gcongr; exact norm_arctan_div_le hz ht'.le
        _ = ‖z‖ / z.re ^ 2 * (t / (Real.exp (2 * π * t) - 1)) := by ring
        _ ≤ _ := by gcongr; exact div_exp_two_pi_sub_one_le ht')
    ((hcontF' z hz).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht w hw => by
      have ht' : (0 : ℝ) < t := ht
      have he := exp_two_pi_sub_one_pos ht'
      have hw' := hre w hw
      have hsq : r ^ 2 ≤ ‖w ^ 2 + (t : ℂ) ^ 2‖ :=
        (pow_le_pow_left₀ hr0.le hw'.le 2).trans (re_sq_le_norm_sq_add_sq (by linarith) t)
      simp only [hF']
      rw [norm_div, norm_div, norm_neg, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg ht'.le, Real.norm_of_nonneg he.le]
      calc t / ‖w ^ 2 + (t : ℂ) ^ 2‖ / (Real.exp (2 * π * t) - 1)
          ≤ t / r ^ 2 / (Real.exp (2 * π * t) - 1) := by gcongr
        _ = 1 / r ^ 2 * (t / (Real.exp (2 * π * t) - 1)) := by ring
        _ ≤ _ := by gcongr; exact div_exp_two_pi_sub_one_le ht'))
    hbound_int
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht w hw =>
      (hasDerivAt_arctan_div_param (by linarith [hre w hw]) ht).div_const _))
  exact key.2

/-- **DLMF 5.9.15**: for `ℜz > 0`,
`ψ(z) = ln z − 1/(2z) − 2 ∫₀^∞ t dt/((t² + z²)(e^{2πt} − 1))`. -/
theorem dlmf_5_9_15 {z : ℂ} (hz : 0 < z.re) :
    digamma z = Complex.log z - 1 / (2 * z) - 2 * ∫ t in Ioi (0 : ℝ),
      (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  set E : ℂ → ℂ := fun w => (w - 1 / 2) * Complex.log w - w + 1 / 2 * Complex.log (2 * π) +
    2 * binetArctanInt w with hE
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hA := hasDerivAt_binetArctanInt hz
  have hD : HasDerivAt E (Complex.log z + (z - 1 / 2) / z - 1 + 2 * ∫ t in Ioi (0 : ℝ),
      -(t : ℂ) / (z ^ 2 + (t : ℂ) ^ 2) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)) z := by
    have hl := hasDerivAt_log (Or.inl hz : z ∈ slitPlane)
    have h1 : HasDerivAt (fun w => (w - 1 / 2) * Complex.log w) (1 * Complex.log z +
        (z - 1 / 2) * z⁻¹) z := ((hasDerivAt_id' z).sub_const _).mul hl
    have := ((h1.sub (hasDerivAt_id' z)).add_const (1 / 2 * Complex.log (2 * π))).add
      (hA.const_mul 2)
    refine HasDerivAt.congr_deriv (f := E) this ?_
    field_simp
  have key := digamma_add_eq_deriv (a := 0) hUo (show z ∈ U from hz) hD.differentiableAt
    (fun w hw => by rw [add_zero]; exact dlmf_5_9_10 hw)
  rw [add_zero] at key
  rw [key, hD.deriv]
  have e : ∫ t in Ioi (0 : ℝ), -(t : ℂ) / (z ^ 2 + (t : ℂ) ^ 2) /
      ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ) = -∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [div_div, add_comm (z ^ 2), neg_div]
  rw [e]
  field_simp
  ring

end Azurite.DLMF
