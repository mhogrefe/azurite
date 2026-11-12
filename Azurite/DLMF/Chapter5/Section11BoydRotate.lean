/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11BoydBound
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# DLMF 5.11.11: tools for the `2K^{1/2}` branch

Following G. Nemes (arXiv:1310.0166, Lemma 2.2 and the proof of Theorem 1.3):
* `|1/Γ*(v)| ≤ 1` for `ℜv ≥ 0` (`norm_inv_scaledGamma_le_one`), by the Phragmén–Lindelöf
  principle on the right half-plane: `1/Γ*` is bounded there (Stieltjes' bound), tends to `0` at
  `0` (`tendsto_inv_scaledGamma_zero`), and `|1/Γ*(iy)| = (1 − e^{−2π|y|})^{1/2} ≤ 1`;
* the reflection identity `Γ*(w) Γ*(−w) (1 − e^{2πiw}) = 1` for `ℑw > 0`
  (`scaledGamma_mul_neg_of_im_pos`), hence `|Γ*(w)| ≤ (1 − e^{−2πℑw})⁻¹` for `ℜw ≤ 0 < ℑw`
  (`norm_scaledGamma_le_of_quadrant`);
* rotation of a ray integral `∫₀^∞ f(r) dr = e^{iφ} ∫₀^∞ f(re^{iφ}) dr` for `f` holomorphic on the
  closed sector `0 ≤ ph s ≤ φ` with `|f(re^{iψ})| ≤ C(1 + r^p)e^{−cr}` (`integral_Ioi_rotate`;
  Cauchy's theorem on the image under `exp` of rectangles, as for Watson's lemma in §2.4).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### `|1/Γ*| ≤ 1` on the closed right half-plane -/

theorem scaledGamma_zero : scaledGamma 0 = 0 := by
  simp [scaledGamma, Complex.Gamma_zero]

/-- `1/Γ*(v) → 0` as `v → 0` in `ℜv ≥ 0`. -/
theorem tendsto_inv_scaledGamma_zero :
    Tendsto (fun v => (scaledGamma v)⁻¹) (𝓝[{v : ℂ | 0 ≤ v.re}] 0) (𝓝 0) := by
  have hG : Tendsto (fun v : ℂ => (Gamma (v + 1))⁻¹) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun v : ℂ => (Gamma (v + 1))⁻¹ :=
      differentiable_one_div_Gamma.continuous.comp (continuous_id.add continuous_const)
    have := hc.tendsto 0
    simpa [Complex.Gamma_one] using this
  have hev : ∀ᶠ v in 𝓝[{v : ℂ | 0 ≤ v.re}] (0 : ℂ),
      ‖v‖ ≤ 1 ∧ ‖(Gamma (v + 1))⁻¹‖ ≤ 2 ∧ 0 ≤ v.re := by
    have h1 : ∀ᶠ v in 𝓝 (0 : ℂ), ‖v‖ ≤ 1 := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with v hv
      simpa using hv
    have h2 : ∀ᶠ v in 𝓝 (0 : ℂ), ‖(Gamma (v + 1))⁻¹‖ ≤ 2 := by
      have := hG.norm
      rw [norm_one] at this
      exact this.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2))
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
      with v a b c
    exact ⟨a, b, c⟩
  set K := Real.sqrt (2 * π) * Real.exp π * 2
  refine squeeze_zero_norm' (a := fun v : ℂ => K * ‖v‖ ^ (1 / 2 : ℝ)) ?_ ?_
  · filter_upwards [hev] with v ⟨hv1, hvG, hvre⟩
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [scaledGamma_zero, inv_zero, norm_zero]; positivity
    have hx : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have hinv : (scaledGamma v)⁻¹ = (Real.sqrt (2 * π) : ℂ) * cexp (-v) *
        (v ^ (v - 1 / 2) * v) * (Gamma (v + 1))⁻¹ := by
      rw [scaledGamma, inv_div, Gamma_add_one v hv0]
      field_simp
    have hcp := norm_cpow_le_of_re (s := v - 1 / 2) hv0
    have him : |(v - 1 / 2).im| ≤ 1 := by
      have : (v - 1 / 2).im = v.im := by simp
      rw [this]
      exact (abs_im_le_norm v).trans hv1
    have hpow : ‖v‖ ^ (v - 1 / 2).re * ‖v‖ ≤ ‖v‖ ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hx.ne']
      refine Real.rpow_le_rpow_of_exponent_ge hx hv1 ?_
      have : (v - 1 / 2).re = v.re - 1 / 2 := by simp
      rw [this]
      linarith
    have he : ‖cexp (-v)‖ ≤ 1 := by
      rw [norm_exp, neg_re, Real.exp_le_one_iff]; linarith
    rw [hinv, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hs := Real.sqrt_nonneg (2 * π)
    calc Real.sqrt (2 * π) * ‖cexp (-v)‖ * (‖v ^ (v - 1 / 2)‖ * ‖v‖) * ‖(Gamma (v + 1))⁻¹‖
        ≤ Real.sqrt (2 * π) * 1 * (‖v‖ ^ (v - 1 / 2).re * Real.exp π * ‖v‖) * 2 := by
          gcongr
          refine hcp.trans ?_
          gcongr
          nlinarith [Real.pi_pos]
      _ = Real.sqrt (2 * π) * Real.exp π * 2 * (‖v‖ ^ (v - 1 / 2).re * ‖v‖) := by ring
      _ ≤ K * ‖v‖ ^ (1 / 2 : ℝ) := by gcongr
  · have : Tendsto (fun v : ℂ => K * ‖v‖ ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 (K * ‖(0 : ℂ)‖ ^ (1 / 2 : ℝ))) :=
      (continuous_const.mul ((continuous_norm).rpow_const fun _ => Or.inr (by norm_num))).tendsto 0
    rw [norm_zero, Real.zero_rpow (by norm_num), mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds

theorem norm_inv_scaledGamma_I_le (y : ℝ) : ‖(scaledGamma ((y : ℂ) * I))⁻¹‖ ≤ 1 := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have h := norm_scaledGamma_neg_I (t := -y) (by linarith)
    rw [show ((-y : ℝ) : ℂ) * -I = (y : ℂ) * I by push_cast; ring] at h
    rw [norm_inv, h, one_div, inv_inv]
    exact Real.sqrt_le_one.mpr (by linarith [Real.exp_pos (-(2 * π * -y))])
  · simp [scaledGamma_zero]
  · rw [norm_inv, norm_scaledGamma_I hy, one_div, inv_inv]
    exact Real.sqrt_le_one.mpr (by linarith [Real.exp_pos (-(2 * π * y))])

/-- **Nemes, proof of Lemma 2.2**: `|1/Γ*(v)| ≤ 1` for `ℜv ≥ 0` (Phragmén–Lindelöf). -/
theorem norm_inv_scaledGamma_le_one {v : ℂ} (hv : 0 ≤ v.re) : ‖(scaledGamma v)⁻¹‖ ≤ 1 := by
  obtain ⟨C, -, h2⟩ := halfPlaneDecay_scaledGamma
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hdiff : DifferentiableOn ℂ (fun w => (scaledGamma w)⁻¹) {w | 0 < w.re} := by
    simpa using h2.diff.add_const 1
  -- the bound at infinity
  have hfar : ∀ w : ℂ, 0 < w.re → 1 ≤ ‖w‖ → ‖(scaledGamma w)⁻¹‖ ≤ 2 := fun w hw hw1 => by
    have h := (norm_scaledGamma_sub_one_le hw hw1).2
    have h3 : 1 / (3 * ‖w‖) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc ‖(scaledGamma w)⁻¹‖ = ‖((scaledGamma w)⁻¹ - 1) + 1‖ := by ring_nf
      _ ≤ ‖(scaledGamma w)⁻¹ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hcont : ContinuousOn (fun w => (scaledGamma w)⁻¹) (closure {w : ℂ | 0 < w.re}) := by
    rw [closure_setOfPred_lt_re]
    intro w hw
    rcases (show (0 : ℝ) ≤ w.re from hw).lt_or_eq with hre | hre
    · exact ((hdiff w hre).differentiableAt (hU.mem_nhds hre)).continuousAt.continuousWithinAt
    · rcases eq_or_ne w.im 0 with him | him
      · have hw0 : w = 0 := Complex.ext hre.symm him
        subst hw0
        rw [ContinuousWithinAt, scaledGamma_zero, inv_zero]
        exact tendsto_inv_scaledGamma_zero
      · have hwI : w = (w.im : ℂ) * I := by
          apply Complex.ext <;> simp [hre.symm]
        obtain ⟨hc, hne⟩ := continuousAt_scaledGamma_I him
        rw [← hwI] at hc hne
        exact (hc.inv₀ hne).continuousWithinAt
  refine PhragmenLindelof.right_half_plane_of_bounded_on_real
    (f := fun w => (scaledGamma w)⁻¹) ⟨hdiff, hcont⟩ ?_ ?_ norm_inv_scaledGamma_I_le hv
  · refine ⟨0, by norm_num, 0, ?_⟩
    refine Asymptotics.IsBigO.of_bound 2 ?_
    have : ∀ᶠ w : ℂ in Bornology.cobounded ℂ, 1 ≤ ‖w‖ :=
      tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop 1)
    filter_upwards [this.filter_mono inf_le_left, mem_inf_of_right (mem_principal_self _)]
      with w hw1 hw
    simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
    exact hfar w hw hw1
  · refine isBoundedUnder_of_eventually_le (a := 2) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx1 : 1 ≤ ‖(x : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact hx
    exact hfar x (by simp; linarith) hx1

/-! ### The reflection identity off the imaginary axis -/

theorem log_neg_eq_sub_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log (-w) = Complex.log w - π * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_sub_pi_of_im_pos hw]

/-- `Γ*(w) Γ*(−w) (1 − e^{2πiw}) = 1` for `ℑw > 0` (Nemes (1.9)). -/
theorem scaledGamma_mul_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    scaledGamma w * scaledGamma (-w) * (1 - cexp (2 * π * I * w)) = 1 := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  have hnw : -w ≠ 0 := neg_ne_zero.mpr hw0
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set E := cexp (π * I * w) with hEdef
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hE2 : cexp (2 * π * I * w) = E * E := by rw [hEdef, ← Complex.exp_add]; ring_nf
  have hsin : Complex.sin (π * w) = (E⁻¹ - E) * I / 2 := by
    rw [Complex.sin, hEdef, ← Complex.exp_neg]
    ring_nf
  have hE1 : E * E ≠ 1 := by
    intro h
    have hn : ‖E‖ < 1 := by
      rw [hEdef, norm_exp]
      have : (π * I * w).re = -(π * w.im) := by simp
      rw [this]
      have h := Real.exp_lt_exp.mpr (show -(π * w.im) < 0 by nlinarith [Real.pi_pos])
      rwa [Real.exp_zero] at h
    have := congrArg norm h
    rw [norm_mul, norm_one] at this
    nlinarith [norm_nonneg E]
  have hsin0 : Complex.sin (π * w) ≠ 0 := by
    rw [hsin]
    refine div_ne_zero (mul_ne_zero ?_ I_ne_zero) two_ne_zero
    intro h
    apply hE1
    have h' : E⁻¹ = E := sub_eq_zero.mp h
    calc E * E = E⁻¹ * E := by rw [h']
      _ = 1 := inv_mul_cancel₀ hE0
  have hrefl := Gamma_mul_Gamma_one_sub w
  rw [show 1 - w = -w + 1 by ring, Gamma_add_one _ hnw] at hrefl
  have hs : ((Real.sqrt (2 * π) : ℝ) : ℂ) * (Real.sqrt (2 * π) : ℝ) = 2 * π := by
    rw [← ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have he : cexp (-w) * cexp (-(-w)) = 1 := by rw [← Complex.exp_add]; simp
  have hX : cexp (Complex.log w * (w - 1 / 2)) * cexp ((Complex.log w - π * I) * (-w - 1 / 2)) =
      w⁻¹ * E * I := by
    rw [← Complex.exp_add, show Complex.log w * (w - 1 / 2) + (Complex.log w - π * I) *
      (-w - 1 / 2) = -Complex.log w + π * I * w + π / 2 * I by ring, Complex.exp_add,
      Complex.exp_add, Complex.exp_neg, Complex.exp_log hw0, exp_pi_div_two_mul_I]
  unfold scaledGamma
  rw [cpow_def_of_ne_zero hw0, cpow_def_of_ne_zero hnw, log_neg_eq_sub_of_im_pos hw, hE2]
  have hGG : Gamma w * Gamma (-w) = π / (Complex.sin (π * w) * -w) := by
    rw [eq_div_iff (mul_ne_zero hsin0 hnw)]
    have h := hrefl
    rw [eq_div_iff hsin0] at h
    linear_combination h
  have hden : (Real.sqrt (2 * π) : ℂ) * cexp (-w) * cexp (Complex.log w * (w - 1 / 2)) *
      ((Real.sqrt (2 * π) : ℂ) * cexp (-(-w)) * cexp ((Complex.log w - π * I) * (-w - 1 / 2))) =
      2 * π * (w⁻¹ * E * I) := by
    rw [← hX, ← hs]
    linear_combination (((Real.sqrt (2 * π) : ℝ) : ℂ) * (Real.sqrt (2 * π) : ℝ) *
      (cexp (Complex.log w * (w - 1 / 2)) * cexp ((Complex.log w - π * I) * (-w - 1 / 2)))) * he
  have hE1' : 1 - E ^ 2 ≠ 0 := by rw [sq]; exact sub_ne_zero.mpr (Ne.symm hE1)
  rw [div_mul_div_comm, hGG, hden, hsin]
  field_simp
  rw [I_sq]

/-- **Nemes, Lemma 2.2**: `|Γ*(w)| ≤ (1 − e^{−2πℑw})⁻¹` for `ℜw ≤ 0 < ℑw`. -/
theorem norm_scaledGamma_le_of_quadrant {w : ℂ} (hre : w.re ≤ 0) (him : 0 < w.im) :
    ‖scaledGamma w‖ ≤ (1 - Real.exp (-(2 * π * w.im)))⁻¹ := by
  have h := scaledGamma_mul_neg_of_im_pos him
  set D := 1 - cexp (2 * π * I * w)
  have hD : 1 - Real.exp (-(2 * π * w.im)) ≤ ‖D‖ := by
    have h1 : ‖cexp (2 * π * I * w)‖ = Real.exp (-(2 * π * w.im)) := by
      rw [norm_exp]; congr 1; simp
    have := norm_sub_norm_le (1 : ℂ) (cexp (2 * π * I * w))
    rw [norm_one, h1] at this
    exact this
  have hpos : 0 < 1 - Real.exp (-(2 * π * w.im)) := by
    have := Real.exp_lt_exp.mpr (show -(2 * π * w.im) < 0 by nlinarith [Real.pi_pos])
    rw [Real.exp_zero] at this
    linarith
  have hG : scaledGamma w = (scaledGamma (-w))⁻¹ * D⁻¹ := by
    rw [← mul_inv]
    exact eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h)
  have hinv := norm_inv_scaledGamma_le_one (v := -w) (by simp; linarith)
  rw [hG, norm_mul, norm_inv D]
  calc ‖(scaledGamma (-w))⁻¹‖ * ‖D‖⁻¹ ≤ 1 * (1 - Real.exp (-(2 * π * w.im)))⁻¹ := by
        gcongr
    _ = _ := one_mul _

/-! ### Rotation of a ray integral -/

/-- The integrand along the ray `ph s = ψ`: `r ↦ e^{iψ} f(re^{iψ})`. -/
noncomputable def rotRay (f : ℂ → ℂ) (ψ r : ℝ) : ℂ := cexp (ψ * I) * f (r * cexp (ψ * I))

/-- `f(e^w) e^w`: the integrand after `s = e^w`. -/
noncomputable def rotRect (f : ℂ → ℂ) (w : ℂ) : ℂ := f (cexp w) * cexp w

theorem cexp_add_mul_I' (x ψ : ℝ) : cexp ((x : ℂ) + ψ * I) = (Real.exp x : ℂ) * cexp (ψ * I) := by
  rw [Complex.exp_add, Complex.ofReal_exp]

theorem rotRect_eq (f : ℂ → ℂ) (x ψ : ℝ) :
    rotRect f ((x : ℂ) + ψ * I) = Real.exp x • rotRay f ψ (Real.exp x) := by
  rw [rotRect, cexp_add_mul_I', rotRay, Complex.real_smul]
  ring

/-- **Rotation of the path**: if `f` is holomorphic on the closed sector between the rays
`ph s = θ` and `ph s = θ'` (vertex removed) and `|f(re^{iψ})| ≤ C(1 + r^p)e^{−cr}` there, then the
integrals along the two rays agree. -/
theorem integral_rotRay_eq {f : ℂ → ℂ} {θ θ' : ℝ}
    (hd : ∀ r ψ : ℝ, 0 < r → ψ ∈ [[θ, θ']] → DifferentiableAt ℂ f (r * cexp (ψ * I)))
    {C c : ℝ} {p : ℕ} (hc : 0 < c)
    (hb : ∀ r ψ : ℝ, 0 < r → ψ ∈ [[θ, θ']] →
      ‖f (r * cexp (ψ * I))‖ ≤ C * ((1 + r ^ p) * Real.exp (-(c * r)))) :
    ∫ r in Ioi (0 : ℝ), rotRay f θ r = ∫ r in Ioi (0 : ℝ), rotRay f θ' r := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hb 1 θ one_pos left_mem_uIcc)
    have hpos : 0 < (1 + (1 : ℝ) ^ p) * Real.exp (-(c * 1)) := by positivity
    exact nonneg_of_mul_nonneg_left h hpos
  have hnorm : ∀ ψ r : ℝ, ‖rotRay f ψ r‖ = ‖f (r * cexp (ψ * I))‖ := fun ψ r => by
    rw [rotRay, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  have hcont : ∀ ψ ∈ [[θ, θ']], ContinuousOn (rotRay f ψ) (Ioi 0) := fun ψ hψ r hr =>
    (continuousAt_const.mul ((hd r ψ hr hψ).continuousAt.comp
      (f := fun r : ℝ => (r : ℂ) * cexp (ψ * I)) (by fun_prop))).continuousWithinAt
  have hint : ∀ ψ ∈ [[θ, θ']], IntegrableOn (rotRay f ψ) (Ioi 0) := fun ψ hψ => by
    have h0 := integrableOn_pow_mul_exp_neg_mul 0 hc
    have hp := integrableOn_pow_mul_exp_neg_mul p hc
    refine Integrable.mono' ((h0.add hp).const_mul C) ((hcont ψ hψ).aestronglyMeasurable
      measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun r hr => ?_))
    rw [hnorm]
    refine (hb r ψ hr hψ).trans (le_of_eq ?_)
    simp only [pow_zero, Pi.add_apply]
    ring
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hεdef
  set R : ℕ → ℝ := fun n => (n : ℝ) + 2 with hRdef
  have hε0 : ∀ n, 0 < ε n := fun n => by simp only [hεdef]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [hεdef]
    rw [div_le_one (by positivity)]
    linarith [n.cast_nonneg (α := ℝ)]
  have hR0 : ∀ n, 0 < R n := fun n => by simp only [hRdef]; positivity
  have hRt : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_const_nhds.div_atTop hRt
  have hlim : ∀ ψ ∈ [[θ, θ']], Tendsto (fun n => ∫ r in ε n..R n, rotRay f ψ r) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), rotRay f ψ r)) := by
    intro ψ hψ
    have hI := hint ψ hψ
    have hII : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable (rotRay f ψ) volume 0 b := fun b hb' =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb').mpr (hI.mono_set Ioc_subset_Ioi_self)
    have h1 : Tendsto (fun n => ∫ r in (0 : ℝ)..R n, rotRay f ψ r) atTop
        (𝓝 (∫ r in Ioi (0 : ℝ), rotRay f ψ r)) :=
      (intervalIntegral_tendsto_integral_Ioi 0 hI tendsto_id).comp hRt
    have hc' := intervalIntegral.continuousOn_primitive_interval
      (f := rotRay f ψ) (μ := volume) (a := 0) (b := 1)
      (by
        rw [uIcc_of_le zero_le_one]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp (hII 1 zero_le_one))
    have h2 : Tendsto (fun n => ∫ r in (0 : ℝ)..ε n, rotRay f ψ r) atTop (𝓝 0) := by
      have h3 := (hc' 0 left_mem_uIcc).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hεt, Eventually.of_forall fun n => (show ε n ∈ uIcc 0 1 by
          rw [uIcc_of_le zero_le_one]; exact ⟨(hε0 n).le, hε1 n⟩)⟩)
      simpa only [Function.comp_def, intervalIntegral.integral_same] using h3
    have h4 := h1.sub h2
    rw [sub_zero] at h4
    refine h4.congr fun n => ?_
    exact intervalIntegral.integral_interval_sub_left (hII _ (hR0 n).le) (hII _ (hε0 n).le)
  -- the change of variables `r = e^x`
  have hsub : ∀ ψ ∈ [[θ, θ']], ∀ n, ∫ x in Real.log (ε n)..Real.log (R n),
      rotRect f ((x : ℂ) + ψ * I) = ∫ r in ε n..R n, rotRay f ψ r := by
    intro ψ hψ n
    have h1 := intervalIntegral.integral_deriv_smul_comp' (a := Real.log (ε n))
      (b := Real.log (R n)) (f := Real.exp) (f' := Real.exp) (g := rotRay f ψ)
      (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
      ((hcont ψ hψ).mono fun r ⟨x, _, hx⟩ => hx ▸ Real.exp_pos x)
    rw [Real.exp_log (hε0 n), Real.exp_log (hR0 n)] at h1
    rw [← h1]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [rotRect_eq]
    rfl
  -- the arcs
  have hnorm_arc : ∀ ψ ∈ [[θ, θ']], ∀ x : ℝ, ‖rotRect f ((x : ℂ) + ψ * I)‖ ≤
      Real.exp x * (C * ((1 + Real.exp x ^ p) * Real.exp (-(c * Real.exp x)))) := by
    intro ψ hψ x
    rw [rotRect_eq, norm_smul, Real.norm_of_nonneg (Real.exp_pos x).le, hnorm]
    gcongr
    exact hb _ ψ (Real.exp_pos x) hψ
  have harcR : Tendsto (fun n => ∫ y in θ..θ', rotRect f ((Real.log (R n) : ℂ) + y * I))
      atTop (𝓝 0) := by
    have hbd : ∀ n, ‖∫ y in θ..θ', rotRect f ((Real.log (R n) : ℂ) + y * I)‖ ≤
        C * (R n ^ (1 : ℝ) * Real.exp (-c * R n) +
          R n ^ ((p + 1 : ℕ) : ℝ) * Real.exp (-c * R n)) * |θ' - θ| := by
      intro n
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      refine (hnorm_arc y (uIoc_subset_uIcc hy) _).trans (le_of_eq ?_)
      rw [Real.exp_log (hR0 n), Real.rpow_one, Real.rpow_natCast]
      ring_nf
    refine squeeze_zero_norm hbd ?_
    have t1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp hRt
    have t2 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((p + 1 : ℕ) : ℝ) c hc).comp hRt
    have t3 := ((t1.add t2).const_mul C).mul_const |θ' - θ|
    simp only [add_zero, mul_zero, zero_mul] at t3
    exact t3
  have harcε : Tendsto (fun n => ∫ y in θ..θ', rotRect f ((Real.log (ε n) : ℂ) + y * I))
      atTop (𝓝 0) := by
    have hbd : ∀ n, ‖∫ y in θ..θ', rotRect f ((Real.log (ε n) : ℂ) + y * I)‖ ≤
        2 * C * ε n * |θ' - θ| := by
      intro n
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      refine (hnorm_arc y (uIoc_subset_uIcc hy) _).trans ?_
      rw [Real.exp_log (hε0 n)]
      have hεn := hε0 n
      have hp1 : ε n ^ p ≤ 1 := pow_le_one₀ hεn.le (hε1 n)
      have he1 : Real.exp (-(c * ε n)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      calc ε n * (C * ((1 + ε n ^ p) * Real.exp (-(c * ε n))))
          ≤ ε n * (C * ((1 + 1) * 1)) := by gcongr
        _ = 2 * C * ε n := by ring
    refine squeeze_zero_norm hbd ?_
    have := ((hεt.const_mul (2 * C)).mul_const |θ' - θ|)
    simp only [mul_zero, zero_mul] at this
    exact this
  -- Cauchy's theorem on the rectangles
  have hdiff : ∀ n, DifferentiableOn ℂ (rotRect f)
      ([[Real.log (ε n), Real.log (R n)]] ×ℂ [[θ, θ']]) := by
    intro n w hw
    have hwim : w.im ∈ [[θ, θ']] := hw.2
    have hexp : cexp w = (Real.exp w.re : ℂ) * cexp (w.im * I) := by
      rw [← cexp_add_mul_I', re_add_im]
    have hf : DifferentiableAt ℂ f (cexp w) := by
      rw [hexp]; exact hd _ _ (Real.exp_pos _) hwim
    exact ((hf.comp w Complex.differentiable_exp.differentiableAt).mul
      Complex.differentiable_exp.differentiableAt).differentiableWithinAt
  have hcauchy : ∀ n, (∫ r in ε n..R n, rotRay f θ r) - (∫ r in ε n..R n, rotRay f θ' r) +
      I • (∫ y in θ..θ', rotRect f ((Real.log (R n) : ℂ) + y * I)) -
      I • (∫ y in θ..θ', rotRect f ((Real.log (ε n) : ℂ) + y * I)) = 0 := by
    intro n
    have hc' := integral_boundary_rect_eq_zero_of_differentiableOn (rotRect f)
      ((Real.log (ε n) : ℂ) + θ * I) ((Real.log (R n) : ℂ) + θ' * I) (by
        simpa using hdiff n)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hc'
    rwa [hsub θ left_mem_uIcc n, hsub θ' right_mem_uIcc n] at hc'
  have hA := (hlim θ left_mem_uIcc).sub (hlim θ' right_mem_uIcc)
  have hB : Tendsto (fun n => (∫ r in ε n..R n, rotRay f θ r) -
      (∫ r in ε n..R n, rotRay f θ' r)) atTop (𝓝 0) := by
    have := ((harcR.const_smul I).sub (harcε.const_smul I)).neg
    simp only [smul_zero, sub_zero, neg_zero] at this
    refine this.congr fun n => ?_
    linear_combination (hcauchy n).symm
  exact sub_eq_zero.mp (tendsto_nhds_unique hA hB)

/-- `∫₀^∞ f(r) dr = e^{iφ} ∫₀^∞ f(re^{iφ}) dr` under the hypotheses of `integral_rotRay_eq` on
`0 ≤ ph s ≤ φ`. -/
theorem integral_Ioi_rotate {f : ℂ → ℂ} {φ : ℝ} (hφ : 0 ≤ φ)
    (hd : ∀ r ψ : ℝ, 0 < r → ψ ∈ Icc 0 φ → DifferentiableAt ℂ f (r * cexp (ψ * I)))
    {C c : ℝ} {p : ℕ} (hc : 0 < c)
    (hb : ∀ r ψ : ℝ, 0 < r → ψ ∈ Icc 0 φ →
      ‖f (r * cexp (ψ * I))‖ ≤ C * ((1 + r ^ p) * Real.exp (-(c * r)))) :
    ∫ r in Ioi (0 : ℝ), f r = cexp (φ * I) * ∫ r in Ioi (0 : ℝ), f (r * cexp (φ * I)) := by
  rw [← uIcc_of_le hφ] at hd hb
  have h := integral_rotRay_eq hd hc hb
  simp only [rotRay, ofReal_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at h
  rw [h, integral_const_mul]

end Azurite.DLMF
