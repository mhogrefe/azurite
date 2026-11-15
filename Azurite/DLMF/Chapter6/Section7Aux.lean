/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section7Sine

/-!
# DLMF §6.7(iii): integral representations, auxiliary functions

Formalizations of <https://dlmf.nist.gov/6.7.iii>, equations 6.7.12–6.7.14.

The key identity is `g(z) ± i f(z) = e^{∓iz} E1Gen(ln z ∓ πi/2)` on the whole cut plane
(`auxG_add_I_mul_auxF`, from 6.5.7 by the identity theorem); `E1Gen(ln t ∓ πi/2)` is an
antiderivative of `−e^{±it}/t` with the cut along the negative real axis
(`hasDerivAt_E1Gen_log`).

* 6.7.12: `dlmf_6_7_12` (any contour off the cut with `ℑt → +∞`); `ph z = π`:
  `dlmf_6_7_12_cut` (vertical ray from `x < 0`, boundary value of `g + i f` from above, with
  Mathlib's `ln x = ln|x| + iπ`); `ph z = −π`: `dlmf_6_7_12_cut_neg` (arc from below the cut
  through the positive real axis, then the vertical ray; boundary value from below; value
  `E1Gen(ln x − πi/2) + 2πi`).
* 6.7.13, 6.7.14, first integrals (`|ph z| < π`, improper): `dlmf_6_7_13_first`,
  `dlmf_6_7_14_first`.
* 6.7.13, 6.7.14, second integrals (`ℜz ≥ 0`; `z ≠ 0` for 6.7.14): `dlmf_6_7_13_second`
  (Lebesgue), `dlmf_6_7_14_second` (improper; Lebesgue for `ℜz > 0`), via the logarithm
  `ln z + ln(t ± i)` of `z(t ± i)` (`tendsto_integral_laplace`, `tendsto_integral_of_E1Gen_lift`).
* 6.7.15, 6.7.16 (`K₀`, §10.25(ii)): deferred to Chapter 10.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Closed forms of `g ± i f` on the cut plane -/

/-- `E1Gen′(w) = −e^{−e^w}`. -/
theorem hasDerivAt_E1Gen (w : ℂ) : HasDerivAt E1Gen (-cexp (-cexp w)) w := by
  have h := (((hasDerivAt_ein (cexp w)).comp w (hasDerivAt_exp w)).sub (hasDerivAt_id w)).sub_const
    (γ : ℂ)
  refine h.congr_deriv ?_
  rw [EinDeriv_mul_self]
  simp

theorem differentiableOn_auxF : DifferentiableOn ℂ auxF slitPlane := fun z hz =>
  ((((hasDerivAt_Ci hz).differentiableAt.mul Complex.differentiable_sin.differentiableAt).sub
    ((differentiable_si z).mul Complex.differentiable_cos.differentiableAt))).differentiableWithinAt

theorem differentiableOn_auxG : DifferentiableOn ℂ auxG slitPlane := fun z hz =>
  ((((hasDerivAt_Ci hz).differentiableAt.neg.mul Complex.differentiable_cos.differentiableAt).sub
    ((differentiable_si z).mul Complex.differentiable_sin.differentiableAt))).differentiableWithinAt

theorem differentiableOn_E1Gen_log (c : ℂ) :
    DifferentiableOn ℂ (fun z => E1Gen (log z + c)) slitPlane := fun z hz =>
  ((hasDerivAt_E1Gen _).differentiableAt.comp z
    (((hasDerivAt_log hz).add_const c).differentiableAt)).differentiableWithinAt

/-- Two functions analytic on the cut plane that agree on `ℜz > 0` agree on the cut plane. -/
theorem eqOn_slitPlane_of_re_pos {F G : ℂ → ℂ} (hF : DifferentiableOn ℂ F slitPlane)
    (hG : DifferentiableOn ℂ G slitPlane) (h : ∀ z : ℂ, 0 < z.re → F z = G z) :
    EqOn F G slitPlane := by
  have hev : F =ᶠ[𝓝 1] G := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (0 : ℝ) < (1 : ℂ).re by simp)] with z hz using h z hz
  exact (hF.analyticOnNhd isOpen_slitPlane).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd isOpen_slitPlane) isPreconnected_slitPlane
    (mem_slitPlane_iff.mpr (Or.inl (by simp))) hev

/-- `g(z) ± i f(z) = e^{∓iz} E₁(z e^{∓πi/2})` on the cut plane, with the general value `E1Gen`
at the logarithm `ln z ∓ πi/2` (the continuation of 6.5.7). -/
theorem auxG_add_I_mul_auxF {z : ℂ} (hz : z ∈ slitPlane) :
    auxG z + I * auxF z = cexp (-I * z) * E1Gen (log z + -(π / 2 * I)) ∧
      auxG z - I * auxF z = cexp (I * z) * E1Gen (log z + π / 2 * I) := by
  have hprin : ∀ w ∈ slitPlane, E1Gen (log w) = expIntE₁ w := fun w hw => by
    have := (dlmf_6_4_1).2.1 _ (log_mem_logStrip hw)
    rwa [exp_log (slitPlane_ne_zero hw)] at this
  constructor
  · refine eqOn_slitPlane_of_re_pos (F := fun z => auxG z + I * auxF z)
      (G := fun z => cexp (-I * z) * E1Gen (log z + -(π / 2 * I)))
      (differentiableOn_auxG.add (differentiableOn_auxF.const_mul I))
      ((by fun_prop : Differentiable ℂ fun z => cexp (-I * z)).differentiableOn.mul
        (differentiableOn_E1Gen_log _)) (fun w hw => ?_) hz
    rw [(dlmf_6_5_7 hw).1, ← sub_eq_add_neg, ← (log_I_mul hw).2,
      hprin _ (neg_I_mul_mem_slitPlane hw)]
    ring
  · refine eqOn_slitPlane_of_re_pos (F := fun z => auxG z - I * auxF z)
      (G := fun z => cexp (I * z) * E1Gen (log z + π / 2 * I))
      (differentiableOn_auxG.sub (differentiableOn_auxF.const_mul I))
      ((by fun_prop : Differentiable ℂ fun z => cexp (I * z)).differentiableOn.mul
        (differentiableOn_E1Gen_log _)) (fun w hw => ?_) hz
    rw [(dlmf_6_5_7 hw).2, ← (log_I_mul hw).1, hprin _ (I_mul_mem_slitPlane hw)]
    ring

/-! ### Antiderivatives of `e^{±it}/t` -/

theorem exp_log_add_half_pi {u : ℂ} (hu : u ≠ 0) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    cexp (log u + σ * (π / 2 * I)) = σ * I * u := by
  rw [exp_add, exp_log hu]
  rcases hσ with rfl | rfl
  · rw [one_mul, show (π / 2 * I : ℂ) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring,
      exp_pi_div_two_mul_I']
    ring
  · rw [show (-1 : ℂ) * (π / 2 * I) = -(((π / 2 : ℝ) : ℂ) * I) by push_cast; ring, exp_neg,
      exp_pi_div_two_mul_I', inv_I]
    ring

/-- `d/du E1Gen(ln u ± πi/2) = −e^{∓iu}/u` off the cut. -/
theorem hasDerivAt_E1Gen_log {u : ℂ} (hu : u ∈ slitPlane) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    HasDerivAt (fun u => E1Gen (log u + σ * (π / 2 * I))) (-cexp (-(σ * I * u)) / u) u := by
  have hu0 := slitPlane_ne_zero hu
  have h := (hasDerivAt_E1Gen _).comp u ((hasDerivAt_log hu).add_const (σ * (π / 2 * I)))
  refine h.congr_deriv ?_
  rw [exp_log_add_half_pi hu0 σ hσ]
  field_simp

/-- `E1Gen(ln u ± πi/2) → 0` as `ℜu → ∞` with `ℑu` bounded. -/
theorem tendsto_E1Gen_log_horizontal (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (z : ℂ) :
    Tendsto (fun R : ℝ => E1Gen (log (z + R) + σ * (π / 2 * I))) atTop (𝓝 0) := by
  have hre : Tendsto (fun R : ℝ => (z + R).re) atTop atTop := by
    simpa using tendsto_atTop_add_const_left _ z.re tendsto_id
  have hpos : ∀ᶠ R : ℝ in atTop, 0 < (z + R).re := hre.eventually (eventually_gt_atTop 0)
  -- on `ℜu > 0`: `E1Gen(ln u ± πi/2) = E₁(±iu)`
  have heq : ∀ᶠ R : ℝ in atTop,
      E1Gen (log (z + R) + σ * (π / 2 * I)) = expIntE₁ (σ * I * (z + R)) := by
    filter_upwards [hpos] with R hR
    have ha := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hR))
    have hs : log (z + R) + σ * (π / 2 * I) ∈ logStrip := by
      have hpi := Real.pi_pos
      show -π < _ ∧ _ < π
      rcases hσ with rfl | rfl <;> simp [log_im] <;> constructor <;> linarith [ha.1, ha.2]
    rw [(dlmf_6_4_1).2.1 _ hs, exp_log_add_half_pi (fun h => by simp [h] at hR) σ hσ]
  have hσim : ∀ R : ℝ, |(σ * I * (z + R)).im| = |(z + R).re| := fun R => by
    rcases hσ with rfl | rfl
    · simp
    · simp only [mul_im, mul_re, neg_re, neg_im, one_re, one_im, I_re, I_im, add_re, add_im,
        ofReal_re, ofReal_im]
      rw [← abs_neg]
      ring_nf
  have hσre : ∀ R : ℝ, (σ * I * (z + R)).re = -σ.re * z.im := fun R => by
    rcases hσ with rfl | rfl <;> simp
  refine (tendsto_expIntE₁_zero (w := fun R : ℝ => σ * I * (z + R)) ?_ (r₀ := -σ.re * z.im)
    (Eventually.of_forall fun R => (hσre R).ge) ?_).congr' (heq.mono fun R h => h.symm)
  · filter_upwards [hpos] with R hR
    refine mem_slitPlane_iff.mpr (Or.inr fun h => ?_)
    have := hσim R
    rw [h, abs_zero] at this
    have := abs_pos.mpr hR.ne'
    linarith
  · refine tendsto_atTop_mono (fun R => le_max_left _ _) ?_
    simp only [hσim]
    exact tendsto_abs_atTop_atTop.comp hre

/-- `∫_0^∞ e^{±it}/(t + z) dt = e^{∓iz} E1Gen(ln z ± πi/2)` (improper), `z` off the cut. -/
theorem tendsto_integral_exp_div_add {z : ℂ} (hz : z ∈ slitPlane) (σ : ℂ)
    (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-σ * I * t) / (t + z)) atTop
      (𝓝 (cexp (σ * I * z) * E1Gen (log z + σ * (π / 2 * I)))) := by
  set H := fun u => E1Gen (log u + σ * (π / 2 * I))
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hftc : ∀ R : ℝ, 0 ≤ R → ∫ t in (0 : ℝ)..R, cexp (-σ * I * t) / (t + z) =
      cexp (σ * I * z) * (H z - H (z + R)) := by
    intro R hR
    have hd : ∀ t ∈ uIcc (0 : ℝ) R, HasDerivAt (fun t : ℝ => -cexp (σ * I * z) * H (z + t))
        (cexp (-σ * I * t) / (t + z)) t := by
      intro t ht
      rw [uIcc_of_le hR] at ht
      have hw := add_ofReal_mem_slitPlane hz ht.1
      have h1 : HasDerivAt (fun v : ℂ => -cexp (σ * I * z) * H (z + v))
          (cexp (-σ * I * t) / (t + z)) (t : ℂ) := by
        have := ((hasDerivAt_E1Gen_log hw σ hσ).comp (t : ℂ)
          ((hasDerivAt_id (t : ℂ)).const_add z)).const_mul (-cexp (σ * I * z))
        refine this.congr_deriv ?_
        have hne := slitPlane_ne_zero hw
        rw [show -(σ * I * (z + t)) = -(σ * I * z) + -σ * I * t by ring, exp_add]
        simp only [mul_one]
        rw [add_comm (t : ℂ) z]
        have hee : cexp (σ * I * z) * cexp (-(σ * I * z)) = 1 := by
          rw [← exp_add, add_neg_cancel, exp_zero]
        field_simp
        linear_combination hee
      exact h1.comp_ofReal
    have hc : ContinuousOn (fun t : ℝ => cexp (-σ * I * t) / (t + z)) (uIcc 0 R) := by
      intro t ht
      rw [uIcc_of_le hR] at ht
      have hne := slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht.1)
      rw [add_comm] at hne
      exact ((by fun_prop : Continuous fun t : ℝ => cexp (-σ * I * t)).continuousAt.div
        (continuous_ofReal.add continuous_const).continuousAt hne).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
    simp only [ofReal_zero, add_zero]
    ring
  have hlim := ((tendsto_E1Gen_log_horizontal σ hσ z).const_sub (H z)).const_mul
    (cexp (σ * I * z))
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  exact (hftc R hR).symm

/-! ### 6.7.12, 6.7.13, 6.7.14 (first integrals) -/

/-- **DLMF 6.7.12**: `g(z) + i f(z) = e^{−iz} ∫_z^∞ e^{it}/t dt`, `z` off the cut: along any
contour from `z` that stays off the cut and goes to infinity with `ℑt → +∞` (where `e^{it}`
decays), the integral converges to `E1Gen(ln z − πi/2)`, and `g + i f = e^{−iz}` times it. -/
theorem dlmf_6_7_12 {z : ℂ} {c : ℝ → ℂ} {a : ℝ} (hca : c a = z)
    (hc : ∀ b, a ≤ b → IsContour c a b) (hcU : ∀ t, a ≤ t → c t ∈ slitPlane)
    (him : Tendsto (fun t => (c t).im) atTop atTop) :
    ContourConvergesAtTop (fun t => cexp (I * t) / t) c a (E1Gen (log z + -(π / 2 * I))) ∧
      auxG z + I * auxF z = cexp (-I * z) * E1Gen (log z + -(π / 2 * I)) := by
  have hz : z ∈ slitPlane := hca ▸ hcU a le_rfl
  refine ⟨?_, (auxG_add_I_mul_auxF hz).1⟩
  set H := fun u => E1Gen (log u + -1 * (π / 2 * I))
  have hF : ∀ w ∈ slitPlane, HasDerivAt (fun u => -H u) (cexp (I * w) / w) w := by
    intro w hw
    have := (hasDerivAt_E1Gen_log hw (-1) (Or.inr rfl)).neg
    refine this.congr_deriv ?_
    rw [neg_div, neg_neg]
    ring_nf
  have hf : ContinuousOn (fun w : ℂ => cexp (I * w) / w) slitPlane := fun w hw =>
    ((by fun_prop : Continuous fun w : ℂ => cexp (I * w)).continuousAt.div continuousAt_id
      (slitPlane_ne_zero hw)).continuousWithinAt
  -- `H(c(b)) → 0`: eventually `H(c) = E₁(−ic)` with `ℜ(−ic) = ℑc → ∞`
  have hpos : ∀ᶠ t in atTop, 0 < (c t).im := him.eventually (eventually_gt_atTop 0)
  have heq : ∀ᶠ t in atTop, H (c t) = expIntE₁ (-I * c t) := by
    filter_upwards [hpos] with t ht
    have hpi := Real.pi_pos
    have h1 := arg_lt_pi_iff.mpr (Or.inr ht.ne')
    have h2 := (arg_nonneg_iff.mpr ht.le)
    have h3 : 0 < arg (c t) := by
      rcases h2.eq_or_lt with h | h
      · exact absurd (arg_eq_zero_iff.mp h.symm).2 (by linarith)
      · exact h
    have hs : log (c t) + -1 * (π / 2 * I) ∈ logStrip := by
      show -π < _ ∧ _ < π
      simp [log_im]
      constructor <;> linarith [arg_le_pi (c t)]
    simp only [H]
    rw [(dlmf_6_4_1).2.1 _ hs, exp_log_add_half_pi (fun h => by simp [h] at ht) (-1)
      (Or.inr rfl)]
    ring_nf
  have hdec : Tendsto (fun t => H (c t)) atTop (𝓝 0) := by
    have hre : ∀ t, (-I * c t).re = (c t).im := fun t => by simp
    refine (tendsto_expIntE₁_zero (w := fun t => -I * c t) ?_ (r₀ := 0) ?_ ?_).congr'
      (heq.mono fun t h => h.symm)
    · filter_upwards [hpos] with t ht
      exact mem_slitPlane_of_re_pos (by rw [hre]; exact ht)
    · filter_upwards [hpos] with t ht
      rw [hre]; exact ht.le
    · exact tendsto_atTop_mono (fun t => (hre t).symm ▸ le_max_right _ _) him
  have hHz : H z = E1Gen (log z + -(π / 2 * I)) := by simp only [H]; ring_nf
  have h := (hdec.const_sub (H z))
  rw [sub_zero, hHz] at h
  unfold ContourConvergesAtTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop a] with b hb
  rw [contourIntegral_eq_sub_of_hasDerivAt (hc b hb) (fun t ht => hcU t ht.1) hF hf, hca, ← hHz]
  ring

/-- Linearity of improper integrals, for integrands integrable on `[x, R]`. -/
theorem tendsto_integral_lin' {g₁ g₂ f : ℝ → ℂ} {x : ℝ} {L₁ L₂ κ₁ κ₂ : ℂ}
    (hg₁ : ∀ R, x ≤ R → IntervalIntegrable g₁ volume x R)
    (hg₂ : ∀ R, x ≤ R → IntervalIntegrable g₂ volume x R)
    (h₁ : Tendsto (fun R => ∫ t in x..R, g₁ t) atTop (𝓝 L₁))
    (h₂ : Tendsto (fun R => ∫ t in x..R, g₂ t) atTop (𝓝 L₂))
    (hf : ∀ t, x ≤ t → f t = κ₁ * g₁ t + κ₂ * g₂ t) :
    Tendsto (fun R => ∫ t in x..R, f t) atTop (𝓝 (κ₁ * L₁ + κ₂ * L₂)) := by
  refine ((h₁.const_mul κ₁).add (h₂.const_mul κ₂)).congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hg₁ R hR).const_mul _) ((hg₂ R hR).const_mul _)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hR] at ht
  exact (hf t ht.1).symm

theorem intervalIntegrable_exp_div_add {z : ℂ} (hz : z ∈ slitPlane) (σ : ℂ) {R : ℝ}
    (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ => cexp (-σ * I * t) / (t + z)) volume 0 R := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  rw [uIcc_of_le hR] at ht
  have hne := slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht.1)
  rw [add_comm] at hne
  exact ((by fun_prop : Continuous fun t : ℝ => cexp (-σ * I * t)).continuousAt.div
    (continuous_ofReal.add continuous_const).continuousAt hne).continuousWithinAt

/-- `E1Gen(ln w − πi/2) → 0` as `ℑw → +∞` (there it is `E₁(−iw)` with `ℜ(−iw) = ℑw`). -/
theorem tendsto_E1Gen_log_upper {α : Type*} {l : Filter α} {w : α → ℂ}
    (him : Tendsto (fun t => (w t).im) l atTop) :
    Tendsto (fun t => E1Gen (log (w t) + -(π / 2 * I))) l (𝓝 0) := by
  have hpos : ∀ᶠ t in l, 0 < (w t).im := him.eventually (eventually_gt_atTop 0)
  have heq : ∀ᶠ t in l, E1Gen (log (w t) + -(π / 2 * I)) = expIntE₁ (-I * w t) := by
    filter_upwards [hpos] with t ht
    have hpi := Real.pi_pos
    have h2 := arg_nonneg_iff.mpr ht.le
    have hs : log (w t) + -(π / 2 * I) ∈ logStrip := by
      show -π < _ ∧ _ < π
      simp [log_im]
      constructor <;> linarith [arg_le_pi (w t)]
    rw [(dlmf_6_4_1).2.1 _ hs, show -(π / 2 * I : ℂ) = -1 * (π / 2 * I) by ring,
      exp_log_add_half_pi (fun h => by simp [h] at ht) (-1) (Or.inr rfl)]
    ring_nf
  have hre : ∀ t, (-I * w t).re = (w t).im := fun t => by simp
  refine (tendsto_expIntE₁_zero (w := fun t => -I * w t) ?_ (r₀ := 0) ?_ ?_).congr'
    (heq.mono fun t h => h.symm)
  · filter_upwards [hpos] with t ht
    exact mem_slitPlane_of_re_pos (by rw [hre]; exact ht)
  · filter_upwards [hpos] with t ht
    rw [hre]; exact ht.le
  · exact tendsto_atTop_mono (fun t => (hre t).symm ▸ le_max_right _ _) him

/-- **DLMF 6.7.12** at `ph z = π` (`z = x < 0`, the boundary value from above; Mathlib's
`ln x = ln|x| + iπ`): along the vertical ray `t = x + is`, `s ≥ 0`, which does not cross the
negative real axis, `∫_x^∞ e^{it}/t dt` converges to `E1Gen(ln x − πi/2)`, and
`g(z) + i f(z) → e^{−ix}` times it as `z → x` from the upper half-plane. -/
theorem dlmf_6_7_12_cut {x : ℝ} (hx : x < 0) :
    Tendsto (fun R => ∫ s in (0 : ℝ)..R, cexp (I * (x + s * I)) / (x + s * I) * I) atTop
        (𝓝 (E1Gen (log x + -(π / 2 * I)))) ∧
      Tendsto (fun z => auxG z + I * auxF z) (𝓝[{z | 0 < z.im}] (x : ℂ))
        (𝓝 (cexp (-I * x) * E1Gen (log x + -(π / 2 * I)))) := by
  set H : ℂ → ℂ := fun w => E1Gen (log w + -(π / 2 * I)) with hH
  have hlog : ContinuousWithinAt log {z : ℂ | 0 ≤ z.im} (x : ℂ) :=
    continuousWithinAt_log_of_re_neg_of_im_zero (by simpa using hx) (by simp)
  have hHc : ContinuousWithinAt H {z : ℂ | 0 ≤ z.im} (x : ℂ) :=
    ((hasDerivAt_E1Gen _).continuousAt).comp_continuousWithinAt
      (hlog.add continuousWithinAt_const)
  constructor
  · set p : ℝ → ℂ := fun s => (x : ℂ) + s * I with hp
    have hpne : ∀ s : ℝ, p s ≠ 0 := fun s h => by
      have := congrArg Complex.re h; simp [hp] at this; linarith
    have hps : ∀ s : ℝ, 0 < s → p s ∈ slitPlane := fun s hs =>
      mem_slitPlane_iff.mpr (Or.inr (by simp [hp]; exact hs.ne'))
    have hd : ∀ s : ℝ, 0 < s → HasDerivAt (fun s => -H (p s))
        (cexp (I * (x + s * I)) / (x + s * I) * I) s := by
      intro s hs
      have hfun : (fun u => E1Gen (log u + -1 * (π / 2 * I))) = H := by
        funext u; simp only [hH]; ring_nf
      have h1 : HasDerivAt (fun v : ℂ => -H ((x : ℂ) + v * I))
          (cexp (I * (x + s * I)) / (x + s * I) * I) (s : ℂ) := by
        have h0 := hasDerivAt_E1Gen_log (hps s hs) (-1) (Or.inr rfl)
        rw [hfun] at h0
        have := (h0.comp (s : ℂ) (((hasDerivAt_id (s : ℂ)).mul_const I).const_add (x : ℂ))).neg
        simp only [Function.comp_def, id, Pi.neg_def] at this
        refine this.congr_deriv ?_
        simp only [hp, one_mul]
        ring_nf
      exact h1.comp_ofReal
    have hcontH : ∀ R : ℝ, 0 ≤ R → ContinuousOn (fun s => -H (p s)) (Icc 0 R) := by
      intro R _ s hs
      rcases hs.1.eq_or_lt with rfl | hs0
      · have hpc : ContinuousWithinAt p (Icc 0 R) 0 :=
          (by fun_prop : Continuous p).continuousWithinAt
        have hmaps : MapsTo p (Icc 0 R) {z : ℂ | 0 ≤ z.im} := fun s hs => by
          simp [hp]; exact hs.1
        exact (hHc.comp_of_eq hpc hmaps (by simp [hp])).neg
      · exact (hd s hs0).continuousAt.continuousWithinAt
    have hint : ∀ R : ℝ, IntervalIntegrable (fun s : ℝ => cexp (I * (x + s * I)) / (x + s * I) * I)
        volume 0 R := fun R =>
      ((by fun_prop : Continuous fun s : ℝ => cexp (I * (x + s * I))).div
        (by fun_prop : Continuous fun s : ℝ => (x : ℂ) + s * I) hpne |>.mul continuous_const)
        |>.intervalIntegrable _ _
    have hftc : ∀ R : ℝ, 0 ≤ R →
        ∫ s in (0 : ℝ)..R, cexp (I * (x + s * I)) / (x + s * I) * I = H x - H (p R) := by
      intro R hR
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR (hcontH R hR)
        (fun s hs => hd s hs.1) (hint R)]
      simp [hp]
      ring
    have hdec : Tendsto (fun R : ℝ => H (p R)) atTop (𝓝 0) :=
      tendsto_E1Gen_log_upper (w := p) (by
        have e : (fun R : ℝ => (p R).im) = id := funext fun R => by simp [hp]
        rw [e]
        exact tendsto_id)
    have h := hdec.const_sub (H x)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    exact (hftc R hR).symm
  · have hR : Tendsto (fun z => cexp (-I * z) * H z) (𝓝[{z | 0 < z.im}] (x : ℂ))
        (𝓝 (cexp (-I * x) * H x)) :=
      (((by fun_prop : Continuous fun z : ℂ => cexp (-I * z)).tendsto _).mono_left
        nhdsWithin_le_nhds).mul ((hHc.mono fun z (hz : 0 < z.im) => hz.le).tendsto)
    refine hR.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z.im)
    exact ((auxG_add_I_mul_auxF (mem_slitPlane_iff.mpr (Or.inr hz.ne'))).1).symm

/-- The vertical ray from a point `w₀` of the upper half-plane:
`∫_{w₀}^{w₀ + i∞} e^{it}/t dt = E1Gen(ln w₀ − πi/2)` (improper). -/
theorem tendsto_vertical_ray {w₀ : ℂ} (hw₀ : 0 < w₀.im) :
    Tendsto (fun R => ∫ s in (0 : ℝ)..R, cexp (I * (w₀ + s * I)) / (w₀ + s * I) * I) atTop
      (𝓝 (E1Gen (log w₀ + -(π / 2 * I)))) := by
  set H : ℂ → ℂ := fun w => E1Gen (log w + -(π / 2 * I)) with hH
  set p : ℝ → ℂ := fun s => w₀ + s * I with hp
  have hpim : ∀ s : ℝ, 0 ≤ s → 0 < (p s).im := fun s hs => by simp [hp]; linarith
  have hps : ∀ s : ℝ, 0 ≤ s → p s ∈ slitPlane := fun s hs =>
    mem_slitPlane_iff.mpr (Or.inr (hpim s hs).ne')
  have hfun : (fun u => E1Gen (log u + -1 * (π / 2 * I))) = H := by
    funext u; simp only [hH]; ring_nf
  have hd : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun s => -H (p s))
      (cexp (I * (w₀ + s * I)) / (w₀ + s * I) * I) s := by
    intro s hs
    have h1 : HasDerivAt (fun v : ℂ => -H (w₀ + v * I))
        (cexp (I * (w₀ + s * I)) / (w₀ + s * I) * I) (s : ℂ) := by
      have h0 := hasDerivAt_E1Gen_log (hps s hs) (-1) (Or.inr rfl)
      rw [hfun] at h0
      have := (h0.comp (s : ℂ) (((hasDerivAt_id (s : ℂ)).mul_const I).const_add w₀)).neg
      simp only [Function.comp_def, id, Pi.neg_def] at this
      refine this.congr_deriv ?_
      simp only [hp, one_mul]
      ring_nf
    exact h1.comp_ofReal
  have hftc : ∀ R : ℝ, 0 ≤ R →
      ∫ s in (0 : ℝ)..R, cexp (I * (w₀ + s * I)) / (w₀ + s * I) * I = H w₀ - H (p R) := by
    intro R hR
    have hc : ContinuousOn (fun s : ℝ => cexp (I * (w₀ + s * I)) / (w₀ + s * I) * I)
        (uIcc 0 R) := fun s hs => by
      rw [uIcc_of_le hR] at hs
      exact ((((by fun_prop : Continuous fun s : ℝ => cexp (I * (w₀ + s * I))).continuousAt.div
          (by fun_prop : Continuous fun s : ℝ => w₀ + s * I).continuousAt
          (slitPlane_ne_zero (hps s hs.1))).mul continuousAt_const).continuousWithinAt)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => by
      rw [uIcc_of_le hR] at hs; exact hd s hs.1) hc.intervalIntegrable]
    simp [hp]
    ring
  have hdec : Tendsto (fun R : ℝ => H (p R)) atTop (𝓝 0) :=
    tendsto_E1Gen_log_upper (w := p) (by
      have e : (fun R : ℝ => (p R).im) = fun R => R + w₀.im := funext fun R => by
        simp [hp]; ring
      rw [e]
      exact tendsto_atTop_add_const_right _ _ tendsto_id)
  have h := hdec.const_sub (H w₀)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  exact (hftc R hR).symm

/-- **DLMF 6.7.12** at `ph z = −π` (`z = x < 0`, the boundary value from below).  The path
from `x` to `+i∞` that does not cross the negative real axis: the arc `|x| e^{i(s − π)}`,
`0 ≤ s ≤ 3π/2` (from below the cut, through the positive real axis, to `i|x|`), then the
vertical ray from `i|x|`.  Along it `∫_x^∞ e^{it}/t dt = E1Gen(ln|x| − πi − πi/2)`
`= E1Gen(ln x − πi/2) + 2πi` (6.4.2), and `g(z) + i f(z) → e^{−ix}` times it as `z → x` from the
lower half-plane. -/
theorem dlmf_6_7_12_cut_neg {x : ℝ} (hx : x < 0) :
    Tendsto (fun R =>
        (∫ s in (0 : ℝ)..3 * π / 2, cexp (I * ((-x : ℝ) * cexp ((s - π) * I))) /
            ((-x : ℝ) * cexp ((s - π) * I)) * ((-x : ℝ) * cexp ((s - π) * I) * I)) +
          ∫ s in (0 : ℝ)..R, cexp (I * (I * (-x : ℝ) + s * I)) / (I * (-x : ℝ) + s * I) * I)
        atTop (𝓝 (E1Gen (Real.log (-x) - π * I + -(π / 2 * I)))) ∧
      Tendsto (fun z => auxG z + I * auxF z) (𝓝[{z | z.im < 0}] (x : ℂ))
        (𝓝 (cexp (-I * x) * E1Gen (Real.log (-x) - π * I + -(π / 2 * I)))) ∧
      E1Gen (Real.log (-x) - π * I + -(π / 2 * I)) =
        E1Gen (log x + -(π / 2 * I)) + 2 * π * I := by
  have hr : 0 < -x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- the arc, with the logarithm `L(s) = ln|x| + i(s − π)`
    set L : ℝ → ℂ := fun s => (Real.log (-x) : ℂ) + (s - π) * I with hL
    set q : ℝ → ℂ := fun s => ((-x : ℝ) : ℂ) * cexp ((s - π) * I) with hq
    have hLq : ∀ s, cexp (L s) = q s := fun s => by
      simp only [hL, hq]
      rw [exp_add, ← ofReal_exp, Real.exp_log hr]
    have hd : ∀ s : ℝ, HasDerivAt (fun s => -E1Gen (L s + -(π / 2 * I)))
        (cexp (I * q s) / q s * (q s * I)) s := by
      intro s
      have hq0 : q s ≠ 0 := by rw [← hLq]; exact exp_ne_zero _
      have hLd : HasDerivAt (fun v : ℂ => (Real.log (-x) : ℂ) + (v - π) * I + -(π / 2 * I)) I
          (s : ℂ) := by
        have := (((hasDerivAt_id (s : ℂ)).sub_const (π : ℂ)).mul_const I).const_add
          (Real.log (-x) : ℂ) |>.add_const (-(π / 2 * I))
        simpa using this
      have h1 := ((hasDerivAt_E1Gen _).comp (s : ℂ) hLd).neg.comp_ofReal
      refine h1.congr_deriv ?_
      have e : cexp ((Real.log (-x) : ℂ) + ((s : ℂ) - π) * I + -(π / 2 * I)) = -I * q s := by
        rw [exp_add, show ((Real.log (-x) : ℂ) + ((s : ℂ) - π) * I) = L s by simp [hL], hLq,
          show -(π / 2 * I : ℂ) = -1 * (π / 2 * I) by ring]
        have := exp_log_add_half_pi (u := 1) one_ne_zero (-1) (Or.inr rfl)
        rw [log_one, zero_add, mul_one] at this
        rw [this]
        ring
      rw [e]
      field_simp
    have harc : ∫ s in (0 : ℝ)..3 * π / 2, cexp (I * q s) / q s * (q s * I) =
        E1Gen (L 0 + -(π / 2 * I)) - E1Gen (L (3 * π / 2) + -(π / 2 * I)) := by
      have hc : Continuous fun s => cexp (I * q s) / q s * (q s * I) := by
        refine ((by fun_prop : Continuous fun s => cexp (I * q s)).div (by fun_prop)
          fun s => ?_).mul (by fun_prop)
        rw [← hLq]; exact exp_ne_zero _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
        (hc.intervalIntegrable _ _)]
      ring
    have hL0 : L 0 = (Real.log (-x) : ℂ) - π * I := by simp [hL]; ring
    have hLend : L (3 * π / 2) + -(π / 2 * I) = log (I * (-x : ℝ)) + -(π / 2 * I) := by
      rw [show I * ((-x : ℝ) : ℂ) = ((-x : ℝ) : ℂ) * I by ring, log_ofReal_mul hr I_ne_zero,
        log_I]
      simp only [hL]
      push_cast
      ring
    have hray := tendsto_vertical_ray (w₀ := I * (-x : ℝ)) (by simpa using hr)
    have h := hray.const_add (E1Gen (L 0 + -(π / 2 * I)) - E1Gen (L (3 * π / 2) + -(π / 2 * I)))
    rw [hLend, sub_add_cancel, hL0] at h
    rw [hL0, hLend] at harc
    refine h.congr fun R => ?_
    rw [← harc]
  · -- the boundary value from below
    have hnorm : ‖(x : ℂ)‖ = -x := by rw [norm_real, Real.norm_eq_abs, abs_of_neg hx]
    have hlog := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (show (x : ℂ).re < 0 by simpa using hx) (ofReal_im x)
    rw [hnorm] at hlog
    have hR : Tendsto (fun z => cexp (-I * z) * E1Gen (log z + -(π / 2 * I)))
        (𝓝[{z | z.im < 0}] (x : ℂ))
        (𝓝 (cexp (-I * x) * E1Gen (Real.log (-x) - π * I + -(π / 2 * I)))) :=
      (((by fun_prop : Continuous fun z : ℂ => cexp (-I * z)).tendsto _).mono_left
        nhdsWithin_le_nhds).mul
        (((hasDerivAt_E1Gen _).continuousAt.tendsto).comp (hlog.add_const _))
    refine hR.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : z.im < 0)
    exact ((auxG_add_I_mul_auxF (mem_slitPlane_iff.mpr (Or.inr hz.ne))).1).symm
  · -- 6.4.2 with `m = −1`
    have hlx : log (x : ℂ) = Real.log (-x) + π * I := by
      apply Complex.ext
      · simp [log_re, abs_of_neg hx]
      · simp [log_im, arg_ofReal_of_neg hx]
    have h := dlmf_6_4_2 (log x + -(π / 2 * I)) (-1)
    rw [hlx] at h ⊢
    convert h using 2 <;> push_cast <;> ring

/-- **DLMF 6.7.13** (first integral): `f(z) = ∫_0^∞ sin t/(t + z) dt`, `|ph z| < π` (improper). -/
theorem dlmf_6_7_13_first {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, Complex.sin t / (t + z)) atTop (𝓝 (auxF z)) := by
  have hp := tendsto_integral_exp_div_add hz (-1) (Or.inr rfl)
  have hm := tendsto_integral_exp_div_add hz 1 (Or.inl rfl)
  obtain ⟨e1, e2⟩ := auxG_add_I_mul_auxF hz
  have h := tendsto_integral_lin' (κ₁ := I / 2) (κ₂ := -(I / 2))
    (f := fun t : ℝ => Complex.sin t / (t + z))
    (fun R hR => intervalIntegrable_exp_div_add hz 1 hR)
    (fun R hR => intervalIntegrable_exp_div_add hz (-1) hR) hm hp (fun t _ => by
      rw [Complex.sin]
      ring_nf)
  convert h using 2
  rw [show (-1 : ℂ) * I * z = -I * z by ring, show (-1 : ℂ) * (π / 2 * I) = -(π / 2 * I) by
    ring, ← e1, show (1 : ℂ) * I * z = I * z by ring, one_mul, ← e2]
  ring_nf
  rw [I_sq]
  ring

/-- **DLMF 6.7.14** (first integral): `g(z) = ∫_0^∞ cos t/(t + z) dt`, `|ph z| < π` (improper). -/
theorem dlmf_6_7_14_first {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, Complex.cos t / (t + z)) atTop (𝓝 (auxG z)) := by
  have hp := tendsto_integral_exp_div_add hz (-1) (Or.inr rfl)
  have hm := tendsto_integral_exp_div_add hz 1 (Or.inl rfl)
  obtain ⟨e1, e2⟩ := auxG_add_I_mul_auxF hz
  have h := tendsto_integral_lin' (κ₁ := 1 / 2) (κ₂ := 1 / 2)
    (f := fun t : ℝ => Complex.cos t / (t + z))
    (fun R hR => intervalIntegrable_exp_div_add hz 1 hR)
    (fun R hR => intervalIntegrable_exp_div_add hz (-1) hR) hm hp (fun t _ => by
      rw [Complex.cos]
      ring_nf)
  convert h using 2
  rw [show (-1 : ℂ) * I * z = -I * z by ring, show (-1 : ℂ) * (π / 2 * I) = -(π / 2 * I) by
    ring, ← e1, show (1 : ℂ) * I * z = I * z by ring, one_mul, ← e2]
  ring

/-! ### 6.7.13, 6.7.14 (second integrals) -/

/-- The improper integral `∫_x^∞ e^{−αt} α/(αt + β) dt = e^β E1Gen(ℓ(x))`, for a smooth logarithm
`ℓ` of `αt + β` along `[x, ∞)` with `E1Gen(ℓ(R)) → 0`. -/
theorem tendsto_integral_of_E1Gen_lift (α β : ℂ) (x : ℝ) {ℓ : ℝ → ℂ}
    (hℓd : ∀ t, x ≤ t → HasDerivAt ℓ (α / (α * t + β)) t)
    (hexp : ∀ t, x ≤ t → cexp (ℓ t) = α * t + β)
    (hlim : Tendsto (fun R => E1Gen (ℓ R)) atTop (𝓝 0)) {f : ℝ → ℂ}
    (hf : ∀ t, x ≤ t → f t = cexp (-(α * t)) * α / (α * t + β)) :
    Tendsto (fun R => ∫ t in x..R, f t) atTop (𝓝 (cexp β * E1Gen (ℓ x))) := by
  have hne : ∀ t, x ≤ t → α * t + β ≠ 0 := fun t ht => by rw [← hexp t ht]; exact exp_ne_zero _
  have hftc : ∀ R, x ≤ R → ∫ t in x..R, f t = cexp β * (E1Gen (ℓ x) - E1Gen (ℓ R)) := by
    intro R hR
    have hd : ∀ t ∈ uIcc x R, HasDerivAt (fun t => -cexp β * E1Gen (ℓ t)) (f t) t := by
      intro t ht
      rw [uIcc_of_le hR] at ht
      have h1 := ((hasDerivAt_E1Gen (ℓ t)).comp t (hℓd t ht.1)).const_mul (-cexp β)
      refine h1.congr_deriv ?_
      rw [hf t ht.1, hexp t ht.1, neg_add, exp_add]
      have hee : cexp β * cexp (-β) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
      have := hne t ht.1
      field_simp
      linear_combination α * hee
    have hc : ContinuousOn f (uIcc x R) := by
      have h2 : ContinuousOn (fun t : ℝ => cexp (-(α * t)) * α / (α * t + β)) (uIcc x R) := by
        intro t ht
        rw [uIcc_of_le hR] at ht
        exact ((by fun_prop : Continuous fun t : ℝ => cexp (-(α * t)) * α).continuousAt.div
          (by fun_prop : Continuous fun t : ℝ => α * t + β).continuousAt
          (hne t ht.1)).continuousWithinAt
      refine h2.congr fun t ht => ?_
      rw [uIcc_of_le hR] at ht
      exact hf t ht.1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
    ring
  have h := (hlim.const_sub (E1Gen (ℓ x))).const_mul (cexp β)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  exact (hftc R hR).symm

/-- `∫_0^∞ e^{−zt}/(t ± i) dt = e^{±iz} E1Gen(ln z ± πi/2)` (improper), `ℜz ≥ 0`, `z ≠ 0`, with the
logarithm `ℓ(t) = ln z + ln(t ± i)` of `z(t ± i)`. -/
theorem tendsto_integral_laplace {z : ℂ} (hz0 : z ≠ 0) (hre : 0 ≤ z.re) (σ : ℂ)
    (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-(z * t)) / (t + σ * I)) atTop
      (𝓝 (cexp (σ * I * z) * E1Gen (log z + σ * (π / 2 * I)))) := by
  have hσim : (σ * I).im ≠ 0 := by rcases hσ with rfl | rfl <;> simp
  have hslit : ∀ t : ℝ, (t : ℂ) + σ * I ∈ slitPlane := fun t =>
    mem_slitPlane_iff.mpr (Or.inr (by simpa using hσim))
  set ℓ : ℝ → ℂ := fun t => log z + log ((t : ℂ) + σ * I) with hℓ
  have hℓd : ∀ t : ℝ, 0 ≤ t → HasDerivAt ℓ (z / (z * t + z * (σ * I))) t := by
    intro t _
    have h1 : HasDerivAt (fun v : ℂ => log z + log (v + σ * I)) (1 / ((t : ℂ) + σ * I)) t := by
      have := ((hasDerivAt_id (t : ℂ)).add_const (σ * I)).clog (hslit t)
      simpa using this.const_add (log z)
    have h2 := h1.comp_ofReal
    refine h2.congr_deriv ?_
    have := slitPlane_ne_zero (hslit t)
    field_simp
  have hexp : ∀ t : ℝ, 0 ≤ t → cexp (ℓ t) = z * t + z * (σ * I) := fun t _ => by
    simp only [hℓ]
    rw [exp_add, exp_log hz0, exp_log (slitPlane_ne_zero (hslit t))]
    ring
  have hℓ0 : ℓ 0 = log z + σ * (π / 2 * I) := by
    simp only [hℓ, ofReal_zero, zero_add]
    rcases hσ with rfl | rfl
    · rw [one_mul, log_I]
      ring
    · rw [neg_one_mul, log_neg_I]
      ring
  -- `E1Gen(ℓ(R)) = E₁(z(R ± i)) → 0`
  have hstrip : ∀ R : ℝ, 0 < R → ℓ R ∈ logStrip := by
    intro R hR
    have h1 := abs_le.mp (abs_arg_le_pi_div_two_iff.mpr hre)
    have h2 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl (show 0 < ((R : ℂ) + σ * I).re by
      rcases hσ with rfl | rfl <;> simpa using hR)))
    show -π < (ℓ R).im ∧ (ℓ R).im < π
    simp only [hℓ, add_im, log_im]
    constructor <;> linarith
  set w : ℝ → ℂ := fun R => z * R + z * (σ * I)
  set r₀ : ℝ := (z * (σ * I)).re
  have hwre : ∀ R : ℝ, 0 ≤ R → r₀ ≤ (w R).re := fun R hR => by
    simp only [w, r₀, add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    nlinarith
  have hmax : Tendsto (fun R => max |(w R).im| (w R).re) atTop atTop := by
    have hn : Tendsto (fun R : ℝ => ‖z‖ * R - 2 * |r₀|) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (norm_pos_iff.mpr hz0))
    refine tendsto_atTop_mono' _ ?_ (hn.atTop_div_const (show (0 : ℝ) < 2 by norm_num))
    filter_upwards [eventually_ge_atTop 0] with R hR
    have h1 : ‖z‖ * R ≤ ‖w R‖ := by
      have : ‖w R‖ = ‖z‖ * ‖(R : ℂ) + σ * I‖ := by simp only [w]; rw [← mul_add, norm_mul]
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have := re_le_norm ((R : ℂ) + σ * I)
      rcases hσ with rfl | rfl <;> simp at this ⊢ <;> linarith
    have h2 := norm_le_abs_re_add_abs_im (w R)
    have h3 : |(w R).re| ≤ (w R).re + 2 * |r₀| := by
      have := hwre R hR
      rcases le_or_gt 0 (w R).re with h | h
      · rw [abs_of_nonneg h]; linarith [abs_nonneg r₀]
      · rw [abs_of_neg h]; linarith [neg_abs_le r₀]
    have h4 := le_max_left |(w R).im| (w R).re
    have h5 := le_max_right |(w R).im| (w R).re
    linarith
  have hlim : Tendsto (fun R => E1Gen (ℓ R)) atTop (𝓝 0) := by
    have heq : ∀ᶠ R : ℝ in atTop, E1Gen (ℓ R) = expIntE₁ (w R) := by
      filter_upwards [eventually_gt_atTop 0] with R hR
      rw [(dlmf_6_4_1).2.1 _ (hstrip R hR), hexp R hR.le]
    refine (tendsto_expIntE₁_zero (w := w) (r₀ := r₀) ?_
      ((eventually_ge_atTop 0).mono fun R hR => hwre R hR) hmax).congr'
      (heq.mono fun R h => h.symm)
    filter_upwards [eventually_gt_atTop 0] with R hR
    show z * R + z * (σ * I) ∈ slitPlane
    rw [← hexp R hR.le]
    exact exp_mem_slitPlane (hstrip R hR)
  have h := tendsto_integral_of_E1Gen_lift z (z * (σ * I)) 0 hℓd hexp hlim
    (f := fun t => cexp (-(z * t)) / (t + σ * I)) (fun t _ => by
      have := slitPlane_ne_zero (hslit t)
      rw [show z * (t : ℂ) + z * (σ * I) = z * (t + σ * I) by ring]
      field_simp)
  rw [hℓ0, show z * (σ * I) = σ * I * z by ring] at h
  exact h

theorem mem_slitPlane_of_re_nonneg {z : ℂ} (hre : 0 ≤ z.re) (hz0 : z ≠ 0) : z ∈ slitPlane := by
  rcases hre.lt_or_eq with h | h
  · exact mem_slitPlane_of_re_pos h
  · refine mem_slitPlane_iff.mpr (Or.inr fun him => hz0 ?_)
    exact Complex.ext (by simp [← h]) (by simp [him])

theorem continuous_laplace_frac (z σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    Continuous fun t : ℝ => cexp (-(z * t)) / (t + σ * I) := by
  refine (by fun_prop : Continuous fun t : ℝ => cexp (-(z * t))).div
    (continuous_ofReal.add continuous_const) fun t h => ?_
  have := congrArg Complex.im h
  rcases hσ with rfl | rfl <;> simp at this

theorem sq_add_one_eq (t : ℝ) : (t : ℂ) ^ 2 + 1 = (t + -1 * I) * (t + 1 * I) := by
  linear_combination I_sq

theorem sq_add_one_ne (t : ℝ) : (t : ℂ) ^ 2 + 1 ≠ 0 := by
  rw [← ofReal_pow, ← ofReal_one, ← ofReal_add, ofReal_ne_zero]
  positivity

theorem pf_f {E A B c : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hc : c ≠ 0) (h : B - A = c) :
    E / (A * B) = 1 / c * (E / A) + -(1 / c) * (E / B) := by
  subst h
  field_simp
  ring

theorem pf_g {E A B t : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (h : A + B = 2 * t) :
    t * E / (A * B) = 1 / 2 * (E / A) + 1 / 2 * (E / B) := by
  have ht : t = (A + B) / 2 := by rw [h]; ring
  subst ht
  field_simp
  ring

theorem auxF_zero : auxF 0 = π / 2 := by
  have h : Si 0 = 0 := by simp [Si]
  simp [auxF, (dlmf_6_2_10 0).2, h]

/-- The improper Laplace integrals of `1/(t² + 1)` and `t/(t² + 1)` against `e^{−zt}`. -/
theorem tendsto_laplace_f_g {z : ℂ} (hre : 0 ≤ z.re) (hz0 : z ≠ 0) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-(z * t)) / ((t : ℂ) ^ 2 + 1)) atTop
        (𝓝 (auxF z)) ∧
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, t * cexp (-(z * t)) / ((t : ℂ) ^ 2 + 1)) atTop
        (𝓝 (auxG z)) := by
  have hz := mem_slitPlane_of_re_nonneg hre hz0
  obtain ⟨e1, e2⟩ := auxG_add_I_mul_auxF hz
  have hm := tendsto_integral_laplace hz0 hre (-1) (Or.inr rfl)
  have hp := tendsto_integral_laplace hz0 hre 1 (Or.inl rfl)
  rw [show (-1 : ℂ) * I * z = -I * z by ring, show (-1 : ℂ) * (π / 2 * I) = -(π / 2 * I) by ring,
    ← e1] at hm
  rw [show (1 : ℂ) * I * z = I * z by ring, show (1 : ℂ) * (π / 2 * I) = π / 2 * I by ring,
    ← e2] at hp
  have hc1 := continuous_laplace_frac z (-1) (Or.inr rfl)
  have hc2 := continuous_laplace_frac z 1 (Or.inl rfl)
  have hne1 : ∀ t : ℝ, (t : ℂ) + -1 * I ≠ 0 := fun t h => by
    have := congrArg Complex.im h; simp at this
  have hne2 : ∀ t : ℝ, (t : ℂ) + 1 * I ≠ 0 := fun t h => by
    have := congrArg Complex.im h; simp at this
  constructor
  · have h := tendsto_integral_lin (κ₁ := 1 / (2 * I)) (κ₂ := -(1 / (2 * I))) hc1 hc2 hm hp
      (f := fun t : ℝ => cexp (-(z * t)) / ((t : ℂ) ^ 2 + 1)) (fun t => by
        rw [sq_add_one_eq]
        exact pf_f (hne1 t) (hne2 t) (mul_ne_zero two_ne_zero I_ne_zero) (by ring))
    convert h using 2
    field_simp
    ring
  · have h := tendsto_integral_lin (κ₁ := 1 / 2) (κ₂ := 1 / 2) hc1 hc2 hm hp
      (f := fun t : ℝ => t * cexp (-(z * t)) / ((t : ℂ) ^ 2 + 1)) (fun t => by
        rw [sq_add_one_eq]
        exact pf_g (hne1 t) (hne2 t) (by ring))
    convert h using 2
    ring

/-- **DLMF 6.7.13** (second integral): `f(z) = ∫_0^∞ e^{−zt}/(t² + 1) dt`, `ℜz ≥ 0`. -/
theorem dlmf_6_7_13_second {z : ℂ} (hre : 0 ≤ z.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) / ((t : ℂ) ^ 2 + 1) = auxF z := by
  have hint : IntegrableOn (fun t : ℝ => cexp (-(z * t)) / ((t : ℂ) ^ 2 + 1)) (Ioi 0) := by
    refine integrable_inv_one_add_sq.integrableOn.mono' ?_
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t (ht : 0 < t) => ?_))
    · exact ((by fun_prop : Continuous fun t : ℝ => cexp (-(z * t))).div
        (by fun_prop) sq_add_one_ne).aestronglyMeasurable
    · rw [norm_div, norm_exp, ← ofReal_pow, ← ofReal_one, ← ofReal_add, norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity), div_eq_mul_inv, add_comm]
      have : Real.exp (-(z * t)).re ≤ 1 := by
        rw [Real.exp_le_one_iff]
        simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        nlinarith
      exact mul_le_of_le_one_left (by positivity) this
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [auxF_zero]
    simp only [zero_mul, neg_zero, exp_zero]
    have h := integral_Ioi_inv_one_add_sq (i := 0)
    rw [Real.arctan_zero, sub_zero] at h
    have h2 : ∫ t in Ioi (0 : ℝ), (1 : ℂ) / ((t : ℂ) ^ 2 + 1) =
        ((∫ t in Ioi (0 : ℝ), (1 + t ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      push_cast
      ring
    rw [h2, h]
    push_cast
    ring
  · exact integral_Ioi_eq_of_tendsto hint (tendsto_laplace_f_g hre hz0).1

/-- **DLMF 6.7.14** (second integral): `g(z) = ∫_0^∞ t e^{−zt}/(t² + 1) dt`, `ℜz ≥ 0`, `z ≠ 0`
(an improper integral; a Lebesgue integral when `ℜz > 0`). -/
theorem dlmf_6_7_14_second {z : ℂ} (hre : 0 ≤ z.re) (hz0 : z ≠ 0) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, t * cexp (-(z * t)) / ((t : ℂ) ^ 2 + 1)) atTop
        (𝓝 (auxG z)) ∧
      (0 < z.re → ∫ t in Ioi (0 : ℝ), t * cexp (-(z * t)) / ((t : ℂ) ^ 2 + 1) = auxG z) := by
  refine ⟨(tendsto_laplace_f_g hre hz0).2, fun hpos => ?_⟩
  refine integral_Ioi_eq_of_tendsto ?_ (tendsto_laplace_f_g hre hz0).2
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-z.re * t)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hpos
  refine hexp.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  · exact ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) * cexp (-(z * t))).div
      (by fun_prop) sq_add_one_ne).aestronglyMeasurable
  · have ht' : (0 : ℝ) < t := ht
    rw [norm_div, norm_mul, norm_exp, ← ofReal_pow, ← ofReal_one, ← ofReal_add, norm_real,
      norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht', abs_of_pos (by positivity)]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [div_le_iff₀ (by positivity), show -z.re * t = -(z.re * t) by ring]
    nlinarith [Real.exp_pos (-(z.re * t)), sq_nonneg (t - 1)]

end Azurite.DLMF
