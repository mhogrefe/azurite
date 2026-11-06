/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Branch
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# DLMF §4.13: the Lambert `W`-function near the negative real axis

* `lambertW_zero_eq_of_norm_lt_one`: a solution `w` of `w e^w = z` with `|w| < 1` is `W₀(z)`
  (`|w| < 1` forces `ℑw + ph w ∈ (−π, π]`).
* `hasDerivAt_lambertW_zero_of_norm_lt_one` and `dlmf_4_13_W0_analytic`: `W₀` is analytic on
  `ℂ ∖ (−∞, −e⁻¹]` (in particular across `(−e⁻¹, 0]`), real-valued for `z > −e⁻¹`.
* `dlmf_4_13_Wk_analytic`: the other branches are analytic on `ℂ ∖ (−∞, 0]`.
* `W_{±1}(x ∓ 0i)`: `tendsto_lambertW_one_below` (`W₁(x − 0i) = Wm(x)`) and
  `continuousWithinAt_lambertW_neg_one` (`W_{−1}(x + 0i) = Wm(x)`) for `−e⁻¹ < x < 0`.
-/

open Set Filter Topology Complex
open scoped Real ComplexConjugate

namespace Azurite.DLMF

/-- An integer squeezed by `(m − 1)π < kπ < (m + 1)π` equals `m`. -/
theorem int_eq_of_mul_pi_bounds {k m : ℤ} (h1 : ((m : ℝ) - 1) * π < k * π)
    (h2 : (k : ℝ) * π < (m + 1) * π) : k = m := by
  have a := lt_of_mul_lt_mul_right h1 Real.pi_pos.le
  have b := lt_of_mul_lt_mul_right h2 Real.pi_pos.le
  have a' : m - 1 < k := by exact_mod_cast a
  have b' : k < m + 1 := by exact_mod_cast b
  omega

theorem im_eq_of_add_log {w ζ : ℂ} {k : ℤ} (hk : w + log w = log ζ + k * (2 * π * I)) :
    w.im + arg w = arg ζ + 2 * π * k := by
  have := congrArg im hk
  rw [add_log_im] at this
  simp [log_im] at this
  linarith

/-! ### Solutions with `|w| < 1` -/

theorem im_add_arg_lt_pi_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) (hη : 0 < w.im) :
    w.im + arg w < π := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr fun h => by rw [h] at hη; simp at hη
  have hηle : w.im ≤ ‖w‖ := (le_abs_self _).trans (abs_im_le_norm w)
  rcases le_or_gt 0 w.re with hξ | hξ
  · have : arg w ≤ π / 2 := arg_le_pi_div_two_iff.mpr (Or.inl hξ)
    linarith [Real.pi_gt_three]
  · rw [arg_of_re_neg_of_im_nonneg hξ hη.le, neg_im, neg_div, Real.arcsin_neg]
    set t := w.im / ‖w‖
    have ht0 : 0 < t := div_pos hη hn
    have ht1 : t ≤ 1 := (div_le_one hn).mpr hηle
    have hηt : w.im < t := by
      rw [lt_div_iff₀ hn]; nlinarith
    have harc : t ≤ Real.arcsin t := by
      have h := Real.sin_le (Real.arcsin_nonneg.mpr ht0.le)
      rwa [Real.sin_arcsin (by linarith) ht1] at h
    linarith

theorem neg_pi_lt_im_add_arg_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) (hη : w.im < 0) :
    -π < w.im + arg w := by
  have h := im_add_arg_lt_pi_of_norm_lt_one (w := conj w) (by simpa using hw)
    (by simpa using hη)
  have hne : arg w ≠ π := fun h' => by have := arg_eq_pi_iff.mp h'; linarith [this.2]
  rw [arg_conj] at h
  simp only [hne, ↓reduceIte] at h
  simp at h
  linarith

/-- **DLMF §4.13**: a solution of `w e^w = z` with `|w| < 1` is the principal value `W₀(z)`. -/
theorem lambertW_zero_eq_of_norm_lt_one {z w : ℂ} (hw : w * exp w = z) (h1 : ‖w‖ < 1) :
    lambertW 0 z = w := by
  by_cases hz : z = 0
  · have : w = 0 := by
      rw [hz] at hw; rcases mul_eq_zero.mp hw with h | h
      · exact h
      · exact absurd h (exp_ne_zero w)
    rw [hz, this, lambertW_zero_arg]
  have hw0 : w ≠ 0 := fun h => hz (by rw [← hw, h]; simp)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, w + log w = log z + k * (2 * π * I) := by
    apply exp_eq_exp_iff_exists_int.mp
    rw [exp_add, exp_log hw0, exp_log hz, ← hw, mul_comm]
  have him := im_eq_of_add_log hk
  -- `ℑw + ph w ∈ (−π, π]`
  have hb : -π < w.im + arg w ∧ w.im + arg w ≤ π := by
    rcases lt_trichotomy w.im 0 with h | h | h
    · exact ⟨neg_pi_lt_im_add_arg_of_norm_lt_one h1 h, by linarith [arg_le_pi w]⟩
    · rw [h, zero_add]; exact ⟨neg_pi_lt_arg w, arg_le_pi w⟩
    · exact ⟨by linarith [(arg_mem_Ioo_of_im_pos h).1, Real.pi_pos],
        (im_add_arg_lt_pi_of_norm_lt_one h1 h).le⟩
  have hk0 : k = 0 := by
    have ha1 := neg_pi_lt_arg z
    have ha2 := arg_le_pi z
    refine int_eq_of_mul_pi_bounds ?_ ?_ <;> push_cast <;> linarith [hb.1, hb.2, him]
  rw [lambertW_of_ne hz]
  have hζ : log z + 2 * π * ((0 : ℤ) : ℂ) * I = log z := by simp
  rw [hζ]
  refine wrightOmega_eq (fun h => ?_) ⟨hw0, by rw [hk, hk0]; simp, fun _ _ => ?_⟩
  · have := h.1; rw [log_im] at this; linarith [neg_pi_lt_arg z]
  · have := (abs_re_le_norm w).trans h1.le
    linarith [neg_abs_le w.re]

/-! ### Analyticity of `W₀` -/

theorem hasStrictDerivAt_mul_exp (w : ℂ) :
    HasStrictDerivAt (fun w => w * exp w) ((1 + w) * exp w) w := by
  have h : HasStrictDerivAt (fun w => w * exp w) (1 * exp w + w * exp w) w :=
    (hasStrictDerivAt_id w).mul (hasStrictDerivAt_exp w)
  convert h using 1; ring

/-- `W₀` is analytic wherever `|W₀| < 1`, with `W₀′ = e^{−W}/(1 + W)`. -/
theorem hasDerivAt_lambertW_zero_of_norm_lt_one {z : ℂ} (h1 : ‖lambertW 0 z‖ < 1) :
    HasDerivAt (lambertW 0) (exp (-lambertW 0 z) / (1 + lambertW 0 z)) z := by
  set w₀ := lambertW 0 z with hw₀
  have hm1 : 1 + w₀ ≠ 0 := fun e => by
    have : w₀ = -1 := by linear_combination e
    rw [this] at h1; simp at h1
  have hf := hasStrictDerivAt_mul_exp w₀
  have hf' : (1 + w₀) * exp w₀ ≠ 0 := mul_ne_zero hm1 (exp_ne_zero _)
  have hfz : w₀ * exp w₀ = z := dlmf_4_13_1 0 z
  set g := hf.localInverse _ _ _ hf'
  have hg := hf.to_localInverse hf'
  have hright := hf.eventually_right_inverse hf'
  simp only [hfz] at hg hright
  have hg0 : g z = w₀ := by
    have := (hf.eventually_left_inverse hf').self_of_nhds
    simp only [hfz] at this; exact this
  have hcont : Tendsto g (𝓝 z) (𝓝 w₀) := by
    have h2 : Tendsto g (𝓝 z) (𝓝 (g z)) := hg.hasDerivAt.continuousAt.tendsto
    rwa [hg0] at h2
  have hev : lambertW 0 =ᶠ[𝓝 z] g := by
    filter_upwards [hright, hcont.eventually (isOpen_lt continuous_norm continuous_const |>.mem_nhds
      (show w₀ ∈ {w : ℂ | ‖w‖ < 1} from h1))] with ζ hζ1 hζ2
    exact lambertW_zero_eq_of_norm_lt_one hζ1 hζ2
  refine (hg.hasDerivAt.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [exp_neg]; field_simp

/-- The set `ℂ ∖ (−∞, −e⁻¹]`. -/
def cutW0 : Set ℂ := {z | ¬(z.im = 0 ∧ z.re ≤ -Real.exp (-1))}

theorem isOpen_cutW0 : IsOpen cutW0 := by
  have : IsClosed {z : ℂ | z.im = 0 ∧ z.re ≤ -Real.exp (-1)} :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_re continuous_const)
  exact this.isOpen_compl

/-- **DLMF §4.13**: `W₀(z)` is a single-valued analytic function on `ℂ ∖ (−∞, −e⁻¹]`, with
`dW/dz = e^{−W}/(1 + W)`. -/
theorem dlmf_4_13_W0_analytic {z : ℂ} (hz : z ∈ cutW0) :
    HasDerivAt (lambertW 0) (exp (-lambertW 0 z) / (1 + lambertW 0 z)) z := by
  by_cases hs : z ∈ slitPlane
  · exact (dlmf_4_13_4 0 hs).1
  · rw [mem_slitPlane_iff] at hs
    push Not at hs
    have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [hs.2])
    have hre : -Real.exp (-1) < z.re := by
      by_contra h; push Not at h; exact hz ⟨hs.2, h⟩
    apply hasDerivAt_lambertW_zero_of_norm_lt_one
    rw [hz', lambertW_zero_ofReal hre.le, norm_real, Real.norm_eq_abs, abs_lt]
    have h1 := lambertW0_gt hre
    have h2 : lambertW0 z.re ≤ 0 := by
      by_contra h; push Not at h
      have := (lambertW0_spec hre.le).2
      have : 0 < lambertW0 z.re * Real.exp (lambertW0 z.re) := mul_pos h (Real.exp_pos _)
      linarith
    constructor <;> linarith

theorem analyticOnNhd_lambertW_zero : AnalyticOnNhd ℂ (lambertW 0) cutW0 :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (dlmf_4_13_W0_analytic hz).differentiableAt.differentiableWithinAt) isOpen_cutW0

/-- **DLMF §4.13**: every branch `W_k` is analytic on `ℂ ∖ (−∞, 0]`. -/
theorem dlmf_4_13_Wk_analytic (k : ℤ) : AnalyticOnNhd ℂ (lambertW k) slitPlane :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (dlmf_4_13_4 k hz).1.differentiableAt.differentiableWithinAt) isOpen_slitPlane

/-! ### `W_{±1}(x ∓ 0i)` on `(−e⁻¹, 0)` -/

/-- Left of `ℜw = −1` (and `|ℑw| < π/2`), `ℑ(w e^w)` has the opposite sign of `ℑw`. -/
theorem im_mul_exp_neg {w : ℂ} (hre : w.re < -1) (hη : 0 < w.im) (hη2 : w.im < π / 2) :
    (w * exp w).im < 0 := by
  have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo ⟨by linarith, hη2⟩
  have ht : w.im < Real.tan w.im := Real.lt_tan hη hη2
  rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hc] at ht
  have him : (w * exp w).im = Real.exp w.re * (w.re * Real.sin w.im + w.im * Real.cos w.im) := by
    simp only [mul_im, exp_re, exp_im]; ring
  rw [him]
  apply mul_neg_of_pos_of_neg (Real.exp_pos _)
  have hs : 0 < Real.sin w.im := lt_trans (mul_pos hη hc) ht
  nlinarith [mul_lt_mul_of_pos_right hre hs]

theorem im_mul_exp_pos {w : ℂ} (hre : w.re < -1) (hη : w.im < 0) (hη2 : -(π / 2) < w.im) :
    0 < (w * exp w).im := by
  have := im_mul_exp_neg (w := conj w) (by simpa using hre) (by simpa using hη)
    (by simp; linarith)
  rw [show conj w * exp (conj w) = conj (w * exp w) by rw [map_mul, exp_conj], conj_im] at this
  linarith

/-- The local inverse of `w e^w` at `Wm(x)`, `−e⁻¹ < x < 0`. -/
theorem exists_local_inverse_Wm1 {x : ℝ} (hx : -Real.exp (-1) < x) (hx0 : x < 0) :
    ∃ g : ℂ → ℂ, Tendsto g (𝓝 (x : ℂ)) (𝓝 (lambertWm1 x : ℂ)) ∧
      ∀ᶠ ζ in 𝓝 (x : ℂ), g ζ * exp (g ζ) = ζ ∧ (g ζ).re < -1 ∧ |(g ζ).im| < 1 := by
  set w₁ : ℂ := (lambertWm1 x : ℂ)
  have hw1 := lambertWm1_lt hx hx0
  have hm1 : 1 + w₁ ≠ 0 := fun e => by
    have := congrArg re e; simp [w₁] at this; linarith
  have hf := hasStrictDerivAt_mul_exp w₁
  have hf' : (1 + w₁) * exp w₁ ≠ 0 := mul_ne_zero hm1 (exp_ne_zero _)
  have hfx : w₁ * exp w₁ = x := by
    simp only [w₁]; rw [← ofReal_exp, ← ofReal_mul, (lambertWm1_spec hx.le hx0).2]
  have hg := hf.to_localInverse hf'
  have hright := hf.eventually_right_inverse hf'
  simp only [hfx] at hg hright
  have hg0 : hf.localInverse _ _ _ hf' x = w₁ := by
    have := (hf.eventually_left_inverse hf').self_of_nhds
    simp only [hfx] at this; exact this
  have hcont : Tendsto (hf.localInverse _ _ _ hf') (𝓝 (x : ℂ)) (𝓝 w₁) := by
    have h2 := hg.hasDerivAt.continuousAt.tendsto; rwa [hg0] at h2
  set δ := min (-1 - lambertWm1 x) 1
  have hδ : 0 < δ := lt_min (by linarith) one_pos
  refine ⟨_, hcont, ?_⟩
  filter_upwards [hright, hcont.eventually (Metric.ball_mem_nhds w₁ hδ)] with ζ h1 h2
  have hd : ‖hf.localInverse _ _ _ hf' ζ - w₁‖ < δ := by
    rw [← dist_eq_norm]; exact h2
  refine ⟨h1, ?_, ?_⟩
  · have h3 := (abs_re_le_norm _).trans_lt hd
    simp only [sub_re, w₁, ofReal_re] at h3
    have := (abs_lt.mp (h3.trans_le (min_le_left _ _))).2
    linarith
  · have h3 := (abs_im_le_norm _).trans_lt hd
    simp only [sub_im, w₁, ofReal_im, sub_zero] at h3
    exact h3.trans_le (min_le_right _ _)

/-- **DLMF §4.13**: `W₁(x − 0i) = Wm(x)` (the decreasing real solution) for `−e⁻¹ < x < 0`. -/
theorem tendsto_lambertW_one_below {x : ℝ} (hx : -Real.exp (-1) < x) (hx0 : x < 0) :
    Tendsto (lambertW 1) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (lambertWm1 x : ℂ)) := by
  obtain ⟨g, hg, hev⟩ := exists_local_inverse_Wm1 hx hx0
  refine (hg.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with ζ ⟨h1, h2, h3⟩ hζ
  have hζim : ζ.im < 0 := hζ
  set w := g ζ
  have hπ2 : (1 : ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  have hwim : 0 < w.im := by
    rcases lt_trichotomy w.im 0 with h | h | h
    · have := im_mul_exp_pos h2 h (by linarith [(abs_lt.mp h3).1])
      rw [h1] at this; linarith
    · exfalso
      have hw' : w = (w.re : ℂ) := Complex.ext rfl (by simp [h])
      have : (w * exp w).im = 0 := by rw [hw', ← ofReal_exp, ← ofReal_mul, ofReal_im]
      rw [h1] at this; linarith
    · exact h
  have hz0 : ζ ≠ 0 := fun h => by rw [h] at hζim; simp at hζim
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
  obtain ⟨k, hk⟩ : ∃ k : ℤ, w + log w = log ζ + k * (2 * π * I) := by
    apply exp_eq_exp_iff_exists_int.mp
    rw [exp_add, exp_log hw0, exp_log hz0, ← h1, mul_comm]
  have him := im_eq_of_add_log hk
  have harg := arg_mem_Ioo_of_im_pos hwim
  have hargζ := arg_mem_Ioo_of_im_neg hζim
  have hk1 : k = 1 := by
    refine int_eq_of_mul_pi_bounds ?_ ?_ <;> push_cast <;>
      linarith [Real.pi_gt_three, (abs_lt.mp h3).2, harg.1, harg.2, hargζ.1, hargζ.2, him]
  rw [lambertW_of_ne hz0, show log ζ + 2 * π * ((1 : ℤ) : ℂ) * I =
    log ζ + ((1 : ℤ) : ℂ) * (2 * π * I) by ring]
  refine (wrightOmega_eq (fun h => ?_) ⟨hw0, by rw [hk, hk1], fun h _ => ?_⟩).symm
  · have := h.1; simp [log_im] at this; linarith [hargζ.1]
  · simp [log_im] at h; linarith [hargζ.2]

/-- **DLMF §4.13**: `W_{−1}(x + 0i) = Wm(x)`: `W_{−1}` is continuous from above on `(−e⁻¹, 0)`. -/
theorem continuousWithinAt_lambertW_neg_one {x : ℝ} (hx : -Real.exp (-1) < x) (hx0 : x < 0) :
    ContinuousWithinAt (lambertW (-1)) {z : ℂ | 0 ≤ z.im} (x : ℂ) := by
  obtain ⟨g, hg, hev⟩ := exists_local_inverse_Wm1 hx hx0
  rw [ContinuousWithinAt, lambertW_neg_one_ofReal hx.le hx0]
  refine (hg.mono_left nhdsWithin_le_nhds).congr' ?_
  have hnx : ∀ᶠ ζ in 𝓝 (x : ℂ), ζ.re < 0 ∧ -Real.exp (-1) < ζ.re := by
    have h := continuous_re.tendsto (x : ℂ)
    simp only [ofReal_re] at h
    exact (h.eventually (Iio_mem_nhds hx0)).and (h.eventually (Ioi_mem_nhds hx))
  filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds hnx, self_mem_nhdsWithin]
    with ζ ⟨h1, h2, h3⟩ ⟨hr0, hr1⟩ hζ
  have hζim : 0 ≤ ζ.im := hζ
  set w := g ζ
  have hπ2 : (1 : ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  rcases hζim.lt_or_eq with hpos | hzero
  · -- upper half-plane: `w` lies in the lower half-plane and is `W_{−1}(ζ)`
    have hwim : w.im < 0 := by
      rcases lt_trichotomy w.im 0 with h | h | h
      · exact h
      · exfalso
        have hw' : w = (w.re : ℂ) := Complex.ext rfl (by simp [h])
        have : (w * exp w).im = 0 := by rw [hw', ← ofReal_exp, ← ofReal_mul, ofReal_im]
        rw [h1] at this; linarith
      · have := im_mul_exp_neg h2 h (by linarith [(abs_lt.mp h3).2])
        rw [h1] at this; linarith
    have hz0 : ζ ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hw0 : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
    obtain ⟨k, hk⟩ : ∃ k : ℤ, w + log w = log ζ + k * (2 * π * I) := by
      apply exp_eq_exp_iff_exists_int.mp
      rw [exp_add, exp_log hw0, exp_log hz0, ← h1, mul_comm]
    have him := im_eq_of_add_log hk
    have harg := arg_mem_Ioo_of_im_neg hwim
    have hargζ := arg_mem_Ioo_of_im_pos hpos
    have hk1 : k = -1 := by
      refine int_eq_of_mul_pi_bounds ?_ ?_ <;> push_cast <;>
        linarith [Real.pi_gt_three, (abs_lt.mp h3).1, harg.1, harg.2, hargζ.1, hargζ.2, him]
    rw [lambertW_of_ne hz0, show log ζ + 2 * π * ((-1 : ℤ) : ℂ) * I =
      log ζ + ((-1 : ℤ) : ℂ) * (2 * π * I) by ring]
    refine (wrightOmega_eq (fun h => ?_) ⟨hw0, by rw [hk, hk1], fun h _ => ?_⟩).symm
    · have := h.1; simp [log_im] at this; linarith [hargζ.2]
    · simp [log_im] at h; linarith [hargζ.2]
  · -- on the real axis: both are the real root `< −1`
    have hζ' : ζ = (ζ.re : ℂ) := Complex.ext rfl (by simp [← hzero])
    have hwim : w.im = 0 := by
      rcases lt_trichotomy w.im 0 with h | h | h
      · have := im_mul_exp_pos h2 h (by linarith [(abs_lt.mp h3).1])
        rw [h1] at this; linarith
      · exact h
      · have := im_mul_exp_neg h2 h (by linarith [(abs_lt.mp h3).2])
        rw [h1] at this; linarith
    have hw' : w = (w.re : ℂ) := Complex.ext rfl (by simp [hwim])
    rw [hζ', lambertW_neg_one_ofReal hr1.le hr0]
    have hreal : w.re * Real.exp w.re = ζ.re := by
      have := congrArg re h1; rw [hw', ← ofReal_exp, ← ofReal_mul, ofReal_re] at this
      exact this
    rw [hw', ← hreal, dlmf_4_13_3_2 h2]

end Azurite.DLMF
