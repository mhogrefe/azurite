/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Cut

/-!
# DLMF §4.13: the logarithmic branch point `z = 0` of `W_k`, `k ≠ 0`

* `one_le_norm_lambertW`: `|W_k(z)| ≥ 1` for `k ≠ 0` (a solution with `|w| < 1` has
  `ℑw + ph w ∈ (−π, π]`, which forces `k = 0`).
* `tendsto_norm_lambertW_zero`: `|W_k(z)| → ∞` as `z → 0` (`k ≠ 0`), while `W₀(0) = 0`.
* `tendsto_lambertW_below_neg`, `continuousWithinAt_lambertW_above_neg`: crossing the negative
  axis downwards moves `W_k` to `W_{k−1}`: `W_k(x − 0i) = W_{k−1}(x)` for `x < 0` (`x < −e⁻¹` when
  `k ∈ {0, 1}`), and `W_k` is continuous from above (`x < −e⁻¹` when `k ∈ {0, −1}`). Going once
  around `0` thus permutes the branches, the logarithmic branch point.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

theorem one_le_norm_lambertW {k : ℤ} (hk : k ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    1 ≤ ‖lambertW k z‖ := by
  rw [lambertW_of_ne hz]
  by_cases hL : omegaLm (log z + 2 * π * k * I)
  · rw [wrightOmega_of_Lm hL, norm_real, Real.norm_eq_abs]
    have h1 : Real.exp (log z + 2 * π * k * I).re ≤ Real.exp (-1) := Real.exp_le_exp.mpr hL.2
    have := (lambertWm1_spec (y := -Real.exp (log z + 2 * π * k * I).re) (by linarith)
      (by linarith [Real.exp_pos (log z + 2 * π * k * I).re])).1
    rw [abs_of_neg (by linarith)]; linarith
  by_contra hlt
  push Not at hlt
  set w := wrightOmega (log z + 2 * π * k * I)
  have h := congrArg im (dlmf_4_13_1_2 hL)
  rw [add_log_im] at h
  have hre : ((2 * π * k : ℂ)).re = 2 * π * k := by
    rw [show (2 * π * k : ℂ) = ((2 * π * k : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  simp only [add_im, log_im, mul_im, I_re, I_im, mul_zero, mul_one, hre] at h
  -- `θ = ℑw + ph w ∈ (−π, π]`
  have hθ : -π < w.im + arg w ∧ w.im + arg w ≤ π := by
    rcases lt_trichotomy w.im 0 with hη | hη | hη
    · exact ⟨neg_pi_lt_im_add_arg_of_norm_lt_one hlt hη,
        by linarith [arg_le_pi w]⟩
    · rw [hη, zero_add]; exact ⟨neg_pi_lt_arg w, arg_le_pi w⟩
    · exact ⟨by linarith [neg_pi_lt_arg w], (im_add_arg_lt_pi_of_norm_lt_one hlt hη).le⟩
  have ha1 := neg_pi_lt_arg z
  have ha2 := arg_le_pi z
  have : k = 0 := by
    refine int_eq_of_mul_pi_bounds (m := 0) ?_ ?_ <;> push_cast <;> nlinarith [Real.pi_pos]
  exact hk this

/-- **DLMF §4.13**: `W_k`, `k ≠ 0`, has a logarithmic singularity at `0`: `|W_k(z)| → ∞`. -/
theorem tendsto_norm_lambertW_zero {k : ℤ} (hk : k ≠ 0) :
    Tendsto (fun z => ‖lambertW k z‖) (𝓝[≠] 0) atTop := by
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuous_norm.tendsto' 0 0 (by simp)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun z hz => norm_ne_zero_iff.mpr hz⟩
  have hl := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp hn)
  refine tendsto_atTop_mono' _ ?_ hl
  filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
  have h1 := one_le_norm_lambertW hk hz
  have h2 : ‖z‖ = ‖lambertW k z‖ * Real.exp (lambertW k z).re := by
    conv_lhs => rw [← dlmf_4_13_1 k z]
    rw [norm_mul, norm_exp]
  -- `ln|z| = ln|W| + ℜW ≥ ℜW ≥ −|W|`
  have h3 : Real.log ‖z‖ = Real.log ‖lambertW k z‖ + (lambertW k z).re := by
    rw [h2, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have h4 := Real.log_nonneg h1
  have h5 : -‖lambertW k z‖ ≤ (lambertW k z).re := by
    have := neg_abs_le (lambertW k z).re
    linarith [abs_re_le_norm (lambertW k z)]
  have h6 : Real.log ‖lambertW k z‖ ≤ ‖lambertW k z‖ - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  simp only [Function.comp_apply]
  linarith

/-! ### Crossing the negative axis -/

/-- `ln x + 2πij` (`x < 0`) is on `L±` only for `j ∈ {0, −1}` and `x ≥ −e⁻¹`. -/
theorem not_omegaL_of_neg {x : ℝ} (hx : x < 0) (j : ℤ)
    (h : j ≠ 0 ∧ j ≠ -1 ∨ x < -Real.exp (-1)) :
    ¬omegaLm (log (x : ℂ) + 2 * π * j * I) ∧ ¬omegaLp (log (x : ℂ) + 2 * π * j * I) := by
  have him : (log (x : ℂ) + 2 * π * j * I).im = π + 2 * π * j := by
    simp [log_im, arg_ofReal_of_neg hx]
  have hre : (log (x : ℂ) + 2 * π * j * I).re = Real.log (-x) := by
    simp [log_re, abs_of_neg hx]
  rcases h with ⟨h0, h1⟩ | h
  · refine ⟨fun hL => h1 ?_, fun hL => h0 ?_⟩
    · have := hL.1; rw [him] at this
      have : (j : ℝ) = -1 := by nlinarith [Real.pi_pos]
      exact_mod_cast this
    · have := hL.1; rw [him] at this
      have : (j : ℝ) = 0 := by nlinarith [Real.pi_pos]
      exact_mod_cast this
  · have hl : -1 < Real.log (-x) := by
      rw [← Real.log_exp (-1)]; exact Real.log_lt_log (Real.exp_pos _) (by linarith)
    exact ⟨fun hL => by linarith [hL.2], fun hL => by linarith [hL.2]⟩

theorem log_ofReal_neg' {x : ℝ} (hx : x < 0) : log (x : ℂ) = Real.log ‖(x : ℂ)‖ + π * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_ofReal_of_neg hx]

/-- **DLMF §4.13** (monodromy at `0`): `W_k(x − 0i) = W_{k−1}(x)` for `x < 0`, unless
`k ∈ {0, 1}` and `−e⁻¹ ≤ x` (the real branches meeting at `−e⁻¹`). -/
theorem tendsto_lambertW_below_neg {x : ℝ} (hx : x < 0) (k : ℤ)
    (h : k ≠ 0 ∧ k ≠ 1 ∨ x < -Real.exp (-1)) :
    Tendsto (lambertW k) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (lambertW (k - 1) x)) := by
  have hne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne
  have h' : k - 1 ≠ 0 ∧ k - 1 ≠ -1 ∨ x < -Real.exp (-1) := by
    rcases h with ⟨a, b⟩ | h
    · left; constructor <;> omega
    · right; exact h
  obtain ⟨hL1, hL2⟩ := not_omegaL_of_neg hx (k - 1) h'
  have hlog := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero (z := (x : ℂ))
    (by simpa using hx) (by simp)
  have hpt : (Real.log ‖(x : ℂ)‖ - π * I) + 2 * π * k * I =
      log (x : ℂ) + 2 * π * ((k - 1 : ℤ) : ℂ) * I := by
    rw [log_ofReal_neg' hx]; push_cast; ring
  have h2 := hlog.add (tendsto_const_nhds (x := 2 * π * (k : ℂ) * I))
  rw [hpt] at h2
  have hω := ((hasDerivAt_wrightOmega hL1 hL2).continuousAt).tendsto.comp h2
  rw [lambertW_of_ne hne]
  exact hω.congr' (nhdsWithin_le_nhds
    ((eventually_ne_nhds hne).mono fun _ hz => (lambertW_of_ne hz).symm))

/-- `W_k` is continuous from above at `x < 0`, unless `k ∈ {0, −1}` and `−e⁻¹ ≤ x`. -/
theorem continuousWithinAt_lambertW_above_neg {x : ℝ} (hx : x < 0) (k : ℤ)
    (h : k ≠ 0 ∧ k ≠ -1 ∨ x < -Real.exp (-1)) :
    ContinuousWithinAt (lambertW k) {z : ℂ | 0 ≤ z.im} (x : ℂ) := by
  have hne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne
  obtain ⟨hL1, hL2⟩ := not_omegaL_of_neg hx k h
  have hlog := continuousWithinAt_log_of_re_neg_of_im_zero (z := (x : ℂ)) (by simpa using hx)
    (by simp)
  have h2 : ContinuousWithinAt (fun z => log z + 2 * π * k * I) {z : ℂ | 0 ≤ z.im} (x : ℂ) :=
    hlog.add continuousWithinAt_const
  have hω := ContinuousAt.comp_continuousWithinAt (f := fun z => log z + 2 * π * k * I)
    (hasDerivAt_wrightOmega hL1 hL2).continuousAt h2
  rw [ContinuousWithinAt, lambertW_of_ne hne]
  exact hω.tendsto.congr' (nhdsWithin_le_nhds
    ((eventually_ne_nhds hne).mono fun _ hz => (lambertW_of_ne hz).symm))

end Azurite.DLMF
