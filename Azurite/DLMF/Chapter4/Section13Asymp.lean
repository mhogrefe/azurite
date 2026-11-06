/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Branch

/-!
# DLMF §4.13: the behaviour of `W_k(z)` as `|z| → ∞`

* `dlmf_4_13_1_1`: `W_k(z) = ln_k z − ln(ln_k z) + o(1)` as `|z| → ∞`, `ln_k z = ln z + 2πik`.

Proof: `w = W_k(z)` satisfies `w + ln w = ln_k z` (`lambertW_add_log`), `|w| → ∞` since
`|z| ≤ |w| e^{|w|}`, so `ln w / w → 0`, `u = w / ln_k z → 1`, and `ln w = ln(ln_k z) + ln u` once
`ph u` is small (`ℜ ln_k z > 0`).
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-- `ln_k z = ln z + 2πik`. -/
noncomputable def lnk (k : ℤ) (z : ℂ) : ℂ := log z + 2 * π * k * I

theorem lnk_re (k : ℤ) (z : ℂ) : (lnk k z).re = Real.log ‖z‖ := by simp [lnk, log_re]

theorem lambertW_add_log (k : ℤ) {z : ℂ} (hz : 1 < ‖z‖) :
    lambertW k z + log (lambertW k z) = lnk k z := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
  have hL : ¬omegaLm (lnk k z) := by
    rintro ⟨-, h⟩
    rw [lnk_re] at h
    linarith [Real.log_pos hz]
  rw [lambertW_of_ne hz0]
  exact dlmf_4_13_1_2 hL

theorem norm_clog_le_abs_log_add_pi (w : ℂ) : ‖log w‖ ≤ |Real.log ‖w‖| + π := by
  have h := norm_le_abs_re_add_abs_im (log w)
  rw [log_re, log_im] at h
  linarith [abs_arg_le_pi w]

/-- `|W_k(z)| → ∞` as `|z| → ∞`. -/
theorem tendsto_norm_lambertW (k : ℤ) :
    Tendsto (fun z => ‖lambertW k z‖) (Bornology.cobounded ℂ) atTop := by
  refine tendsto_atTop.2 fun R => ?_
  set R' := max R 1
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop (R' * Real.exp R')] with z hz
  by_contra h
  push Not at h
  have hR : ‖lambertW k z‖ < R' := h.trans_le (le_max_left _ _)
  have h1 := dlmf_4_13_1 k z
  have h2 : ‖z‖ = ‖lambertW k z‖ * Real.exp (lambertW k z).re := by
    conv_lhs => rw [← h1]
    rw [norm_mul, norm_exp]
  have h3 : (lambertW k z).re ≤ ‖lambertW k z‖ := re_le_norm _
  have h4 : Real.exp (lambertW k z).re ≤ Real.exp R' := Real.exp_le_exp.mpr (by linarith)
  have h5 : ‖z‖ ≤ R' * Real.exp R' := by
    rw [h2]
    exact mul_le_mul hR.le h4 (Real.exp_pos _).le (by positivity)
  linarith

theorem tendsto_log_add_pi_div : Tendsto (fun r : ℝ => (Real.log r + π) / r) atTop (𝓝 0) := by
  have h1 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun r : ℝ => π / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  simpa [add_div] using h1.add h2

/-- `ln W / W → 0`. -/
theorem tendsto_log_div_lambertW (k : ℤ) :
    Tendsto (fun z => log (lambertW k z) / lambertW k z) (Bornology.cobounded ℂ) (𝓝 0) := by
  have ht := tendsto_norm_lambertW k
  refine squeeze_zero_norm' ?_ (tendsto_log_add_pi_div.comp ht)
  filter_upwards [ht.eventually_ge_atTop 1] with z hz
  have hw : 0 < ‖lambertW k z‖ := by linarith
  rw [norm_div, Function.comp_apply, div_le_div_iff_of_pos_right hw]
  have := norm_clog_le_abs_log_add_pi (lambertW k z)
  rwa [abs_of_nonneg (Real.log_nonneg hz)] at this

/-- **DLMF 4.13.1_1**: `W_k(z) = ln_k z − ln(ln_k z) + o(1)` as `|z| → ∞`. -/
theorem dlmf_4_13_1_1 (k : ℤ) :
    Tendsto (fun z => lambertW k z - (lnk k z - log (lnk k z))) (Bornology.cobounded ℂ)
      (𝓝 0) := by
  set g := fun z => log (lambertW k z) / lambertW k z
  have hg := tendsto_log_div_lambertW k
  have ht := tendsto_norm_lambertW k
  -- `u = W / ln_k z = (1 + ln W / W)⁻¹ → 1`
  have hu : Tendsto (fun z => (1 + g z)⁻¹) (Bornology.cobounded ℂ) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ))).add hg
    simpa using this.inv₀ (by norm_num)
  have h1 : (1 : ℂ) ∈ slitPlane := one_mem_slitPlane
  have hlogu := (continuousAt_clog h1).tendsto.comp hu
  have hargu := ((continuousAt_arg h1).tendsto.comp hu).eventually
    (Metric.ball_mem_nhds (arg 1) (by positivity : (0 : ℝ) < π / 2))
  rw [log_one] at hlogu
  have hneg := hlogu.neg
  rw [neg_zero] at hneg
  refine hneg.congr' ?_
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 1, ht.eventually_ge_atTop 1,
    hargu] with z hz hw ha
  set w := lambertW k z
  have hw0 : w ≠ 0 := fun h => by simp [w, h] at hw; linarith
  set ξ := lnk k z
  have hξ : w + log w = ξ := lambertW_add_log k hz
  have hre : 0 ≤ ξ.re := by rw [lnk_re]; exact (Real.log_pos hz).le
  have hξ0 : ξ ≠ 0 := fun h => by
    have h2 : ξ.re = Real.log ‖z‖ := lnk_re k z
    rw [h] at h2; simp at h2; linarith [Real.log_pos hz]
  have hξw : ξ = w * (1 + g z) := by
    rw [← hξ]; show w + log w = w * (1 + log w / w); field_simp
  have h1g : 1 + g z ≠ 0 := fun h => hξ0 (by rw [hξw, h, mul_zero])
  have hu : (1 + g z)⁻¹ ≠ 0 := inv_ne_zero h1g
  have hwu : w = ξ * (1 + g z)⁻¹ := by rw [hξw]; field_simp
  simp only [Function.comp_apply, Real.dist_eq, arg_one, sub_zero] at ha
  have hargξ := abs_arg_le_pi_div_two_iff.mpr hre
  have hlog : log w = log ξ + log (1 + g z)⁻¹ := by
    rw [hwu]
    refine log_mul hξ0 hu ⟨?_, ?_⟩ <;>
      linarith [(abs_le.mp hargξ).1, (abs_le.mp hargξ).2, (abs_lt.mp ha).1, (abs_lt.mp ha).2]
  show -log (1 + g z)⁻¹ = w - (ξ - log ξ)
  have : w = ξ - log w := by rw [← hξ]; ring
  rw [this, hlog]; ring

end Azurite.DLMF
