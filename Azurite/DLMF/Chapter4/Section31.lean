/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section16
import Azurite.DLMF.Chapter4.Section17
import Azurite.DLMF.Chapter4.Section28
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF §4.31 Special Values and Limits (hyperbolic functions)

* Table 4.31.1 (complex `z`), one theorem per column `z = 0, ½πi, πi, (3/2)πi, ∞`:
  `dlmf_table_4_31_1_zero`, `_pi_div_two_I`, `_pi_I`, `_three_pi_div_two_I`, `_infty`.
  An `∞` entry at a finite `z₀` is a pole: `‖f(w)‖ → ∞` as `w → z₀`, `w ≠ z₀`
  (`tendsto_norm_div_of_simple_zero`, §4.14).
* **Imprecisions**: the entries `∞i` (at `½πi`) and `−∞i` (at `(3/2)πi`) of `tanh` cannot differ,
  since `tanh` has period `πi` (`dlmf_table_4_31_1_tanh_poles_same`); both are the same simple
  pole. The column `z = ∞` holds as `ℜz → +∞` (uniformly in `ℑz`), not as `z → ∞` in `ℂ`:
  `tanh` has no limit at `∞` (`dlmf_table_4_31_1_infty_not_cobounded`; `tanh x → −1` as
  `x → −∞`).
* 4.31.1–4.31.3 (`z → 0`, `z ≠ 0`): from 4.17.1–4.17.3 via `z ↦ iz` (4.28.8–4.28.10).
-/

open Set Filter Topology Complex Bornology
open scoped Real

namespace Azurite.DLMF

/-! ### Values and poles -/

theorem cosh_ne_zero_of_sinh_eq_zero {z : ℂ} (h : sinh z = 0) : cosh z ≠ 0 := fun hc => by
  have := cosh_sq_sub_sinh_sq z; rw [h, hc] at this; norm_num at this

theorem sinh_ne_zero_of_cosh_eq_zero {z : ℂ} (h : cosh z = 0) : sinh z ≠ 0 := fun hs => by
  have := cosh_sq_sub_sinh_sq z; rw [h, hs] at this; norm_num at this

theorem tanh_eq_sinh_div_cosh_fun : tanh = fun z => sinh z / cosh z :=
  funext tanh_eq_sinh_div_cosh

/-- Poles of `csch` and `coth` at the zeros of `sinh`. -/
theorem csch_coth_poles {z₀ : ℂ} (hz : sinh z₀ = 0) :
    Tendsto (fun w => ‖cschC w‖) (𝓝[≠] z₀) atTop ∧
      Tendsto (fun w => ‖cothC w‖) (𝓝[≠] z₀) atTop := by
  have hc := cosh_ne_zero_of_sinh_eq_zero hz
  refine ⟨tendsto_norm_div_of_simple_zero continuousAt_const one_ne_zero (hasDerivAt_sinh z₀) hz
    hc, ?_⟩
  have h := tendsto_norm_div_of_simple_zero continuous_cosh.continuousAt hc (hasDerivAt_sinh z₀)
    hz hc
  simpa [cothC_eq_cosh_div_sinh] using h

/-- Poles of `tanh` and `sech` at the zeros of `cosh`. -/
theorem tanh_sech_poles {z₀ : ℂ} (hz : cosh z₀ = 0) :
    Tendsto (fun w => ‖tanh w‖) (𝓝[≠] z₀) atTop ∧
      Tendsto (fun w => ‖sechC w‖) (𝓝[≠] z₀) atTop := by
  have hs := sinh_ne_zero_of_cosh_eq_zero hz
  refine ⟨?_, tendsto_norm_div_of_simple_zero continuousAt_const one_ne_zero
    (hasDerivAt_cosh z₀) hz hs⟩
  have h := tendsto_norm_div_of_simple_zero continuous_sinh.continuousAt hs (hasDerivAt_cosh z₀)
    hz hs
  simpa [tanh_eq_sinh_div_cosh] using h

/-- **Table 4.31.1**, `z = 0`: `sinh 0 = 0`, `cosh 0 = 1`, `tanh 0 = 0`, `csch 0 = ∞`,
`sech 0 = 1`, `coth 0 = ∞`. -/
theorem dlmf_table_4_31_1_zero :
    sinh 0 = 0 ∧ cosh 0 = 1 ∧ tanh 0 = 0 ∧ Tendsto (fun w => ‖cschC w‖) (𝓝[≠] 0) atTop ∧
      sechC 0 = 1 ∧ Tendsto (fun w => ‖cothC w‖) (𝓝[≠] 0) atTop := by
  obtain ⟨h1, h2⟩ := csch_coth_poles sinh_zero
  exact ⟨sinh_zero, cosh_zero, tanh_zero, h1, by simp [sechC], h2⟩

/-- **Table 4.31.1**, `z = ½πi`: `sinh = i`, `cosh = 0`, `tanh = ∞i` (a pole), `csch = −i`,
`sech = ∞`, `coth = 0`. -/
theorem dlmf_table_4_31_1_pi_div_two_I :
    sinh (π / 2 * I) = I ∧ cosh (π / 2 * I) = 0 ∧
      Tendsto (fun w => ‖tanh w‖) (𝓝[≠] (π / 2 * I)) atTop ∧ cschC (π / 2 * I) = -I ∧
      Tendsto (fun w => ‖sechC w‖) (𝓝[≠] (π / 2 * I)) atTop ∧ cothC (π / 2 * I) = 0 := by
  have hs : sinh (π / 2 * I) = I := by rw [sinh_mul_I, sin_pi_div_two, one_mul]
  have hc : cosh (π / 2 * I) = 0 := by rw [cosh_mul_I, cos_pi_div_two]
  obtain ⟨h1, h2⟩ := tanh_sech_poles hc
  refine ⟨hs, hc, h1, ?_, h2, ?_⟩
  · rw [cschC, hs, one_div, inv_I]
  · rw [cothC_eq_cosh_div_sinh, hc, zero_div]

/-- **Table 4.31.1**, `z = πi`: `sinh = 0`, `cosh = −1`, `tanh = 0`, `csch = ∞`, `sech = −1`,
`coth = ∞`. -/
theorem dlmf_table_4_31_1_pi_I :
    sinh (π * I) = 0 ∧ cosh (π * I) = -1 ∧ tanh (π * I) = 0 ∧
      Tendsto (fun w => ‖cschC w‖) (𝓝[≠] (π * I)) atTop ∧ sechC (π * I) = -1 ∧
      Tendsto (fun w => ‖cothC w‖) (𝓝[≠] (π * I)) atTop := by
  have hs : sinh (π * I) = 0 := by rw [sinh_mul_I, sin_pi, zero_mul]
  have hc : cosh (π * I) = -1 := by rw [cosh_mul_I, cos_pi]
  obtain ⟨h1, h2⟩ := csch_coth_poles hs
  refine ⟨hs, hc, by rw [tanh_eq_sinh_div_cosh, hs, zero_div], h1, ?_, h2⟩
  rw [sechC, hc]; norm_num

/-- **Table 4.31.1**, `z = (3/2)πi`: `sinh = −i`, `cosh = 0`, `tanh = −∞i` (a pole), `csch = i`,
`sech = ∞`, `coth = 0`. -/
theorem dlmf_table_4_31_1_three_pi_div_two_I :
    sinh (3 * π / 2 * I) = -I ∧ cosh (3 * π / 2 * I) = 0 ∧
      Tendsto (fun w => ‖tanh w‖) (𝓝[≠] (3 * π / 2 * I)) atTop ∧ cschC (3 * π / 2 * I) = I ∧
      Tendsto (fun w => ‖sechC w‖) (𝓝[≠] (3 * π / 2 * I)) atTop ∧
      cothC (3 * π / 2 * I) = 0 := by
  have hs : sinh (3 * π / 2 * I) = -I := by
    rw [sinh_mul_I, sin_three_pi_div_two']; ring
  have hc : cosh (3 * π / 2 * I) = 0 := by rw [cosh_mul_I, cos_three_pi_div_two']
  obtain ⟨h1, h2⟩ := tanh_sech_poles hc
  refine ⟨hs, hc, h1, ?_, h2, ?_⟩
  · rw [cschC, hs, one_div, inv_neg, inv_I, neg_neg]
  · rw [cothC_eq_cosh_div_sinh, hc, zero_div]

/-- **Imprecision in Table 4.31.1**: the entries `∞i` and `−∞i` of `tanh` at `½πi` and
`(3/2)πi` describe the same behaviour, since `tanh(z + πi) = tanh z`. -/
theorem dlmf_table_4_31_1_tanh_poles_same (w : ℂ) :
    tanh (3 * π / 2 * I + w) = tanh (π / 2 * I + w) := by
  rw [show 3 * π / 2 * I + w = (π / 2 * I + w) + π * I by ring]
  exact dlmf_4_28_tanh_periodic _

/-! ### The column `z = ∞` (as `ℜz → +∞`) -/

theorem tendsto_re_comap : Tendsto re (comap re atTop) atTop := tendsto_comap

theorem tendsto_exp_neg_comap_re :
    Tendsto (fun z : ℂ => exp (-z)) (comap re atTop) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_exp, neg_re]
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_re_comap

theorem tendsto_norm_exp_comap_re :
    Tendsto (fun z : ℂ => Real.exp z.re) (comap re atTop) atTop :=
  Real.tendsto_exp_atTop.comp tendsto_re_comap

theorem exp_mul_exp_neg' (z : ℂ) : exp z * exp (-z) = 1 := by
  rw [← exp_add, add_neg_cancel, exp_zero]

/-- **Table 4.31.1**, `z = ∞`, read as `ℜz → +∞`: `sinh, cosh → ∞`, `tanh → 1`, `csch → 0`,
`sech → 0`, `coth → 1`. -/
theorem dlmf_table_4_31_1_infty :
    Tendsto (fun z => ‖sinh z‖) (comap re atTop) atTop ∧
      Tendsto (fun z => ‖cosh z‖) (comap re atTop) atTop ∧
      Tendsto tanh (comap re atTop) (𝓝 1) ∧ Tendsto cschC (comap re atTop) (𝓝 0) ∧
      Tendsto sechC (comap re atTop) (𝓝 0) ∧ Tendsto cothC (comap re atTop) (𝓝 1) := by
  have hp := tendsto_exp_neg_comap_re
  have hq : Tendsto (fun z : ℂ => exp (-z) ^ 2) (comap re atTop) (𝓝 0) := by
    simpa using hp.pow 2
  -- `‖exp(−z)‖ ≤ 1` eventually
  have hsmall : ∀ᶠ z in comap re atTop, ‖exp (-z)‖ ≤ 1 := by
    filter_upwards [tendsto_re_comap.eventually_ge_atTop 0] with z hz
    rw [norm_exp, neg_re]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hgrow : Tendsto (fun z : ℂ => (Real.exp z.re - 1) / 2) (comap re atTop) atTop := by
    have h := (tendsto_atTop_add_const_right _ (-1) tendsto_norm_exp_comap_re).atTop_div_const
      (by norm_num : (0 : ℝ) < 2)
    exact h.congr fun z => by ring
  have hlow : ∀ z : ℂ, ‖exp (-z)‖ ≤ 1 → (Real.exp z.re - 1) / 2 ≤ ‖sinh z‖ ∧
      (Real.exp z.re - 1) / 2 ≤ ‖cosh z‖ := by
    intro z hz
    have he : ‖exp z‖ = Real.exp z.re := norm_exp z
    constructor
    · rw [sinh, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
      have := norm_sub_norm_le (exp z) (exp (-z))
      linarith
    · rw [cosh, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
      have := norm_sub_le_norm_add (exp z) (exp (-z))
      have h2 : ‖exp z‖ - ‖exp (-z)‖ ≤ ‖exp z + exp (-z)‖ := by
        have := norm_sub_norm_le (exp z) (-exp (-z))
        rw [norm_neg, sub_neg_eq_add] at this; exact this
      linarith
  -- algebraic forms in `p = e^{−z}`
  have etanh : ∀ z : ℂ, tanh z = (1 - exp (-z) ^ 2) / (1 + exp (-z) ^ 2) := fun z => by
    rw [tanh_eq_sinh_div_cosh, sinh, cosh, div_div_div_cancel_right₀ (two_ne_zero' ℂ),
      ← mul_div_mul_right _ _ (exp_ne_zero (-z))]
    congr 1 <;> linear_combination exp_mul_exp_neg' z
  have ecsch : ∀ z : ℂ, cschC z = 2 * exp (-z) / (1 - exp (-z) ^ 2) := fun z => by
    rw [cschC, sinh, one_div_div, ← mul_div_mul_right _ _ (exp_ne_zero (-z))]
    congr 1; linear_combination exp_mul_exp_neg' z
  have esech : ∀ z : ℂ, sechC z = 2 * exp (-z) / (1 + exp (-z) ^ 2) := fun z => by
    rw [sechC, cosh, one_div_div, ← mul_div_mul_right _ _ (exp_ne_zero (-z))]
    congr 1; linear_combination exp_mul_exp_neg' z
  have ecoth : ∀ z : ℂ, cothC z = (1 + exp (-z) ^ 2) / (1 - exp (-z) ^ 2) := fun z => by
    rw [cothC, etanh, one_div_div]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono' _ (hsmall.mono fun z hz => (hlow z hz).1) hgrow
  · exact tendsto_atTop_mono' _ (hsmall.mono fun z hz => (hlow z hz).2) hgrow
  · rw [funext etanh]
    have h := ((tendsto_const_nhds (x := (1 : ℂ))).sub hq).div
      ((tendsto_const_nhds (x := (1 : ℂ))).add hq) (by norm_num)
    rw [sub_zero, add_zero, div_one] at h
    exact h
  · rw [funext ecsch]
    have h := (hp.const_mul 2).div ((tendsto_const_nhds (x := (1 : ℂ))).sub hq) (by norm_num)
    rw [mul_zero, zero_div] at h
    exact h
  · rw [funext esech]
    have h := (hp.const_mul 2).div ((tendsto_const_nhds (x := (1 : ℂ))).add hq) (by norm_num)
    rw [mul_zero, zero_div] at h
    exact h
  · rw [funext ecoth]
    have h := ((tendsto_const_nhds (x := (1 : ℂ))).add hq).div
      ((tendsto_const_nhds (x := (1 : ℂ))).sub hq) (by norm_num)
    rw [sub_zero, add_zero, div_one] at h
    exact h

/-- **Imprecision in Table 4.31.1**: as `z → ∞` in `ℂ` (no restriction on `ℜz`), `tanh` has no
limit, since `tanh x → 1` as `x → +∞` and `tanh x → −1` as `x → −∞`. -/
theorem dlmf_table_4_31_1_infty_not_cobounded :
    Tendsto (fun x : ℝ => tanh (x : ℂ)) atBot (𝓝 (-1)) ∧
      ¬ ∃ L, Tendsto tanh (cobounded ℂ) (𝓝 L) := by
  have hT := dlmf_table_4_31_1_infty.2.2.1
  have hpos : Tendsto (fun x : ℝ => (x : ℂ)) atTop (comap re atTop) :=
    tendsto_comap_iff.mpr (tendsto_id.congr fun x => by simp)
  have hneg : Tendsto (fun x : ℝ => tanh (x : ℂ)) atBot (𝓝 (-1)) := by
    have h := (hT.comp hpos).comp tendsto_neg_atBot_atTop
    have h' := h.neg
    refine h'.congr fun x => ?_
    simp [Function.comp, tanh_neg]
  refine ⟨hneg, fun ⟨L, hL⟩ => ?_⟩
  have hcb : ∀ l : Filter ℝ, Tendsto (fun x : ℝ => |x|) l atTop →
      Tendsto (fun x : ℝ => (x : ℂ)) l (cobounded ℂ) := fun l hl => by
    rw [← tendsto_norm_atTop_iff_cobounded]; simpa using hl
  have h1 := hL.comp (hcb atTop (tendsto_abs_atTop_atTop.comp tendsto_id))
  have h2 := hL.comp (hcb atBot tendsto_abs_atBot_atTop)
  have e1 := tendsto_nhds_unique h1 (hT.comp hpos)
  have e2 := tendsto_nhds_unique h2 hneg
  rw [e1] at e2
  norm_num at e2

/-! ### 4.31.1–4.31.3 -/

theorem tendsto_I_mul_punctured :
    Tendsto (fun z : ℂ => I * z) (𝓝[≠] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
  · have hc : Continuous fun z : ℂ => I * z := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  · exact mul_ne_zero I_ne_zero hz

/-- **DLMF 4.31.1**: `sinh z / z → 1` as `z → 0`. -/
theorem dlmf_4_31_1 : Tendsto (fun z : ℂ => sinh z / z) (𝓝[≠] 0) (𝓝 1) := by
  refine (dlmf_4_17_1.comp tendsto_I_mul_punctured).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  simp only [Function.comp_apply, dlmf_4_28_8]
  field_simp

/-- **DLMF 4.31.2**: `tanh z / z → 1` as `z → 0`. -/
theorem dlmf_4_31_2 : Tendsto (fun z : ℂ => tanh z / z) (𝓝[≠] 0) (𝓝 1) := by
  refine (dlmf_4_17_2.comp tendsto_I_mul_punctured).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  simp only [Function.comp_apply, dlmf_4_28_10]
  field_simp

/-- **DLMF 4.31.3**: `(cosh z − 1)/z² → 1/2` as `z → 0`. -/
theorem dlmf_4_31_3 : Tendsto (fun z : ℂ => (cosh z - 1) / z ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  refine (dlmf_4_17_3.comp tendsto_I_mul_punctured).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  simp only [Function.comp_apply, dlmf_4_28_9]
  rw [mul_pow, I_sq]
  field_simp
  ring

end Azurite.DLMF
