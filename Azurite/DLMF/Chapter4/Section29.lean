/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section29InvHyp

/-!
# DLMF §4.29 Graphics (hyperbolic functions)

The principal inverse hyperbolic functions are those of §4.37 (`Section29InvHyp.lean`).

* §4.29(i), Figures 4.29.1, 4.29.3, 4.29.5: the plotted functions are real on the real axis
  (`dlmf_4_29_F1`, `dlmf_4_29_F3`, `dlmf_4_29_F5`).
* Figure 4.29.2: `arcsinh x` is real for all `x`, `arccosh x` for `x ≥ 1`; "`arccosh x` is complex
  when `x < 1`": on that part of its cut both one-sided limits exist and are nonreal
  (`dlmf_4_29_F2`).
* Figure 4.29.4: `arctanh x` is complex for `|x| > 1`, `arccoth x` for `0 < |x| < 1`
  (`dlmf_4_29_F4`; `arccoth 0 = arctanh(1/0)` is not defined by 4.37.9).
* Figure 4.29.6: `arccsch x` is real (`x ≠ 0`); "`arcsech x` is complex when `x < 0` and `x > 1`"
  (`dlmf_4_29_F6`).
* §4.29(ii): `w = sinh z` is Figure 4.15.7 rotated through `½π` in both planes (4.28.8):
  `dlmf_4_29_ii_sinh` (the strip `|ℑz| < ½π` maps conformally onto the plane cut along
  `(−i∞, −i]`, `[i, i∞)`, with inverse `arcsinh`). The surfaces "can be visualized with the aid
  of (4.28.8)–(4.28.13)": `dlmf_4_28_8` … `dlmf_4_28_13`.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-! ### §4.29(i) -/

/-- **Figure 4.29.1**: `sinh x` and `cosh x` are real for real `x`. -/
theorem dlmf_4_29_F1 (x : ℝ) : sinh (x : ℂ) = Real.sinh x ∧ cosh (x : ℂ) = Real.cosh x :=
  ⟨(ofReal_sinh x).symm, (ofReal_cosh x).symm⟩

/-- **Figure 4.29.3**: `tanh x` and `coth x` are real for real `x`. -/
theorem dlmf_4_29_F3 (x : ℝ) :
    tanh (x : ℂ) = Real.tanh x ∧ cothC x = ((Real.cosh x / Real.sinh x : ℝ) : ℂ) := by
  refine ⟨(ofReal_tanh x).symm, ?_⟩
  rw [cothC_eq_cosh_div_sinh, ofReal_div, ofReal_cosh, ofReal_sinh]

/-- **Figure 4.29.5**: `csch x` and `sech x` are real for real `x`. -/
theorem dlmf_4_29_F5 (x : ℝ) :
    cschC x = ((1 / Real.sinh x : ℝ) : ℂ) ∧ sechC x = ((1 / Real.cosh x : ℝ) : ℂ) := by
  rw [cschC, sechC, ofReal_div, ofReal_div, ofReal_one, ofReal_sinh, ofReal_cosh]
  exact ⟨rfl, rfl⟩

/-- **Figure 4.29.2**: principal values of `arcsinh x` (real for all `x`) and `arccosh x` (real
for `x ≥ 1`); "`arccosh x` is complex when `x < 1`": there `x` lies on the cut `(−∞, 1]`, and the
two values of the principal branch (the limits from above and below) are both nonreal. -/
theorem dlmf_4_29_F2 :
    (∀ x : ℝ, arcsinhD x = Real.arsinh x) ∧ (∀ x : ℝ, 1 ≤ x → arccoshD x = Real.arcosh x) ∧
      ∀ x : ℝ, x < 1 → ∃ b c : ℂ, b.im ≠ 0 ∧ c.im ≠ 0 ∧
        Tendsto arccoshD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
        Tendsto arccoshD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c) :=
  ⟨arcsinhD_ofReal, fun _ hx => arccoshD_ofReal hx, fun _ hx => arccoshD_cut_limits hx⟩

theorem one_div_ofReal (x : ℝ) : (1 : ℂ) / x = ((1 / x : ℝ) : ℂ) := by
  rw [ofReal_div, ofReal_one]

/-- **Figure 4.29.4**: principal values of `arctanh x` (real for `|x| < 1`) and `arccoth x` (real
for `|x| > 1`); "`arctanh x` is complex when `x < −1` or `x > 1`, and `arccoth x` is complex when
`−1 < x < 1`" (`x ≠ 0`): both one-sided limits on the cuts are nonreal. -/
theorem dlmf_4_29_F4 :
    (∀ x : ℝ, |x| < 1 → arctanhD x = Real.artanh x) ∧
      (∀ x : ℝ, 1 < |x| → arccothD x = Real.artanh (1 / x)) ∧
      (∀ x : ℝ, 1 < |x| → ∃ b c : ℂ, b.im ≠ 0 ∧ c.im ≠ 0 ∧
        Tendsto arctanhD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
        Tendsto arctanhD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c)) ∧
      ∀ x : ℝ, x ≠ 0 → |x| < 1 → ∃ b c : ℂ, b.im ≠ 0 ∧ c.im ≠ 0 ∧
        Tendsto arccothD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
        Tendsto arccothD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c) := by
  refine ⟨fun x hx => arctanhD_ofReal (abs_lt.mp hx), fun x hx => ?_,
    fun _ hx => arctanhD_cut_limits hx, fun x hx0 hx1 => ?_⟩
  · have h : |1 / x| < 1 := by
      rw [abs_one_div]; exact (div_lt_one (by linarith)).mpr hx
    rw [arccothD, one_div_ofReal, arctanhD_ofReal (abs_lt.mp h)]
  · obtain ⟨b, c, hb, hc, e1, e2⟩ := arctanhD_cut_limits (one_lt_abs_one_div hx0 hx1)
    obtain ⟨t1, t2⟩ := tendsto_one_div_nhdsWithin hx0
    exact ⟨c, b, hc, hb, e2.comp t1, e1.comp t2⟩

/-- **Figure 4.29.6**: principal values of `arccsch x` (real for `x ≠ 0`) and `arcsech x` (real
for `0 < x ≤ 1`); "`arcsech x` is complex when `x < 0` and `x > 1`": both one-sided limits on the
cuts are nonreal. -/
theorem dlmf_4_29_F6 :
    (∀ x : ℝ, arccschD x = Real.arsinh (1 / x)) ∧
      (∀ x : ℝ, 0 < x → x ≤ 1 → arcsechD x = Real.arcosh (1 / x)) ∧
      ∀ x : ℝ, x < 0 ∨ 1 < x → ∃ b c : ℂ, b.im ≠ 0 ∧ c.im ≠ 0 ∧
        Tendsto arcsechD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
        Tendsto arcsechD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c) := by
  refine ⟨fun x => by rw [arccschD, one_div_ofReal, arcsinhD_ofReal], fun x hx0 hx1 => ?_,
    fun x hx => ?_⟩
  · rw [arcsechD, one_div_ofReal, arccoshD_ofReal (one_le_one_div hx0 hx1)]
  · have hx0 : x ≠ 0 := by
      rcases hx with h | h
      · exact h.ne
      · exact (by linarith : (0 : ℝ) < x).ne'
    have h1 : 1 / x < 1 := by
      rcases hx with h | h
      · linarith [one_div_neg.mpr h]
      · exact (div_lt_one (by linarith)).mpr h
    obtain ⟨b, c, hb, hc, e1, e2⟩ := arccoshD_cut_limits h1
    obtain ⟨t1, t2⟩ := tendsto_one_div_nhdsWithin hx0
    exact ⟨c, b, hc, hb, e2.comp t1, e1.comp t2⟩

/-! ### §4.29(ii) -/

/-- The strip `|ℑz| < ½π` (Figure 4.15.7's strip rotated through `½π`). -/
def sinhStrip : Set ℂ := {z | |z.im| < π / 2}

theorem I_mul_mem_sinStrip {z : ℂ} : I * z ∈ sinStrip ↔ z ∈ sinhStrip := by
  simp only [sinStrip, sinhStrip, mem_ofPred_eq, mul_re, I_re, zero_mul, I_im, one_mul,
    zero_sub, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **§4.29(ii)**: "The conformal mapping `w = sinh z` is obtainable from Figure 4.15.7 by
rotating both the `w`-plane and the `z`-plane through an angle `½π`, compare (4.28.8)":
`sinh z = −i sin(iz)`, and `sinh` maps the strip `|ℑz| < ½π` bijectively and conformally onto
the plane cut along `(−i∞, −i]` and `[i, i∞)`, with inverse the principal `arcsinh`. -/
theorem dlmf_4_29_ii_sinh :
    (∀ z, sinh z = -I * sin (I * z)) ∧ BijOn sinh sinhStrip arcsinhCut ∧
      (∀ z ∈ sinhStrip, arcsinhD (sinh z) = z) ∧ (∀ w ∈ arcsinhCut, sinh (arcsinhD w) = w) ∧
      (∀ z ∈ sinhStrip, HasDerivAt sinh (cosh z) z ∧ cosh z ≠ 0) ∧
      (∀ w ∈ arcsinhCut, HasDerivAt arcsinhD ((1 + w ^ 2) ^ (1 / 2 : ℂ))⁻¹ w) := by
  have hsin : ∀ z, sin (I * z) = I * sinh z := dlmf_4_28_8
  have hinv : ∀ z ∈ sinhStrip, arcsinhD (sinh z) = z := fun z hz => by
    rw [arcsinhD_eq, ← hsin, arcsinD_sin (I_mul_mem_sinStrip.mpr hz), neg_I_mul_I_mul]
  refine ⟨sinh_eq_neg_I_mul_sin, ⟨fun z hz => ?_, fun a ha b hb hab => ?_, fun w hw => ?_⟩,
    hinv, fun _ hw => sinh_arcsinhD hw, fun z hz => ⟨hasDerivAt_sinh z, ?_⟩,
    fun _ hw => hasDerivAt_arcsinhD hw⟩
  · rw [← I_mul_mem_arcsinCut, ← hsin]
    exact sin_mem_arcsinCut (I_mul_mem_sinStrip.mpr hz)
  · rw [← hinv a ha, ← hinv b hb, hab]
  · refine ⟨arcsinhD w, ?_, sinh_arcsinhD hw⟩
    rw [← I_mul_mem_sinStrip, ← arcsinD_I_mul_arcsinhD]
    exact (arcsinD_props (I_mul_mem_arcsinCut.mpr hw)).2.1
  · rw [← dlmf_4_28_9]
    exact cos_ne_zero_of_mem_sinStrip (I_mul_mem_sinStrip.mpr hz)

end Azurite.DLMF
