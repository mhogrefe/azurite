/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13BranchPoint
import Azurite.DLMF.Chapter4.Section13Deriv

/-!
# DLMF Figure 4.13.2: the images of the Riemann sheets

* `mul_exp_im_eq_zero_iff`: `w e^w` is real exactly on the real axis and on the curves
  `ξ = −η cot η` (`w = ξ + iη`, `η ∉ πℤ`) — the curves drawn in the figure.
* `figure_4_13_2_sheet0`: `W₀` maps the first sheet `|ph(z + e⁻¹)| < π` (`firstSheet = cutW0`)
  bijectively onto `lambertRegion0`, the region enclosed by the green curve `ξ = −η cot η`,
  `|η| < π`.
* `figure_4_13_2_sheet`: for `k ≠ 0`, `W_k` maps the sheet `(2k − 1)π < ph z < (2k + 1)π`
  (`ℂ ∖ (−∞, 0]`) bijectively onto `sheetRegion k = {w ≠ 0 : (2k − 1)π < ℑw + ph w < (2k + 1)π}`,
  bounded by the curves where `ℑw + ph w = (2k ± 1)π`.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-! ### The curves -/

/-- `ℑ(w e^w) = 0` iff `η = 0` or `ξ = −η cot η` (`w = ξ + iη`). -/
theorem mul_exp_im_eq_zero_iff (w : ℂ) : (w * exp w).im = 0 ↔
    w.im = 0 ∨ (Real.sin w.im ≠ 0 ∧ w.re = -(w.im * Real.cos w.im / Real.sin w.im)) := by
  rw [mul_exp_im, mul_eq_zero, or_iff_right (Real.exp_pos _).ne']
  constructor
  · intro h
    by_cases hs : Real.sin w.im = 0
    · left
      have hc : Real.cos w.im ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq w.im]
      rw [hs] at h
      have : w.im * Real.cos w.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · rw [h'] at hc; norm_num at hc
    · right; refine ⟨hs, ?_⟩; field_simp; linear_combination h
  · rintro (h | ⟨hs, h⟩)
    · rw [h]; simp
    · rw [h]; field_simp; ring

/-! ### Sheets and the solutions on them -/

/-- A solution `w ≠ 0` with `(2k − 1)π < ℑw + ph w < (2k + 1)π` satisfies
`w + ln w = ln(w e^w) + 2πik`. -/
theorem add_log_of_sheet {w : ℂ} (hw : w ≠ 0) (k : ℤ)
    (h1 : (2 * k - 1) * π < w.im + arg w) (h2 : w.im + arg w < (2 * k + 1) * π) :
    w + log w = log (w * exp w) + k * (2 * π * I) := by
  have hz : w * exp w ≠ 0 := mul_ne_zero hw (exp_ne_zero w)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, w + log w = log (w * exp w) + m * (2 * π * I) := by
    apply exp_eq_exp_iff_exists_int.mp
    rw [exp_add, exp_log hw, exp_log hz, mul_comm]
  have him := im_eq_of_add_log hm
  have ha1 := neg_pi_lt_arg (w * exp w)
  have ha2 := arg_le_pi (w * exp w)
  have : m = k := by
    refine int_eq_of_mul_pi_bounds (m := k) ?_ ?_ <;> nlinarith [Real.pi_pos]
  rw [hm, this]

/-- On the sheet `(2k − 1)π < ℑw + ph w < (2k + 1)π`, `W_k(w e^w) = w`. -/
theorem lambertW_mul_exp_of_sheet {w : ℂ} (hw : w ≠ 0) (k : ℤ)
    (h1 : (2 * k - 1) * π < w.im + arg w) (h2 : w.im + arg w < (2 * k + 1) * π) :
    lambertW k (w * exp w) = w := by
  have hz : w * exp w ≠ 0 := mul_ne_zero hw (exp_ne_zero w)
  have hadd := add_log_of_sheet hw k h1 h2
  have him := im_eq_of_add_log hadd
  rw [lambertW_of_ne hz]
  set ζ := log (w * exp w) + 2 * π * k * I
  have hζ : w + log w = ζ := by rw [hadd]; simp only [ζ]; ring
  have hζim : ζ.im = w.im + arg w := by
    have := congrArg im hζ; rw [add_log_im] at this; exact this.symm
  -- `ℑζ` is never `±π` on an open sheet
  have hne : ∀ j : ℤ, ζ.im ≠ (2 * j + 1) * π := by
    intro j hj
    rw [hζim] at hj
    have a : (2 * (k : ℝ) - 1) < 2 * j + 1 := by
      have := h1.trans_le hj.le; exact lt_of_mul_lt_mul_right this Real.pi_pos.le
    have b : (2 * (j : ℝ) + 1) < 2 * k + 1 := by
      have := hj.symm.le.trans_lt h2; exact lt_of_mul_lt_mul_right this Real.pi_pos.le
    have a' : 2 * k - 1 < 2 * j + 1 := by exact_mod_cast a
    have b' : 2 * j + 1 < 2 * k + 1 := by exact_mod_cast b
    omega
  refine wrightOmega_eq (fun h => hne (-1) (by rw [h.1]; push_cast; ring))
    ⟨hw, hζ, fun h => absurd (by rw [h]; push_cast; ring) (hne 0)⟩

/-- On an open sheet, `w e^w` is not on `(−∞, 0]`. -/
theorem mul_exp_mem_slitPlane_of_sheet {w : ℂ} (hw : w ≠ 0) (k : ℤ)
    (h1 : (2 * k - 1) * π < w.im + arg w) (h2 : w.im + arg w < (2 * k + 1) * π) :
    w * exp w ∈ slitPlane := by
  have hz : w * exp w ≠ 0 := mul_ne_zero hw (exp_ne_zero w)
  have him := im_eq_of_add_log (add_log_of_sheet hw k h1 h2)
  rw [mem_slitPlane_iff_arg]
  refine ⟨fun h => ?_, hz⟩
  rw [h] at him
  rw [him] at h2
  linarith

/-! ### The first sheet and the green curve -/

/-- DLMF's first sheet `|ph(z + e⁻¹)| < π`. -/
def firstSheet : Set ℂ :=
  {z | z + ((Real.exp (-1) : ℝ) : ℂ) ≠ 0 ∧ |arg (z + ((Real.exp (-1) : ℝ) : ℂ))| < π}

theorem firstSheet_eq : firstSheet = cutW0 := by
  ext z
  simp only [firstSheet, cutW0, Set.mem_ofPred_eq]
  have hre : (z + ((Real.exp (-1) : ℝ) : ℂ)).re = z.re + Real.exp (-1) := by
    rw [add_re, ofReal_re]
  have him : (z + ((Real.exp (-1) : ℝ) : ℂ)).im = z.im := by rw [add_im, ofReal_im, add_zero]
  constructor
  · rintro ⟨h0, ha⟩ ⟨hi, hr⟩
    rcases hr.lt_or_eq with hlt | heq
    · have : arg (z + ((Real.exp (-1) : ℝ) : ℂ)) = π :=
        arg_eq_pi_iff.mpr ⟨by rw [hre]; linarith, by rw [him, hi]⟩
      rw [this, abs_of_pos Real.pi_pos] at ha; exact lt_irrefl _ ha
    · exact h0 (Complex.ext (by rw [hre, heq, zero_re]; ring) (by rw [him, hi, zero_im]))
  · intro h
    have hne : z + ((Real.exp (-1) : ℝ) : ℂ) ≠ 0 := fun e => h ⟨by
      have := congrArg im e; rwa [him, zero_im] at this, by
      have := congrArg re e; rw [hre, zero_re] at this; linarith⟩
    refine ⟨hne, lt_of_le_of_ne (abs_arg_le_pi _) fun e => ?_⟩
    have harg : arg (z + ((Real.exp (-1) : ℝ) : ℂ)) = π := by
      rcases abs_eq (Real.pi_pos.le) |>.mp e with h' | h'
      · exact h'
      · linarith [neg_pi_lt_arg (z + ((Real.exp (-1) : ℝ) : ℂ))]
    obtain ⟨h1, h2⟩ := arg_eq_pi_iff.mp harg
    rw [hre] at h1; rw [him] at h2
    exact h ⟨h2, by linarith⟩

/-- The region enclosed by the green curve `ξ = −η cot η`, `|η| < π` (and `ξ > −1` on the axis). -/
def lambertRegion0 : Set ℂ :=
  {w | |w.im| < π ∧ (w.im = 0 → -1 < w.re) ∧
    (w.im ≠ 0 → -(w.im * Real.cos w.im / Real.sin w.im) < w.re)}

/-- `‖w‖ sin(ph w + ℑw) = ξ sin η + η cos η`. -/
theorem norm_mul_sin_arg_add_im (w : ℂ) :
    ‖w‖ * Real.sin (arg w + w.im) = w.re * Real.sin w.im + w.im * Real.cos w.im := by
  rw [Real.sin_add, mul_add, ← mul_assoc, ← mul_assoc, norm_mul_sin_arg, norm_mul_cos_arg]
  ring

/-- Off the axis, `|ℑw + ph w| < π` iff `w` lies inside the green curve. -/
theorem abs_im_add_arg_lt_pi_iff {w : ℂ} (hη : w.im ≠ 0) :
    |w.im + arg w| < π ↔ |w.im| < π ∧ -(w.im * Real.cos w.im / Real.sin w.im) < w.re := by
  have hw : w ≠ 0 := fun h => hη (by simp [h])
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have key := norm_mul_sin_arg_add_im w
  rcases lt_or_gt_of_ne hη with hneg | hpos
  · obtain ⟨ha1, ha2⟩ := arg_mem_Ioo_of_im_neg hneg
    constructor
    · intro h
      have hθ := (abs_lt.mp h).1
      have hη' : -π < w.im := by linarith
      have hs : Real.sin w.im < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hneg hη'
      have hsa : Real.sin (arg w + w.im) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
      have hc : w.re * Real.sin w.im + w.im * Real.cos w.im < 0 := by
        rw [← key]; exact mul_neg_of_pos_of_neg hn hsa
      refine ⟨abs_lt.mpr ⟨hη', by linarith [Real.pi_pos]⟩, ?_⟩
      rw [neg_lt, lt_div_iff_of_neg hs]
      linarith
    · rintro ⟨h1, h2⟩
      have hη' : -π < w.im := (abs_lt.mp h1).1
      have hs : Real.sin w.im < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hneg hη'
      rw [neg_lt, lt_div_iff_of_neg hs] at h2
      have hc : ‖w‖ * Real.sin (arg w + w.im) < 0 := by rw [key]; linarith
      have hsa : Real.sin (arg w + w.im) < 0 := by
        by_contra hc'; push Not at hc'; nlinarith
      have : -π < arg w + w.im := by
        by_contra hc'; push Not at hc'
        have : 0 ≤ Real.sin (arg w + w.im + 2 * π) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        rw [Real.sin_add_two_pi] at this; linarith
      exact abs_lt.mpr ⟨by linarith, by linarith [Real.pi_pos]⟩
  · obtain ⟨ha1, ha2⟩ := arg_mem_Ioo_of_im_pos hpos
    constructor
    · intro h
      have hθ := (abs_lt.mp h).2
      have hη' : w.im < π := by linarith
      have hs : 0 < Real.sin w.im := Real.sin_pos_of_pos_of_lt_pi hpos hη'
      have hsa : 0 < Real.sin (arg w + w.im) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hc : 0 < w.re * Real.sin w.im + w.im * Real.cos w.im := by
        rw [← key]; exact mul_pos hn hsa
      refine ⟨abs_lt.mpr ⟨by linarith [Real.pi_pos], hη'⟩, ?_⟩
      rw [neg_lt, lt_div_iff₀ hs]
      linarith
    · rintro ⟨h1, h2⟩
      have hη' : w.im < π := (abs_lt.mp h1).2
      have hs : 0 < Real.sin w.im := Real.sin_pos_of_pos_of_lt_pi hpos hη'
      rw [neg_lt, lt_div_iff₀ hs] at h2
      have hc : 0 < ‖w‖ * Real.sin (arg w + w.im) := by rw [key]; linarith
      have hsa : 0 < Real.sin (arg w + w.im) := by
        by_contra hc'; push Not at hc'; nlinarith
      have : arg w + w.im < π := by
        by_contra hc'; push Not at hc'
        have : 0 ≤ Real.sin (arg w + w.im - π) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        rw [Real.sin_sub_pi] at this; linarith
      exact abs_lt.mpr ⟨by linarith [Real.pi_pos], by linarith⟩

theorem injOn_lambertW (k : ℤ) (s : Set ℂ) : InjOn (lambertW k) s := fun a _ b _ h => by
  rw [← dlmf_4_13_1 k a, ← dlmf_4_13_1 k b, h]

/-- **DLMF Figure 4.13.2** (first sheet): `W₀` maps `|ph(z + e⁻¹)| < π` bijectively onto the
region enclosed by the green curve `ξ = −η cot η`. -/
theorem figure_4_13_2_sheet0 :
    lambertW 0 '' firstSheet = lambertRegion0 ∧ InjOn (lambertW 0) firstSheet := by
  refine ⟨?_, injOn_lambertW 0 _⟩
  rw [firstSheet_eq]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    by_cases hz0 : z = 0
    · rw [hz0, lambertW_zero_arg]; refine ⟨by simp [Real.pi_pos], fun _ => by simp, ?_⟩; simp
    by_cases hzi : z.im = 0
    · have hzr : -Real.exp (-1) < z.re := by
        by_contra h; push Not at h; exact hz ⟨hzi, h⟩
      have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzi])
      rw [hz', lambertW_zero_ofReal hzr.le]
      refine ⟨by simp [Real.pi_pos], fun _ => by simpa using lambertW0_gt hzr, fun h => ?_⟩
      simp at h
    · have hs : z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr hzi)
      set w := lambertW 0 z
      have hθ := lambertW_im_add_arg 0 hs
      simp only [Int.cast_zero, mul_zero, add_zero] at hθ
      have hwi : w.im ≠ 0 := by
        intro h
        have := (mul_exp_im_eq_zero_iff w).mpr (Or.inl h)
        rw [dlmf_4_13_1] at this; exact hzi this
      have harg : |arg z| < π := by
        refine lt_of_le_of_ne (abs_arg_le_pi z) fun e => ?_
        rcases abs_eq Real.pi_pos.le |>.mp e with h | h
        · exact hzi (arg_eq_pi_iff.mp h).2
        · linarith [neg_pi_lt_arg z]
      obtain ⟨h1, h2⟩ := (abs_im_add_arg_lt_pi_iff hwi).mp (by rw [hθ]; exact harg)
      exact ⟨h1, fun h => absurd h hwi, fun _ => h2⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases hwi : w.im = 0
    · have hx := h2 hwi
      have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hwi])
      have hle := neg_exp_neg_one_le_mul_exp w.re
      have hlt : -Real.exp (-1) < w.re * Real.exp w.re := by
        refine lt_of_le_of_ne hle fun e => ?_
        have := eq_neg_one_of_real_mul_exp e.symm; linarith
      refine ⟨((w.re * Real.exp w.re : ℝ) : ℂ), fun ⟨_, h⟩ => ?_, ?_⟩
      · simp only [ofReal_re] at h; linarith
      · rw [lambertW_zero_ofReal hlt.le, dlmf_4_13_3_1 hx.le, ← hw']
    · have hw0 : w ≠ 0 := fun h => hwi (by simp [h])
      have hθ := (abs_im_add_arg_lt_pi_iff hwi).mpr ⟨h1, h3 hwi⟩
      have a : (2 * ((0 : ℤ) : ℝ) - 1) * π < w.im + arg w := by
        push_cast; linarith [(abs_lt.mp hθ).1]
      have b : w.im + arg w < (2 * ((0 : ℤ) : ℝ) + 1) * π := by
        push_cast; linarith [(abs_lt.mp hθ).2]
      exact ⟨w * exp w, slitPlane_subset_cutW0 (mul_exp_mem_slitPlane_of_sheet hw0 0 a b),
        lambertW_mul_exp_of_sheet hw0 0 a b⟩

/-- The image `{w ≠ 0 : (2k − 1)π < ℑw + ph w < (2k + 1)π}` of the `k`-th sheet. -/
def sheetRegion (k : ℤ) : Set ℂ :=
  {w | w ≠ 0 ∧ (2 * k - 1) * π < w.im + arg w ∧ w.im + arg w < (2 * k + 1) * π}

/-- **DLMF Figure 4.13.2** (other sheets): `W_k` maps the sheet `(2k − 1)π < ph z < (2k + 1)π`,
i.e. `ℂ ∖ (−∞, 0]` with `ph z = arg z + 2πk`, bijectively onto `sheetRegion k`, the region
bounded by the curves `ℑw + ph w = (2k ± 1)π` (pieces of `ξ = −η cot η`). -/
theorem figure_4_13_2_sheet (k : ℤ) :
    lambertW k '' slitPlane = sheetRegion k ∧ InjOn (lambertW k) slitPlane := by
  refine ⟨?_, injOn_lambertW k _⟩
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hθ := lambertW_im_add_arg k hz
    obtain ⟨hpi, hz0⟩ := mem_slitPlane_iff_arg.mp hz
    have ha1 := neg_pi_lt_arg z
    have ha2 := lt_of_le_of_ne (arg_le_pi z) hpi
    refine ⟨lambertW_ne_zero k hz0, ?_, ?_⟩ <;> rw [hθ] <;> linarith
  · rintro ⟨hw0, h1, h2⟩
    exact ⟨w * exp w, mul_exp_mem_slitPlane_of_sheet hw0 k h1 h2,
      lambertW_mul_exp_of_sheet hw0 k h1 h2⟩

end Azurite.DLMF
