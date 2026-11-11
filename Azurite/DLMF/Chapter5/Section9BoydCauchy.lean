/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9Boyd
import Azurite.DLMF.Chapter2.Section5Residues
import Azurite.DLMF.Chapter2.Section5LaplaceShift

/-!
# A Cauchy formula for the right half-plane

For `F` holomorphic on `ℜw > 0` with `|F(w)| ≤ C/|w|` for `|w| ≥ 1`, `|F(w)| ≤ C|w|^{−½}` for
`|w| ≤ 1`, and continuous at the points `iy`, `y ≠ 0`, of the imaginary axis (`HalfPlaneDecay`):

* `∫_{−∞}^{∞} F(iy)/(iy − z) dy = −2π F(z)` for `ℜz > 0` (`integral_halfPlane_inside`);
* `∫_{−∞}^{∞} F(iy)/(iy − z) dy = 0` for `ℜz < 0` (`integral_halfPlane_outside`).

Proof: the residue theorem on the rectangles `[δ, T] × [−T, T]` (`rectBoundary_eq_sum_residues`),
`T → ∞` (the other three sides are `O(1/T)`), then `δ → 0+` by dominated convergence with the
majorant `|y|^{−½} 1_{|y|<1} + 2/(1 + y²)` (`halfPlaneDom`).
-/

open Complex Filter Topology Set MeasureTheory Metric
open scoped Real

namespace Azurite.DLMF

/-- Hypotheses for the half-plane Cauchy formula. -/
structure HalfPlaneDecay (F : ℂ → ℂ) (C : ℝ) : Prop where
  pos : 0 < C
  diff : DifferentiableOn ℂ F {w | 0 < w.re}
  far : ∀ w : ℂ, 0 < w.re → 1 ≤ ‖w‖ → ‖F w‖ ≤ C / ‖w‖
  near : ∀ w : ℂ, 0 < w.re → ‖w‖ ≤ 1 → ‖F w‖ ≤ C * ‖w‖ ^ (-(1 / 2 : ℝ))
  cont : ∀ y : ℝ, y ≠ 0 → ContinuousAt F (y * I)

/-- The majorant `|y|^{−½} 1_{|y|<1} + 2/(1 + y²)`. -/
noncomputable def halfPlaneDom (y : ℝ) : ℝ :=
  (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 2 : ℝ))) y + 2 * (1 + y ^ 2)⁻¹

theorem intervalIntegrable_abs_rpow_neg_half :
    IntervalIntegrable (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) volume (-1) 1 := by
  have h1 : IntervalIntegrable (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h1' : IntervalIntegrable (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    refine h1.congr fun y hy => ?_
    rw [uIoc_of_le zero_le_one] at hy
    simp only [abs_of_pos hy.1]
  have h2 : IntervalIntegrable (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) volume (-1) 0 := by
    have := h1'.comp_mul_left (c := -1)
    simp only [neg_mul, one_mul, abs_neg, div_neg, div_one, neg_zero] at this
    exact this.symm
  exact h2.trans h1'

theorem integrable_halfPlaneDom : Integrable halfPlaneDom := by
  refine Integrable.add ?_ (integrable_inv_one_add_sq.const_mul 2)
  rw [integrable_indicator_iff measurableSet_Ioo]
  have := intervalIntegrable_abs_rpow_neg_half
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at this
  exact this.mono_set Ioo_subset_Ioc_self

theorem halfPlaneDom_nonneg (y : ℝ) : 0 ≤ halfPlaneDom y := by
  unfold halfPlaneDom
  have : 0 ≤ (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 2 : ℝ))) y :=
    indicator_nonneg (fun y _ => Real.rpow_nonneg (abs_nonneg y) _) y
  positivity

/-- `|(δ + iy) − z| ≥ c (1 + |y|)` when `|δ − ℜz| ≥ m > 0`. -/
theorem norm_line_sub_ge {z : ℂ} {m δ : ℝ} (hm : 0 < m) (hgap : m ≤ |δ - z.re|) (y : ℝ) :
    m / (1 + |z.im| + m) * (1 + |y|) ≤ ‖(δ : ℂ) + y * I - z‖ := by
  set A := |z.im| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  have h1 : m ≤ ‖(δ : ℂ) + y * I - z‖ := by
    have := Complex.abs_re_le_norm ((δ : ℂ) + y * I - z)
    simp at this
    linarith
  have h2 : |y| - A ≤ ‖(δ : ℂ) + y * I - z‖ := by
    have := Complex.abs_im_le_norm ((δ : ℂ) + y * I - z)
    simp at this
    have := abs_sub_abs_le_abs_sub y z.im
    linarith
  have hd : 0 < 1 + A + m := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  rcases le_or_gt |y| (A + m) with h | h
  · nlinarith [abs_nonneg y]
  · nlinarith [abs_nonneg y]

/-- On `ℜw = δ > 0`: `|F(δ + iy)| ≤ C (|y|^{−½} 1_{|y|<1} + 2/(1 + |y|))`, `y ≠ 0`. -/
theorem norm_F_line_le {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {δ : ℝ} (hδ : 0 < δ)
    {y : ℝ} (hy : y ≠ 0) :
    ‖F ((δ : ℂ) + y * I)‖ ≤ C * ((Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 2 : ℝ))) y +
      2 / (1 + |y|)) := by
  set w : ℂ := (δ : ℂ) + y * I with hw
  have hre : 0 < w.re := by simpa [hw] using hδ
  have hwy : |y| ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w; simpa [hw] using this
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hC := hF.pos
  have hind0 : 0 ≤ (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 2 : ℝ))) y :=
    indicator_nonneg (fun y _ => Real.rpow_nonneg (abs_nonneg y) _) y
  rcases le_or_gt 1 |y| with h1 | h1
  · have hF1 := hF.far w hre (le_trans h1 hwy)
    have : C / ‖w‖ ≤ C * (2 / (1 + |y|)) := by
      rw [div_le_iff₀ (lt_of_lt_of_le hy0 hwy)]
      have : 1 + |y| ≤ 2 * ‖w‖ := by linarith
      calc C = C * (2 / (1 + |y|)) * ((1 + |y|) / 2) := by field_simp
        _ ≤ C * (2 / (1 + |y|)) * ‖w‖ := by gcongr; linarith
    nlinarith
  · have hmem : y ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp h1
    rw [indicator_of_mem hmem]
    have hpow1 : 1 ≤ |y| ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 h1.le (by norm_num)
    have hextra : 0 ≤ C * (2 / (1 + |y|)) := by positivity
    rcases le_or_gt 1 ‖w‖ with h2 | h2
    · have hF1 := hF.far w hre h2
      have : C / ‖w‖ ≤ C := div_le_self hC.le h2
      nlinarith
    · have hF0 := hF.near w hre h2.le
      have : ‖w‖ ^ (-(1 / 2 : ℝ)) ≤ |y| ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hy0 hwy (by norm_num)
      nlinarith

/-- The dominated bound for `F(δ + iy)/(δ + iy − z)`. -/
theorem norm_line_div_le {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {z : ℂ} {m δ : ℝ}
    (hm : 0 < m) (hgap : m ≤ |δ - z.re|) (hδ : 0 < δ) {y : ℝ} (hy : y ≠ 0) :
    ‖F ((δ : ℂ) + y * I) / ((δ : ℂ) + y * I - z)‖ ≤
      C / (m / (1 + |z.im| + m)) * halfPlaneDom y := by
  set c := m / (1 + |z.im| + m) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hd := norm_line_sub_ge hm hgap y
  have hF1 := norm_F_line_le hF hδ hy
  have hpos : 0 < ‖(δ : ℂ) + y * I - z‖ := lt_of_lt_of_le (by positivity) hd
  set ind := (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 2 : ℝ))) y with hind
  have hind0 : 0 ≤ ind := indicator_nonneg (fun y _ => Real.rpow_nonneg (abs_nonneg y) _) y
  rw [norm_div, div_le_iff₀ hpos]
  have hC := hF.pos
  have key : C * (ind + 2 / (1 + |y|)) ≤ C / c * halfPlaneDom y * (c * (1 + |y|)) := by
    have e : C / c * halfPlaneDom y * (c * (1 + |y|)) = C * (halfPlaneDom y * (1 + |y|)) := by
      field_simp
    rw [e]
    gcongr
    unfold halfPlaneDom
    rw [← hind]
    have h1 : ind ≤ ind * (1 + |y|) := le_mul_of_one_le_right hind0 (by linarith [abs_nonneg y])
    have h2 : 2 / (1 + |y|) ≤ 2 * (1 + y ^ 2)⁻¹ * (1 + |y|) := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 + y ^ 2) ≤ (1 + |y|) * (1 + |y|) := by nlinarith [sq_abs y, abs_nonneg y]
      calc (2 : ℝ) = 2 * (1 + y ^ 2)⁻¹ * (1 + y ^ 2) := by field_simp
        _ ≤ 2 * (1 + y ^ 2)⁻¹ * ((1 + |y|) * (1 + |y|)) := by gcongr
        _ = _ := by ring
    nlinarith
  calc ‖F ((δ : ℂ) + y * I)‖ ≤ C * (ind + 2 / (1 + |y|)) := hF1
    _ ≤ C / c * halfPlaneDom y * (c * (1 + |y|)) := key
    _ ≤ C / c * halfPlaneDom y * ‖(δ : ℂ) + y * I - z‖ := by
        gcongr
        exact mul_nonneg (div_nonneg hC.le hc0.le) (halfPlaneDom_nonneg y)

theorem integrable_line_div {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : z.re ≠ δ) :
    Integrable fun y : ℝ => F ((δ : ℂ) + y * I) / ((δ : ℂ) + y * I - z) := by
  have hm : 0 < |δ - z.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hz))
  refine (integrable_halfPlaneDom.const_mul
    (C / (|δ - z.re| / (1 + |z.im| + |δ - z.re|)))).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y => ?_)
    have hre : 0 < ((δ : ℂ) + y * I).re := by simpa using hδ
    have hne : (δ : ℂ) + y * I - z ≠ 0 := fun h => by
      have := congrArg re h; simp at this; exact hz (by linarith)
    have hc : ContinuousAt (fun y : ℝ => (δ : ℂ) + y * I) y := by fun_prop
    have hFc : ContinuousAt F ((δ : ℂ) + y * I) :=
      (hF.diff.differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds hre)).continuousAt
    have h1 : ContinuousAt (fun y : ℝ => F ((δ : ℂ) + y * I)) y :=
      ContinuousAt.comp (f := fun y : ℝ => (δ : ℂ) + y * I) hFc hc
    exact h1.div (hc.sub continuousAt_const) hne
  · filter_upwards [(measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0) |>
      measure_eq_zero_iff_ae_notMem.mp] with y hy
    exact norm_line_div_le hF hm le_rfl hδ (by simpa using hy)

/-! ### The line `ℜw = δ` -/

theorem norm_far_le {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {z w : ℂ} (hw : 0 < w.re)
    {T : ℝ} (hT : 2 * ‖z‖ + 1 ≤ T) (hwT : T ≤ ‖w‖) : ‖F w / (w - z)‖ ≤ 2 * C / T ^ 2 := by
  have hC := hF.pos
  have hT0 : 0 < T := by linarith [norm_nonneg z]
  have h1 := hF.far w hw (by linarith [norm_nonneg z])
  have h2 : T / 2 ≤ ‖w - z‖ := by
    have := norm_sub_norm_le w z
    linarith [norm_nonneg z]
  have h3 : C / ‖w‖ ≤ C / T := div_le_div_of_nonneg_left hC.le hT0 hwT
  rw [norm_div, div_le_iff₀ (by linarith)]
  calc ‖F w‖ ≤ C / T := h1.trans h3
    _ = 2 * C / T ^ 2 * (T / 2) := by field_simp
    _ ≤ 2 * C / T ^ 2 * ‖w - z‖ := by gcongr

/-- For `δ > 0` and `ℜz ≠ δ`: `∫ F(δ + iy)/(δ + iy − z) dy` is `−2πF(z)` if `ℜz > δ`, else `0`. -/
theorem integral_line_eq {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {δ : ℝ} (hδ : 0 < δ)
    {z : ℂ} (hz : z.re ≠ δ) :
    ∫ y : ℝ, F ((δ : ℂ) + y * I) / ((δ : ℂ) + y * I - z) =
      if δ < z.re then -(2 * π * F z) else 0 := by
  have hC := hF.pos
  set f : ℂ → ℂ := fun w => F w / (w - z) with hf
  set T₀ : ℝ := δ + 2 * ‖z‖ + 1 with hT₀
  have hzim : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hzre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  -- the rectangle identity
  have hrect : ∀ T : ℝ, T₀ < T → rectBoundary f ⟨δ, -T⟩ ⟨T, T⟩ =
      if δ < z.re then 2 * π * I * F z else 0 := by
    intro T hT
    have hδT : δ < T := by linarith [norm_nonneg z]
    split_ifs with hin
    · have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
      have hres := rectBoundary_eq_sum_residues (p := ⟨δ, -T⟩) (q := ⟨T, T⟩) hδT
        (by show -T < T; linarith) hU (fun w hw => lt_of_lt_of_le hδ hw.1.1) (S := {z})
        (fun s hs => by
          obtain rfl : s = z := by simpa using hs
          refine ⟨hin, ?_, ?_, ?_⟩
          · show s.re < T; linarith [abs_le.mp hzre]
          · show -T < s.im; linarith [abs_le.mp hzim]
          · show s.im < T; linarith [abs_le.mp hzim])
        (f := f) (by
          intro w hw
          have hw1 : 0 < w.re := hw.1
          have hw2 : w ≠ z := fun h => hw.2 (by simp [h])
          exact ((hF.diff.differentiableAt (hU.mem_nhds hw1)).div (differentiableAt_id.sub_const z)
            (sub_ne_zero.mpr hw2)).differentiableWithinAt)
        (fun _ => z.re) (fun s hs => by
          obtain rfl : s = z := by simpa using hs
          refine ⟨lt_trans hδ hin, fun w hw => ?_, fun t ht h => ?_⟩
          · rw [mem_ball, dist_eq_norm] at hw
            have := Complex.abs_re_le_norm (w - s)
            simp only [sub_re] at this
            show 0 < w.re
            linarith [abs_le.mp this]
          · exact absurd (by simpa using ht) h)
      rw [hres, Finset.sum_singleton]
      congr 1
      refine residue_eq_of_eq_div_add (A := F) (g := fun _ => 0) (lt_trans hδ hin) ?_
        (differentiableOn_const 0) fun w _ => by simp [hf]
      refine hF.diff.mono fun w hw => ?_
      rw [mem_ball, dist_eq_norm] at hw
      have := Complex.abs_re_le_norm (w - z)
      simp only [sub_re] at this
      show 0 < w.re
      linarith [abs_le.mp this]
    · have hzδ : z.re < δ := lt_of_le_of_ne (not_lt.mp hin) hz
      set U : Set ℂ := {w : ℂ | (δ + z.re) / 2 < w.re} ∩ {w : ℂ | 0 < w.re} with hUdef
      have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_const continuous_re)
      have hres := rectBoundary_eq_sum_residues (p := ⟨δ, -T⟩) (q := ⟨T, T⟩) hδT
        (by show -T < T; linarith) hU (fun w hw => ⟨by
          show (δ + z.re) / 2 < w.re; linarith [hw.1.1], lt_of_lt_of_le hδ hw.1.1⟩)
        (S := ∅) (fun s hs => absurd hs (Finset.notMem_empty s)) (f := f) (by
          intro w hw
          have hw1 : 0 < w.re := hw.1.2
          have hw2 : w - z ≠ 0 := fun h => by
            have := congrArg re h; simp at this; have := hw.1.1; simp at this; linarith
          exact ((hF.diff.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds
            hw1)).div (differentiableAt_id.sub_const z) hw2).differentiableWithinAt)
        (fun _ => 1) (fun s hs => absurd hs (Finset.notMem_empty s))
      rw [hres, Finset.sum_empty, mul_zero]
  -- the limits of the sides
  have hfar : ∀ T : ℝ, T₀ ≤ T → ∀ w : ℂ, δ ≤ w.re → T ≤ ‖w‖ → ‖f w‖ ≤ 2 * C / T ^ 2 :=
    fun T hT w hw hwT => norm_far_le hF (lt_of_lt_of_le hδ hw) (by linarith) hwT
  have hlim0 : ∀ k : ℝ, 0 ≤ k → Tendsto (fun T : ℝ => k * C / T) atTop (𝓝 0) := fun k _ =>
    tendsto_const_nhds.div_atTop tendsto_id
  have hbot : Tendsto (fun T : ℝ => ∫ σ in δ..T, f (σ - T * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hlim0 2 (by norm_num))
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hT0 : 0 < T := by linarith [norm_nonneg z]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * C / T ^ 2)
      fun σ hσ => ?_).trans ?_
    · have hδT : δ ≤ T := by linarith [norm_nonneg z]
      rw [uIoc_of_le hδT] at hσ
      refine hfar T hT _ (by simp; linarith [hσ.1]) ?_
      have := Complex.abs_im_le_norm ((σ : ℂ) - T * I)
      simp at this
      rwa [abs_of_pos hT0] at this
    · rw [abs_of_nonneg (by linarith [norm_nonneg z])]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hT0]
      have : 0 ≤ 2 * C * T * δ := by positivity
      nlinarith
  have htop : Tendsto (fun T : ℝ => ∫ σ in δ..T, f (σ + T * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hlim0 2 (by norm_num))
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hT0 : 0 < T := by linarith [norm_nonneg z]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * C / T ^ 2)
      fun σ hσ => ?_).trans ?_
    · have hδT : δ ≤ T := by linarith [norm_nonneg z]
      rw [uIoc_of_le hδT] at hσ
      refine hfar T hT _ (by simp; linarith [hσ.1]) ?_
      have := Complex.abs_im_le_norm ((σ : ℂ) + T * I)
      simp at this
      rwa [abs_of_pos hT0] at this
    · rw [abs_of_nonneg (by linarith [norm_nonneg z])]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hT0]
      have : 0 ≤ 2 * C * T * δ := by positivity
      nlinarith
  have hright : Tendsto (fun T : ℝ => ∫ y in (-T)..T, f (T + y * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hlim0 4 (by norm_num))
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hT0 : 0 < T := by linarith [norm_nonneg z]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * C / T ^ 2)
      fun y _ => ?_).trans ?_
    · refine hfar T hT _ (by simp; linarith [norm_nonneg z]) ?_
      have := Complex.abs_re_le_norm ((T : ℂ) + y * I)
      simp at this
      rwa [abs_of_pos hT0] at this
    · rw [show T - -T = 2 * T by ring, abs_of_pos (by positivity)]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hT0]
      nlinarith
  set L := ∫ y : ℝ, F ((δ : ℂ) + y * I) / ((δ : ℂ) + y * I - z) with hL
  have hleft : Tendsto (fun T : ℝ => ∫ y in (-T)..T, f (δ + y * I)) atTop (𝓝 L) :=
    intervalIntegral_tendsto_integral (integrable_line_div hF hδ hz) tendsto_neg_atTop_atBot
      tendsto_id
  have h1 : Tendsto (fun T : ℝ => rectBoundary f ⟨δ, -T⟩ ⟨T, T⟩) atTop
      (𝓝 (if δ < z.re then 2 * π * I * F z else 0)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop T₀] with T hT
    exact (hrect T hT).symm
  have h2 : Tendsto (fun T : ℝ => rectBoundary f ⟨δ, -T⟩ ⟨T, T⟩) atTop
      (𝓝 (0 - 0 + I * 0 - I * L)) := by
    have := ((hbot.sub htop).add (hright.const_mul I)).sub (hleft.const_mul I)
    refine this.congr' (Eventually.of_forall fun T => ?_)
    show _ = rectBoundary f ⟨δ, -T⟩ ⟨T, T⟩
    rw [rectBoundary_strip]
  have hkey := tendsto_nhds_unique h1 h2
  have hI : I ≠ 0 := I_ne_zero
  split_ifs at hkey ⊢ with hin
  · have : I * L = I * (-(2 * π * F z)) := by linear_combination hkey
    exact mul_left_cancel₀ hI this
  · have : I * L = I * 0 := by linear_combination hkey
    exact mul_left_cancel₀ hI this

/-! ### `δ → 0` -/

theorem tendsto_line_point {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {z : ℂ} (hz : z.re ≠ 0)
    {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun δ : ℝ => F ((δ : ℂ) + y * I) / ((δ : ℂ) + y * I - z)) (𝓝[>] 0)
      (𝓝 (F (y * I) / (y * I - z))) := by
  have hc : Continuous fun δ : ℝ => (δ : ℂ) + y * I := by fun_prop
  have h0 : ((0 : ℝ) : ℂ) + y * I = y * I := by simp
  have hne : (y : ℂ) * I - z ≠ 0 := fun h => by
    have := congrArg re h; simp at this; exact hz (by linarith)
  have h1 : Tendsto (fun δ : ℝ => (δ : ℂ) + y * I) (𝓝 0) (𝓝 (y * I)) := by
    have := hc.tendsto 0; rwa [h0] at this
  have h2 := ((hF.cont y hy).tendsto.comp h1).div (h1.sub tendsto_const_nhds) hne
  exact h2.mono_left nhdsWithin_le_nhds

theorem eventually_line_bound {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {z : ℂ}
    (hz : z.re ≠ 0) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ y : ℝ, ‖F ((δ : ℂ) + y * I) / ((δ : ℂ) + y * I - z)‖ ≤
      C / ((|z.re| / 2) / (1 + |z.im| + |z.re| / 2)) * halfPlaneDom y := by
  have hm : 0 < |z.re| / 2 := by have := abs_pos.mpr hz; positivity
  filter_upwards [Ioo_mem_nhdsGT hm] with δ hδ
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℝ))] with y hy
  refine norm_line_div_le hF hm ?_ hδ.1 (by simpa using hy)
  rcases lt_or_gt_of_ne hz with h | h
  · rw [abs_of_neg h] at hδ ⊢
    rw [abs_of_pos (by linarith [hδ.1])]
    linarith [hδ.1]
  · rw [abs_of_pos h] at hδ ⊢
    rw [abs_of_neg (by linarith [hδ.2])]
    linarith [hδ.2]

theorem tendsto_integral_line {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {z : ℂ}
    (hz : z.re ≠ 0) :
    Tendsto (fun δ : ℝ => ∫ y : ℝ, F ((δ : ℂ) + y * I) / ((δ : ℂ) + y * I - z)) (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, F (y * I) / (y * I - z))) := by
  have hm : 0 < |z.re| / 2 := by have := abs_pos.mpr hz; positivity
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => C / ((|z.re| / 2) / (1 + |z.im| + |z.re| / 2)) * halfPlaneDom y) ?_
    (eventually_line_bound hF hz) (integrable_halfPlaneDom.const_mul _) ?_
  · filter_upwards [Ioo_mem_nhdsGT hm] with δ hδ
    refine (integrable_line_div hF hδ.1 fun h => ?_).aestronglyMeasurable
    rcases lt_or_gt_of_ne hz with h' | h'
    · linarith [hδ.1]
    · rw [abs_of_pos h'] at hδ; linarith [hδ.2]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℝ))] with y hy
    exact tendsto_line_point hF hz (by simpa using hy)

theorem integrable_halfPlane {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {z : ℂ}
    (hz : z.re ≠ 0) : Integrable fun y : ℝ => F (y * I) / (y * I - z) := by
  have hm : 0 < |z.re| / 2 := by have := abs_pos.mpr hz; positivity
  set K := C / ((|z.re| / 2) / (1 + |z.im| + |z.re| / 2))
  set d : ℕ → ℝ := fun n => (|z.re| / 2) / ((n : ℝ) + 2) with hd
  have hd0 : ∀ n, 0 < d n := fun n => by rw [hd]; positivity
  have hdlt : ∀ n, d n < |z.re| / 2 := fun n => by
    rw [hd, div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hdne : ∀ n, z.re ≠ d n := fun n h => by
    have h1 := hdlt n
    rw [← h] at h1
    rcases lt_or_gt_of_ne hz with h' | h'
    · rw [abs_of_neg h'] at h1; linarith [hd0 n, h]
    · rw [abs_of_pos h'] at h1; linarith
  have hdlim : Tendsto d atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hd0⟩
    have : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop this
  have hf : ∀ n : ℕ, AEStronglyMeasurable (fun y : ℝ =>
      F ((d n : ℂ) + y * I) / ((d n : ℂ) + y * I - z)) volume := fun n =>
    (integrable_line_div hF (hd0 n) (hdne n)).aestronglyMeasurable
  have hlim : ∀ᵐ y : ℝ, Tendsto (fun n : ℕ => F ((d n : ℂ) + y * I) / ((d n : ℂ) + y * I - z))
      atTop (𝓝 (F (y * I) / (y * I - z))) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℝ))] with y hy
    exact (tendsto_line_point hF hz (by simpa using hy)).comp hdlim
  have hmeas : AEStronglyMeasurable (fun y : ℝ => F (y * I) / (y * I - z)) volume :=
    aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun (n : ℕ) (y : ℝ) => F ((d n : ℂ) + y * I) / ((d n : ℂ) + y * I - z))
      (g := fun y : ℝ => F (y * I) / (y * I - z)) hf hlim
  refine (integrable_halfPlaneDom.const_mul K).mono' hmeas ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℝ))] with y hy
  have hy0 : y ≠ 0 := by simpa using hy
  have hlim := (tendsto_line_point hF hz hy0).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hm] with δ hδ
  refine norm_line_div_le hF hm ?_ hδ.1 hy0
  rcases lt_or_gt_of_ne hz with h | h
  · rw [abs_of_neg h] at hδ ⊢
    rw [abs_of_pos (by linarith [hδ.1])]
    linarith [hδ.1]
  · rw [abs_of_pos h] at hδ ⊢
    rw [abs_of_neg (by linarith [hδ.2])]
    linarith [hδ.2]

/-- **Cauchy's formula on the right half-plane**: `∫ F(iy)/(iy − z) dy = −2πF(z)`, `ℜz > 0`. -/
theorem integral_halfPlane_inside {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {z : ℂ}
    (hz : 0 < z.re) : ∫ y : ℝ, F (y * I) / (y * I - z) = -(2 * π * F z) := by
  refine tendsto_nhds_unique (tendsto_integral_line hF hz.ne') (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hz] with δ hδ
  rw [integral_line_eq hF hδ.1 (ne_of_gt hδ.2), ite_eq_left_iff.mpr (fun h => absurd hδ.2 h)]

/-- `∫ F(iy)/(iy − z) dy = 0` for `ℜz < 0`. -/
theorem integral_halfPlane_outside {F : ℂ → ℂ} {C : ℝ} (hF : HalfPlaneDecay F C) {z : ℂ}
    (hz : z.re < 0) : ∫ y : ℝ, F (y * I) / (y * I - z) = 0 := by
  refine tendsto_nhds_unique (tendsto_integral_line hF hz.ne) (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  rw [integral_line_eq hF hδ (by linarith), ite_eq_right_iff.mpr (fun h => absurd h (by linarith))]

end Azurite.DLMF
