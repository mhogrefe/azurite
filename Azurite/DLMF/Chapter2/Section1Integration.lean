/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DLMF §2.1(ii): integration of asymptotic relations

* `isLittleO_integral_Ioi` (tails of convergent integrals) and `isLittleO_intervalIntegral`
  (divergent integrals): integration of `o`-relations.
* `dlmf_2_1_11`: `f ∼ x^ν`, `ℜν < −1` ⇒ `∫_x^∞ f ∼ −x^{ν+1}/(ν+1)`.
* 2.1.12: `dlmf_2_1_12_const` (`ℜν < −1`: `∫_a^x f` tends to a constant, `∼` it when nonzero),
  `dlmf_2_1_12_log` (`ν = −1`: `∼ ln x`), `dlmf_2_1_12_pow` (`ℜν > −1`: `∼ x^{ν+1}/(ν+1)`).
  `f` is complex valued and continuous on `[a, ∞)`, `a > 0`.
-/

open Set Filter Topology Asymptotics MeasureTheory

namespace Azurite.DLMF

/-! ### Integrating `o`-relations -/

/-- Tails: if `h = o(w)` with `w ≥ 0` integrable, then `∫_x^∞ h = o(∫_x^∞ w)` as `x → +∞`. -/
theorem isLittleO_integral_Ioi {h : ℝ → ℂ} {w : ℝ → ℝ} {a : ℝ} (hw : ∀ t, a < t → 0 ≤ w t)
    (hwi : IntegrableOn w (Ioi a)) (hhi : IntegrableOn h (Ioi a)) (hhw : h =o[atTop] w) :
    (fun x => ∫ t in Ioi x, h t) =o[atTop] fun x => ∫ t in Ioi x, w t := by
  refine IsLittleO.of_bound fun c hc => ?_
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hhw.bound hc).and (eventually_gt_atTop a))
  filter_upwards [eventually_ge_atTop (max T a)] with x hx
  have hxa : a ≤ x := (le_max_right _ _).trans hx
  have hsub : Ioi x ⊆ Ioi a := Ioi_subset_Ioi hxa
  rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Ioi fun t ht =>
    hw t (hxa.trans_lt ht))]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine setIntegral_mono_on (hhi.mono_set hsub).norm ((hwi.mono_set hsub).const_mul c)
    measurableSet_Ioi fun t ht => ?_
  have ht' := hT t ((le_max_left _ _).trans (hx.trans ht.le))
  rw [Real.norm_of_nonneg (hw t ht'.2)] at ht'
  exact ht'.1

/-- Divergent integrals: if `h = o(w)` with `w ≥ 0` and `∫_a^x w → ∞`, then
`∫_a^x h = o(∫_a^x w)` as `x → +∞`. -/
theorem isLittleO_intervalIntegral {h : ℝ → ℂ} {w : ℝ → ℝ} {a : ℝ}
    (hw : ∀ t, a ≤ t → 0 ≤ w t) (hwi : ∀ x, a ≤ x → IntervalIntegrable w volume a x)
    (hhi : ∀ x, a ≤ x → IntervalIntegrable h volume a x)
    (hW : Tendsto (fun x => ∫ t in a..x, w t) atTop atTop) (hhw : h =o[atTop] w) :
    (fun x => ∫ t in a..x, h t) =o[atTop] fun x => ∫ t in a..x, w t := by
  refine IsLittleO.of_bound fun c hc => ?_
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hhw.bound (half_pos hc)).and (eventually_ge_atTop a))
  set C := ‖∫ t in a..T, h t‖
  have hTa : a ≤ T := (hT T le_rfl).2
  filter_upwards [eventually_ge_atTop T, hW.eventually_ge_atTop (2 / c * C)] with x hx hWx
  have hTx : ∀ t ∈ Icc T x, ‖h t‖ ≤ c / 2 * w t := fun t ht => by
    have := (hT t ht.1).1
    rwa [Real.norm_of_nonneg (hw t ((hT t ht.1).2))] at this
  have hwnn : 0 ≤ ∫ t in a..x, w t :=
    intervalIntegral.integral_nonneg (hTa.trans hx) fun t ht => hw t ht.1
  have hwaT : 0 ≤ ∫ t in a..T, w t :=
    intervalIntegral.integral_nonneg hTa fun t ht => hw t ht.1
  have hax : a ≤ x := hTa.trans hx
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hhi T hTa)
    ((hhi T hTa).symm.trans (hhi x hax))
  have hsplitw := intervalIntegral.integral_add_adjacent_intervals (hwi T hTa)
    ((hwi T hTa).symm.trans (hwi x hax))
  have hTx' : ‖∫ t in T..x, h t‖ ≤ c / 2 * ∫ t in T..x, w t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.norm_integral_le_of_norm_le hx
      (ae_of_all _ fun t ht => hTx t ⟨ht.1.le, ht.2⟩)
      (((hwi T hTa).symm.trans (hwi x hax)).const_mul _)
  rw [Real.norm_of_nonneg hwnn, ← hsplit]
  have hC : C ≤ c / 2 * ∫ t in a..x, w t := by
    have := hWx
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at this
    linarith
  calc ‖(∫ t in a..T, h t) + ∫ t in T..x, h t‖ ≤ C + ‖∫ t in T..x, h t‖ := norm_add_le _ _
    _ ≤ (c / 2 * ∫ t in a..x, w t) + c / 2 * ∫ t in T..x, w t := add_le_add hC hTx'
    _ ≤ c * ∫ t in a..x, w t := by
      have hB : (∫ t in T..x, w t) ≤ ∫ t in a..x, w t := by rw [← hsplitw]; linarith
      nlinarith

/-! ### Powers -/

theorem norm_ofReal_cpow {x : ℝ} (hx : 0 < x) (ν : ℂ) : ‖(x : ℂ) ^ ν‖ = x ^ ν.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx ν

theorem ofReal_cpow_ne_zero {x : ℝ} (hx : 0 < x) (ν : ℂ) : (x : ℂ) ^ ν ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_ofReal_cpow hx]; exact (Real.rpow_pos_of_pos hx _).ne'

theorem continuousOn_ofReal_cpow (ν : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ) ^ ν) (Ioi 0) :=
  fun x hx => (Complex.continuousAt_ofReal_cpow_const x ν (Or.inr hx.ne')).continuousWithinAt

/-- If `f ∼ g` along `atTop`, `f` is continuous on `[a, ∞)` and `g` is integrable on `(a, ∞)`,
then `f` is integrable on `(a, ∞)`. -/
theorem integrableOn_Ioi_of_isEquivalent {f g : ℝ → ℂ} {a : ℝ} (hf : ContinuousOn f (Ici a))
    (hg : IntegrableOn g (Ioi a)) (hfg : f ~[atTop] g) : IntegrableOn f (Ioi a) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hfg.isLittleO.bound one_pos).and (eventually_ge_atTop a))
  have hTa : a ≤ T := (hT T le_rfl).2
  rw [← Ioc_union_Ioi_eq_Ioi hTa]
  refine (((hf.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set
    Ioc_subset_Icc_self).union ?_
  refine Integrable.mono' ((hg.mono_set (Ioi_subset_Ioi hTa)).norm.const_mul 2)
    ((hf.mono fun t ht => hTa.trans (le_of_lt ht)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have := (hT t (le_of_lt ht)).1
  rw [one_mul] at this
  calc ‖f t‖ = ‖(f t - g t) + g t‖ := by ring_nf
    _ ≤ ‖f t - g t‖ + ‖g t‖ := norm_add_le _ _
    _ ≤ 2 * ‖g t‖ := by simp only [Pi.sub_apply] at this; linarith

/-- **DLMF 2.1.11**: if `f` is continuous and `f(x) ∼ x^ν` as `x → +∞` with `ℜν < −1`, then
`∫_x^∞ f(t) dt ∼ −x^{ν+1}/(ν+1)`. -/
theorem dlmf_2_1_11 {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hf : ContinuousOn f (Ici a)) {ν : ℂ}
    (hν : ν.re < -1) (h : AsympEqDLMF atTop f fun x => (x : ℂ) ^ ν) :
    AsympEqDLMF atTop (fun x => ∫ t in Ioi x, f t) fun x => -(x : ℂ) ^ (ν + 1) / (ν + 1) := by
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ ν
  set w : ℝ → ℝ := fun x => x ^ ν.re
  set T : ℝ → ℂ := fun x => -(x : ℂ) ^ (ν + 1) / (ν + 1)
  have hν1 : ν + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hT0 : ∀ᶠ x in atTop, T x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_ne_zero (neg_ne_zero.mpr (ofReal_cpow_ne_zero hx _)) hν1
  rw [dlmf_2_1_1 hT0]
  have hg0 : ∀ᶠ x in atTop, g x ≠ 0 :=
    (eventually_gt_atTop 0).mono fun x hx => ofReal_cpow_ne_zero hx ν
  have hfg : f ~[atTop] g := (dlmf_2_1_1 hg0).mp h
  have hgi : IntegrableOn g (Ioi a) := integrableOn_Ioi_cpow_of_lt hν ha
  have hwi : IntegrableOn w (Ioi a) := integrableOn_Ioi_rpow_of_lt hν ha
  have hfi := integrableOn_Ioi_of_isEquivalent hf hgi hfg
  have hgw : g =O[atTop] w := IsBigO.of_bound 1 (by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_ofReal_cpow hx, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _), one_mul])
  have hL := isLittleO_integral_Ioi (fun t ht => Real.rpow_nonneg (ha.trans ht).le _) hwi
    (hfi.sub hgi) (hfg.isLittleO.trans_isBigO hgw)
  have hwT : (fun x => ∫ t in Ioi x, w t) =O[atTop] T := by
    refine IsBigO.of_bound (‖ν + 1‖ / -(ν.re + 1)) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hnT : ‖T x‖ = x ^ (ν.re + 1) / ‖ν + 1‖ := by
      simp only [T, norm_div, norm_neg, norm_ofReal_cpow hx, Complex.add_re, Complex.one_re]
    rw [integral_Ioi_rpow_of_lt hν hx, hnT, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (Real.rpow_pos_of_pos hx _), abs_of_neg (by linarith)]
    have hn : 0 < ‖ν + 1‖ := norm_pos_iff.mpr hν1
    field_simp
    rfl
  refine (hL.trans_isBigO hwT).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop a] with x hx
  have hsub : Ioi x ⊆ Ioi a := Ioi_subset_Ioi hx.le
  show ∫ t in Ioi x, (f t - g t) = (∫ t in Ioi x, f t) - T x
  rw [integral_sub (hfi.mono_set hsub) (hgi.mono_set hsub),
    integral_Ioi_cpow_of_lt hν (ha.trans hx)]

/-- Common step of 2.1.12: if `f ∼ x^ν` then `∫_a^x f − ∫_a^x t^ν = o(∫_a^x t^{ℜν})` whenever the
latter integral diverges. -/
theorem intervalIntegral_sub_isLittleO {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hf : ContinuousOn f (Ici a)) {ν : ℂ} (hfg : f ~[atTop] fun x => (x : ℂ) ^ ν)
    (hW : Tendsto (fun x => ∫ t in a..x, t ^ ν.re) atTop atTop) :
    (fun x => (∫ t in a..x, f t) - ∫ t in a..x, (t : ℂ) ^ ν) =o[atTop]
      fun x => ∫ t in a..x, t ^ ν.re := by
  have hI : ∀ x, a ≤ x → Icc a x ⊆ Ioi 0 := fun x _ t ht => ha.trans_le ht.1
  have hgc : ∀ x, a ≤ x → IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ ν) volume a x :=
    fun x hx => ((continuousOn_ofReal_cpow ν).mono (hI x hx)).intervalIntegrable_of_Icc hx
  have hfc : ∀ x, a ≤ x → IntervalIntegrable f volume a x := fun x hx =>
    (hf.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hx
  have hwc : ∀ x, a ≤ x → IntervalIntegrable (fun t : ℝ => t ^ ν.re) volume a x := fun x hx =>
    (ContinuousOn.rpow_const continuousOn_id fun t ht =>
      Or.inl (hI x hx ht).ne').intervalIntegrable_of_Icc hx
  have hgw : (fun x : ℝ => (x : ℂ) ^ ν) =O[atTop] fun x => x ^ ν.re := IsBigO.of_bound 1 (by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_ofReal_cpow hx, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _), one_mul])
  have hL := isLittleO_intervalIntegral (fun t ht => Real.rpow_nonneg (ha.trans_le ht).le _) hwc
    (fun x hx => (hfc x hx).sub (hgc x hx)) hW (hfg.isLittleO.trans_isBigO hgw)
  refine hL.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop a] with x hx
  exact intervalIntegral.integral_sub (hfc x hx) (hgc x hx)

/-- **DLMF 2.1.12**, `ℜν < −1`: `∫_a^x f` tends to a constant `L`, and `∫_a^x f ∼ L` when
`L ≠ 0`. -/
theorem dlmf_2_1_12_const {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hf : ContinuousOn f (Ici a))
    {ν : ℂ} (hν : ν.re < -1) (h : AsympEqDLMF atTop f fun x => (x : ℂ) ^ ν) :
    ∃ L : ℂ, Tendsto (fun x => ∫ t in a..x, f t) atTop (𝓝 L) ∧
      (L ≠ 0 → AsympEqDLMF atTop (fun x => ∫ t in a..x, f t) fun _ => L) := by
  have hg0 : ∀ᶠ x : ℝ in atTop, (x : ℂ) ^ ν ≠ 0 :=
    (eventually_gt_atTop 0).mono fun x hx => ofReal_cpow_ne_zero hx ν
  have hfi := integrableOn_Ioi_of_isEquivalent hf (integrableOn_Ioi_cpow_of_lt hν ha)
    ((dlmf_2_1_1 hg0).mp h)
  have hT := intervalIntegral_tendsto_integral_Ioi a hfi tendsto_id
  refine ⟨_, hT, fun hL => ?_⟩
  have := hT.div_const (∫ t in Ioi a, f t)
  rwa [div_self hL] at this

/-- **DLMF 2.1.12**, `ν = −1`: `∫_a^x f ∼ ln x`. -/
theorem dlmf_2_1_12_log {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hf : ContinuousOn f (Ici a))
    (h : AsympEqDLMF atTop f fun x => (x : ℂ) ^ (-1 : ℂ)) :
    AsympEqDLMF atTop (fun x => ∫ t in a..x, f t) fun x => (Real.log x : ℂ) := by
  have hg0 : ∀ᶠ x : ℝ in atTop, (x : ℂ) ^ (-1 : ℂ) ≠ 0 :=
    (eventually_gt_atTop 0).mono fun x hx => ofReal_cpow_ne_zero hx _
  have hfg := (dlmf_2_1_1 hg0).mp h
  have hwlog : ∀ x, a ≤ x → ∫ t in a..x, t ^ (-1 : ℂ).re = Real.log x - Real.log a :=
    fun x hx => by
      have hpos : ∀ t ∈ uIcc a x, 0 < t := fun t ht => by
        rw [uIcc_of_le hx] at ht; exact ha.trans_le ht.1
      rw [intervalIntegral.integral_congr (g := fun t => t⁻¹) fun t ht => by
        simp [Real.rpow_neg_one], integral_inv_of_pos ha (ha.trans_le hx),
        Real.log_div (ha.trans_le hx).ne' ha.ne']
  have hglog : ∀ x, a ≤ x → ∫ t in a..x, (t : ℂ) ^ (-1 : ℂ) =
      ((Real.log x - Real.log a : ℝ) : ℂ) := fun x hx => by
    rw [← hwlog x hx, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    simp [Complex.cpow_neg_one, Real.rpow_neg_one, Complex.ofReal_inv]
  have hlog := Real.tendsto_log_atTop
  have hW : Tendsto (fun x => ∫ t in a..x, t ^ (-1 : ℂ).re) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-Real.log a) hlog).congr' (by
      filter_upwards [eventually_ge_atTop a] with x hx
      rw [hwlog x hx]; ring)
  have hL := intervalIntegral_sub_isLittleO ha hf hfg hW
  set G : ℝ → ℂ := fun x => (Real.log x : ℂ)
  have hG0 : ∀ᶠ x in atTop, G x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos hx).ne'
  rw [dlmf_2_1_1 hG0]
  have hGn : Tendsto (fun x => ‖G x‖) atTop atTop :=
    hlog.congr' (by
      filter_upwards [eventually_gt_atTop 1] with x hx
      simp [G, Complex.norm_real, abs_of_pos (Real.log_pos hx)])
  have hwG : (fun x => ∫ t in a..x, t ^ (-1 : ℂ).re) =O[atTop] G := IsBigO.of_bound 2 (by
    filter_upwards [eventually_ge_atTop a, eventually_gt_atTop 1,
      hlog.eventually_ge_atTop (2 * |Real.log a|)] with x hx hx1 hxl
    rw [hwlog x hx, Real.norm_eq_abs]
    simp only [G, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (Real.log_pos hx1)]
    have := abs_sub (Real.log x) (Real.log a)
    rw [abs_of_pos (Real.log_pos hx1)] at this
    linarith [Real.log_pos hx1, abs_nonneg (Real.log a)])
  have hc : (fun _ : ℝ => ((Real.log a : ℝ) : ℂ)) =o[atTop] G :=
    isLittleO_const_left.mpr (Or.inr hGn)
  refine ((hL.trans_isBigO hwG).sub hc).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop a] with x hx
  simp only [Pi.sub_apply, hglog x hx, G]
  push_cast; ring

/-- **DLMF 2.1.12**, `ℜν > −1`: `∫_a^x f ∼ x^{ν+1}/(ν+1)`. -/
theorem dlmf_2_1_12_pow {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hf : ContinuousOn f (Ici a))
    {ν : ℂ} (hν : -1 < ν.re) (h : AsympEqDLMF atTop f fun x => (x : ℂ) ^ ν) :
    AsympEqDLMF atTop (fun x => ∫ t in a..x, f t) fun x => (x : ℂ) ^ (ν + 1) / (ν + 1) := by
  have hg0 : ∀ᶠ x : ℝ in atTop, (x : ℂ) ^ ν ≠ 0 :=
    (eventually_gt_atTop 0).mono fun x hx => ofReal_cpow_ne_zero hx ν
  have hfg := (dlmf_2_1_1 hg0).mp h
  have hν1 : ν + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hr : 0 < ν.re + 1 := by linarith
  have hwint : ∀ x, a ≤ x → ∫ t in a..x, t ^ ν.re =
      (x ^ (ν.re + 1) - a ^ (ν.re + 1)) / (ν.re + 1) :=
    fun x _ => integral_rpow (Or.inl hν)
  have hgint : ∀ x, a ≤ x → ∫ t in a..x, (t : ℂ) ^ ν =
      ((x : ℂ) ^ (ν + 1) - (a : ℂ) ^ (ν + 1)) / (ν + 1) :=
    fun x _ => integral_cpow (Or.inl hν)
  have hpow : Tendsto (fun x : ℝ => x ^ (ν.re + 1)) atTop atTop := tendsto_rpow_atTop hr
  have hW : Tendsto (fun x => ∫ t in a..x, t ^ ν.re) atTop atTop :=
    (((tendsto_atTop_add_const_right _ (-(a ^ (ν.re + 1))) hpow).atTop_div_const hr)).congr'
      (by filter_upwards [eventually_ge_atTop a] with x hx; rw [hwint x hx]; ring)
  have hL := intervalIntegral_sub_isLittleO ha hf hfg hW
  set P : ℝ → ℂ := fun x => (x : ℂ) ^ (ν + 1) / (ν + 1)
  have hnP : ∀ x, 0 < x → ‖P x‖ = x ^ (ν.re + 1) / ‖ν + 1‖ := fun x hx => by
    simp only [P, norm_div, norm_ofReal_cpow hx, Complex.add_re, Complex.one_re]
  have hn : 0 < ‖ν + 1‖ := norm_pos_iff.mpr hν1
  have hP0 : ∀ᶠ x in atTop, P x ≠ 0 :=
    (eventually_gt_atTop 0).mono fun x hx => div_ne_zero (ofReal_cpow_ne_zero hx _) hν1
  rw [dlmf_2_1_1 hP0]
  have hPn : Tendsto (fun x => ‖P x‖) atTop atTop :=
    (hpow.atTop_div_const hn).congr' (by
      filter_upwards [eventually_gt_atTop 0] with x hx; rw [hnP x hx])
  have hwP : (fun x => ∫ t in a..x, t ^ ν.re) =O[atTop] P :=
    IsBigO.of_bound (‖ν + 1‖ / (ν.re + 1)) (by
      filter_upwards [eventually_ge_atTop a] with x hx
      have hx0 : 0 < x := ha.trans_le hx
      rw [hwint x hx, hnP x hx0, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow ha.le hx hr.le)) hr.le)]
      have ha' : 0 ≤ a ^ (ν.re + 1) := Real.rpow_nonneg ha.le _
      rw [div_mul_div_comm, mul_comm (ν.re + 1) ‖ν + 1‖, ← div_mul_div_comm, div_self hn.ne',
        one_mul]
      gcongr
      linarith)
  have hc : (fun _ : ℝ => (a : ℂ) ^ (ν + 1) / (ν + 1)) =o[atTop] P :=
    isLittleO_const_left.mpr (Or.inr hPn)
  refine ((hL.trans_isBigO hwP).sub hc).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop a] with x hx
  simp only [Pi.sub_apply, hgint x hx, P]
  ring

end Azurite.DLMF
