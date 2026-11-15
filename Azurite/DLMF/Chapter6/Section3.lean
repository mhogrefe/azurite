/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section2Aux

/-!
# DLMF §6.3: graphics

The qualitative content of the figures of <https://dlmf.nist.gov/6.3> (no numbered equations).

* Figure 6.3.1 (`E₁(x)`, `Ei(x)`, `0 < x ≤ 2`): `E₁` positive (`dlmf_6_3_F1_E1_pos`), strictly
  decreasing (`dlmf_6_3_F1_E1_anti`), strictly convex (`dlmf_6_3_F1_E1_convex`), `→ ∞` at `0+`
  (`dlmf_6_3_F1_E1_zero`); `Ei` strictly increasing (`dlmf_6_3_F1_Ei_mono`) from `−∞`
  (`dlmf_6_3_F1_Ei_zero`) to `∞` (`dlmf_6_3_F1_Ei_top`), one positive zero, in `(0, 1)`
  (`dlmf_6_3_F1_Ei_zero_unique`), concave on `(0, 1]` and convex on `[1, ∞)`
  (`dlmf_6_3_F1_Ei_inflection`); the curves cross exactly once (`dlmf_6_3_F1_cross`).
* Figure 6.3.2 (`Si(x)`, `Ci(x)`, `0 ≤ x ≤ 15`): both real (`dlmf_6_3_F2_Si_real`,
  `dlmf_6_3_F2_Ci_real`); `Si` monotone on each `[nπ, (n + 1)π]` (`dlmf_6_3_F2_Si_mono`), minima
  below and maxima above the dashed line `π/2`, approaching it (`dlmf_6_3_F2_Si_extrema`),
  `Si > 0` on `(0, ∞)` with maximum at `π` (`dlmf_6_3_F2_Si_pos_max`), one crossing of `π/2` per
  half-period (`dlmf_6_3_F2_Si_cross`); `Ci → −∞` at `0+` (`dlmf_6_3_F2_Ci_zero`), monotone on
  `(0, π/2]` and each `[(n + 1/2)π, (n + 3/2)π]` (`dlmf_6_3_F2_Ci_mono`), alternating extrema
  (`dlmf_6_3_F2_Ci_extrema`), one zero per piece (`dlmf_6_3_F2_Ci_zeros`).  The extrema come
  from an alternating-series argument (`alternating_bounds`) over half-periods, with the values
  at infinity 6.2.14.
* Figure 6.3.3 (`|E₁(x + iy)|`): symmetric in `y` (`dlmf_6_3_F3_conj`); `|E₁(z)| → ∞`
  logarithmically as `z → 0`, `|E₁(z)|/ln(1/|z|) → 1` (`dlmf_6_3_F3`, via
  `dlmf_6_3_F3_log`: `E₁(z) + ln z → −γ`); the cut is §6.2's `dlmf_6_2_1_cut`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Interval ComplexConjugate

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Figure 6.3.1: `E₁(x)` and `Ei(x)`, `0 < x ≤ 2` -/

/-- `E₁(x)` at a positive real point is the real `Ein x − ln x − γ`. -/
theorem dlmf_6_3_F1_real {x : ℝ} (hx : 0 < x) : expIntE₁ x = (expIntE₁R x : ℂ) := by
  rw [expIntE₁_ofReal hx, integral_exp_neg_div_Ioi hx]

theorem continuousOn_expIntE₁R : ContinuousOn expIntE₁R (Ioi 0) :=
  fun _ hx => (hasDerivAt_expIntE₁R hx).continuousAt.continuousWithinAt

/-- **Figure 6.3.1**: `E₁` is strictly decreasing on `(0, ∞)`. -/
theorem dlmf_6_3_F1_E1_anti : StrictAntiOn expIntE₁R (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) continuousOn_expIntE₁R fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_expIntE₁R hx).deriv]
  have : 0 < Real.exp (-x) / x := div_pos (Real.exp_pos _) hx
  linarith

/-- **Figure 6.3.1**: `E₁(x) > 0` for `x > 0`. -/
theorem dlmf_6_3_F1_E1_pos {x : ℝ} (hx : 0 < x) : 0 < expIntE₁R x := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have h0 : 0 ≤ expIntE₁R (x + 1) := by
    refine le_of_tendsto tendsto_expIntE₁R_atTop ?_
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    rcases hy.eq_or_lt with rfl | hy
    · exact le_rfl
    · exact (dlmf_6_3_F1_E1_anti hx1 (hx1.trans hy) hy).le
  exact h0.trans_lt (dlmf_6_3_F1_E1_anti hx hx1 (by linarith))

/-- **Figure 6.3.1**: `E₁(x) → ∞` as `x → 0+`. -/
theorem dlmf_6_3_F1_E1_zero : Tendsto expIntE₁R (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun x => -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h2 : Tendsto (fun x => BZ.EinR x - γ) (𝓝[>] 0) (𝓝 (BZ.EinR 0 - γ)) :=
    ((continuous_EinR.tendsto 0).mono_left nhdsWithin_le_nhds).sub_const γ
  refine (h1.atTop_add h2).congr fun x => ?_
  simp only [expIntE₁R]
  ring

/-- **Figure 6.3.1**: `E₁` is strictly convex on `(0, ∞)` (`E₁′ = −e^{−x}/x` increases). -/
theorem dlmf_6_3_F1_E1_convex : StrictConvexOn ℝ (Ioi 0) expIntE₁R := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0) continuousOn_expIntE₁R ?_
  rw [interior_Ioi]
  intro x hx y hy hxy
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  rw [(hasDerivAt_expIntE₁R hx').deriv, (hasDerivAt_expIntE₁R hy').deriv, neg_lt_neg_iff,
    div_lt_div_iff₀ hy' hx']
  have he : Real.exp (-y) < Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
  nlinarith [Real.exp_pos (-y)]

theorem EinDerivR_pos (t : ℝ) : 0 < BZ.EinDerivR t := by
  unfold BZ.EinDerivR
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with h | h
    · exact div_pos_of_neg_of_neg (by
        have := Real.add_one_lt_exp (show -t ≠ 0 by linarith)
        linarith) h
    · exact div_pos (by
        have := Real.exp_lt_exp.mpr (show -t < 0 by linarith)
        rw [Real.exp_zero] at this
        linarith) h

theorem strictMono_EinR : StrictMono BZ.EinR :=
  strictMono_of_deriv_pos fun x => by rw [(BZ.hasDerivAt_EinR x).deriv]; exact EinDerivR_pos x

theorem continuousOn_EiEin : ContinuousOn BZ.EiEin (Ioi 0) :=
  fun _ hx => (BZ.hasDerivAt_EiEin (ne_of_gt hx)).continuousAt.continuousWithinAt

/-- **Figure 6.3.1**: `Ei` is strictly increasing on `(0, ∞)`. -/
theorem dlmf_6_3_F1_Ei_mono : StrictMonoOn Ei (Ioi 0) := by
  have h : StrictMonoOn BZ.EiEin (Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0) continuousOn_EiEin fun x hx => ?_
    rw [interior_Ioi] at hx
    rw [(BZ.hasDerivAt_EiEin (ne_of_gt hx)).deriv]
    exact div_pos (Real.exp_pos _) hx
  intro a ha b hb hab
  rw [Ei_eq_EiEin ha, Ei_eq_EiEin hb]
  exact h ha hb hab

/-- **Figure 6.3.1**: `Ei(x) → −∞` as `x → 0+`. -/
theorem dlmf_6_3_F1_Ei_zero : Tendsto Ei (𝓝[>] 0) atBot := by
  have h2 : Tendsto (fun x => γ - BZ.EinR (-x)) (𝓝[>] 0) (𝓝 (γ - BZ.EinR (-0))) :=
    (((continuous_EinR.comp continuous_neg).tendsto 0).mono_left nhdsWithin_le_nhds).const_sub γ
  refine (Real.tendsto_log_nhdsGT_zero.atBot_add h2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [Ei_eq_EiEin hx, BZ.EiEin]
  ring

/-- **Figure 6.3.1**: `Ei(x) → ∞` as `x → ∞` (`Ei(x) ≥ γ + ln x`). -/
theorem dlmf_6_3_F1_Ei_top : Tendsto Ei atTop atTop := by
  have h : Tendsto (fun x => γ + Real.log x) atTop atTop :=
    tendsto_atTop_add_const_left _ _ Real.tendsto_log_atTop
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Ei_eq_EiEin hx, BZ.EiEin]
  have : BZ.EinR (-x) < 0 := by
    have := strictMono_EinR (show -x < 0 by linarith)
    rwa [BZ.EinR_zero] at this
  linarith

/-- **Figure 6.3.1**: `Ei` has exactly one positive zero, and it lies in `(0, 1)`. -/
theorem dlmf_6_3_F1_Ei_zero_unique : ∃! x₀, 0 < x₀ ∧ Ei x₀ = 0 ∧ x₀ < 1 := by
  have h1 : 0 < Ei 1 := by
    rw [Ei_eq_EiEin one_pos, BZ.EiEin, Real.log_one]
    have : BZ.EinR (-1) < 0 := by
      have := strictMono_EinR (show (-1 : ℝ) < 0 by norm_num)
      rwa [BZ.EinR_zero] at this
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  obtain ⟨a, ⟨ha0, ha1⟩, hneg⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, Ei a < 0 :=
    ((dlmf_6_3_F1_Ei_zero.eventually (eventually_lt_atBot 0)).and
      (Ioo_mem_nhdsGT one_pos)).exists.imp fun a h => ⟨h.2, h.1⟩
  have hcont : ContinuousOn Ei (Icc a 1) := by
    refine (continuousOn_EiEin.mono fun x hx => ha0.trans_le hx.1).congr fun x hx => ?_
    exact Ei_eq_EiEin (ha0.trans_le hx.1)
  obtain ⟨x₀, hx₀, hval⟩ := intermediate_value_Ioo ha1.le hcont ⟨hneg, h1⟩
  refine ⟨x₀, ⟨ha0.trans hx₀.1, hval, hx₀.2⟩, fun y hy => ?_⟩
  exact dlmf_6_3_F1_Ei_mono.injOn hy.1 (ha0.trans hx₀.1) (hy.2.1.trans hval.symm)

/-- `Ei′(x) = eˣ/x` decreases on `(0, 1]` and increases on `[1, ∞)`. -/
theorem exp_div_mono :
    StrictAntiOn (fun x => Real.exp x / x) (Ioc 0 1) ∧
      StrictMonoOn (fun x => Real.exp x / x) (Ici 1) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x => Real.exp x / x)
      (Real.exp x * (x - 1) / x ^ 2) x := fun x hx => by
    refine ((Real.hasDerivAt_exp x).div (hasDerivAt_id x) hx.ne').congr_deriv ?_
    simp only [id]
    ring
  have hc : ∀ s : Set ℝ, s ⊆ Ioi 0 → ContinuousOn (fun x => Real.exp x / x) s :=
    fun s hs x hx => (hd x (hs hx)).continuousAt.continuousWithinAt
  constructor
  · refine strictAntiOn_of_deriv_neg (convex_Ioc 0 1) (hc _ Ioc_subset_Ioi_self) fun x hx => ?_
    rw [interior_Ioc] at hx
    rw [(hd x hx.1).deriv]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith [hx.2]))
      (pow_pos hx.1 2)
  · refine strictMonoOn_of_deriv_pos (convex_Ici 1)
      (hc _ fun x (hx : (1 : ℝ) ≤ x) => show (0 : ℝ) < x from lt_of_lt_of_le one_pos hx)
      fun x hx => ?_
    rw [interior_Ici] at hx
    have hx' : (1 : ℝ) < x := hx
    rw [(hd x (by linarith)).deriv]
    exact div_pos (mul_pos (Real.exp_pos _) (by linarith)) (by positivity)

theorem deriv_Ei {x : ℝ} (hx : 0 < x) : deriv Ei x = Real.exp x / x := by
  have hev : Ei =ᶠ[𝓝 x] BZ.EiEin := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact Ei_eq_EiEin hy
  rw [hev.deriv_eq, (BZ.hasDerivAt_EiEin hx.ne').deriv]

theorem continuousOn_Ei {s : Set ℝ} (hs : s ⊆ Ioi 0) : ContinuousOn Ei s :=
  (continuousOn_EiEin.mono hs).congr fun _ hx => Ei_eq_EiEin (hs hx)

/-- **Figure 6.3.1**: `Ei` is strictly concave on `(0, 1]` and strictly convex on `[1, ∞)`
(an inflection at `x = 1`). -/
theorem dlmf_6_3_F1_Ei_inflection :
    StrictConcaveOn ℝ (Ioc 0 1) Ei ∧ StrictConvexOn ℝ (Ici 1) Ei := by
  obtain ⟨h1, h2⟩ := exp_div_mono
  constructor
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioc 0 1)
      (continuousOn_Ei Ioc_subset_Ioi_self) ?_
    rw [interior_Ioc]
    intro x hx y hy hxy
    rw [deriv_Ei hx.1, deriv_Ei hy.1]
    exact h1 (Ioo_subset_Ioc_self hx) (Ioo_subset_Ioc_self hy) hxy
  · refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 1)
      (continuousOn_Ei fun x (hx : (1 : ℝ) ≤ x) => show (0 : ℝ) < x from
        lt_of_lt_of_le one_pos hx) ?_
    rw [interior_Ici]
    intro x (hx : (1 : ℝ) < x) y (hy : (1 : ℝ) < y) hxy
    rw [deriv_Ei (by linarith), deriv_Ei (by linarith)]
    exact h2 (le_of_lt hx) (le_of_lt hy) hxy

/-- **Figure 6.3.1**: the graphs of `E₁` and `Ei` cross exactly once on `(0, ∞)`. -/
theorem dlmf_6_3_F1_cross : ∃! x, 0 < x ∧ expIntE₁R x = Ei x := by
  set D := fun x => expIntE₁R x - Ei x
  have hanti : StrictAntiOn D (Ioi 0) := fun a ha b hb hab => by
    have := dlmf_6_3_F1_E1_anti ha hb hab
    have := dlmf_6_3_F1_Ei_mono ha hb hab
    simp only [D]
    linarith
  have hcont : ContinuousOn D (Ioi 0) := continuousOn_expIntE₁R.sub (continuousOn_Ei subset_rfl)
  have hlo : Tendsto D (𝓝[>] 0) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_neg_atBot_atTop.comp dlmf_6_3_F1_Ei_zero)
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    have := dlmf_6_3_F1_E1_pos hx
    simp only [D, Function.comp]
    linarith
  have hhi : Tendsto D atTop atBot :=
    ((tendsto_neg_atTop_atBot.comp dlmf_6_3_F1_Ei_top).atBot_add
      tendsto_expIntE₁R_atTop).congr fun x => by simp only [D, Function.comp]; ring
  obtain ⟨a, ha, hDa⟩ : ∃ a, 0 < a ∧ 0 < D a :=
    ((hlo.eventually (eventually_gt_atTop 0)).and self_mem_nhdsWithin).exists.imp
      fun a h => ⟨h.2, h.1⟩
  obtain ⟨b, hab, hDb⟩ : ∃ b, a < b ∧ D b < 0 :=
    ((hhi.eventually (eventually_lt_atBot 0)).and (eventually_gt_atTop a)).exists.imp
      fun b h => ⟨h.2, h.1⟩
  obtain ⟨x, hx, hDx⟩ := intermediate_value_Ioo' hab.le
    (hcont.mono fun y hy => ha.trans_le hy.1) ⟨hDb, hDa⟩
  have hx0 : 0 < x := ha.trans hx.1
  refine ⟨x, ⟨hx0, sub_eq_zero.mp hDx⟩, fun y hy => ?_⟩
  exact hanti.injOn hy.1 hx0 ((sub_eq_zero.mpr hy.2).trans hDx.symm)

/-! ### Figure 6.3.3: `|E₁(x + iy)|` -/

/-- **Figure 6.3.3**: the surface is symmetric under `y ↦ −y`: `E₁(z̄) = conj E₁(z)`. -/
theorem dlmf_6_3_F3_conj (z : ℂ) : expIntE₁ (conj z) = conj (expIntE₁ z) := by
  rw [expIntE₁, expIntE₁, ← integral_conj]
  congr 1
  funext s
  rw [map_div₀, ← Complex.exp_conj, map_neg, map_add, conj_ofReal]

/-- **Figure 6.3.3**: `E₁(z) + ln z → −γ` as `z → 0` (off the cut). -/
theorem dlmf_6_3_F3_log :
    Tendsto (fun z => expIntE₁ z + log z) (𝓝[slitPlane] 0) (𝓝 (-(γ : ℂ))) := by
  have h : Tendsto (fun z => ein z - γ) (𝓝[slitPlane] 0) (𝓝 (ein 0 - γ)) :=
    ((dlmf_6_2_3_entire 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub_const _
  rw [ein_eq, BZ.Ein_zero, zero_sub] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [dlmf_6_2_4 hz]
  ring

theorem tendsto_neg_log_norm_slitPlane :
    Tendsto (fun z : ℂ => -Real.log ‖z‖) (𝓝[slitPlane] 0) atTop := by
  have h1 : Tendsto (fun z : ℂ => ‖z‖) (𝓝[slitPlane] 0) (𝓝[>] 0) :=
    tendsto_norm_nhdsNE_zero.mono_left
      (nhdsWithin_mono _ fun z hz => slitPlane_ne_zero hz)
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)

/-- **Figure 6.3.3**: `|E₁(z)| → ∞` logarithmically as `z → 0`:
`|E₁(z)| / ln(1/|z|) → 1`. -/
theorem dlmf_6_3_F3 :
    Tendsto (fun z => ‖expIntE₁ z‖ / -Real.log ‖z‖) (𝓝[slitPlane] 0) (𝓝 1) ∧
      Tendsto (fun z => ‖expIntE₁ z‖) (𝓝[slitPlane] 0) atTop := by
  set L := fun z : ℂ => -Real.log ‖z‖
  have hL := tendsto_neg_log_norm_slitPlane
  -- `|E₁(z)| − L(z)` stays bounded: `E₁(z) = −ln|z| − i ph z + (E₁(z) + ln z)`
  have hbd : ∀ᶠ z in 𝓝[slitPlane] 0, |‖expIntE₁ z‖ - L z| ≤ π + (γ + 1) := by
    have hc := dlmf_6_3_F3_log
    filter_upwards [hc.eventually (Metric.ball_mem_nhds _ one_pos), self_mem_nhdsWithin,
      hL.eventually (eventually_ge_atTop 0)] with z hz hzs hL0
    have hz0 := slitPlane_ne_zero hzs
    have hdec : expIntE₁ z = (L z : ℂ) + (-(z.arg : ℂ) * I + (expIntE₁ z + log z)) := by
      apply Complex.ext <;> simp [L, log_re, log_im]
    have hb : ‖-(z.arg : ℂ) * I + (expIntE₁ z + log z)‖ ≤ π + (γ + 1) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_neg, norm_I, mul_one, norm_real, Real.norm_eq_abs]
        exact abs_arg_le_pi z
      · have h1 : ‖expIntE₁ z + log z - -(γ : ℂ)‖ < 1 := by
          simpa [dist_eq_norm] using hz
        have h2 : ‖(-(γ : ℂ))‖ = γ := by
          rw [norm_neg, norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
        have := norm_le_norm_sub_add (expIntE₁ z + log z) (-(γ : ℂ))
        linarith
    have hnL : ‖(L z : ℂ)‖ = L z := by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
    calc |‖expIntE₁ z‖ - L z| = |‖expIntE₁ z‖ - ‖(L z : ℂ)‖| := by rw [hnL]
      _ ≤ ‖expIntE₁ z - (L z : ℂ)‖ := abs_norm_sub_norm_le _ _
      _ ≤ π + (γ + 1) := by rw [hdec, add_sub_cancel_left]; exact hb
  set C := π + (γ + 1)
  have hq : Tendsto (fun z => (‖expIntE₁ z‖ - L z) / L z) (𝓝[slitPlane] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop hL : Tendsto (fun z => C / L z) _ _)
    filter_upwards [hbd, hL.eventually (eventually_gt_atTop 0)] with z hz hpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right hz hpos.le
  refine ⟨?_, ?_⟩
  · have h1 := hq.const_add 1
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hL.eventually (eventually_gt_atTop 0)] with z hpos
    have hne : L z ≠ 0 := hpos.ne'
    change 1 + (‖expIntE₁ z‖ - L z) / L z = ‖expIntE₁ z‖ / L z
    field_simp
    ring
  · refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C) hL)
    filter_upwards [hbd] with z hz
    have := (abs_le.mp hz).1
    linarith

/-! ### Figure 6.3.2: `Si(x)` and `Ci(x)`, `0 ≤ x ≤ 15` -/

/-- An alternating sequence `S(n + 1) − S(n) = (−1)ⁿ aₙ` with `aₙ` strictly decreasing and
`S(n) → L`: the even terms increase strictly, the odd terms decrease strictly, and
`S(2m) < L < S(2m + 1)`. -/
theorem alternating_bounds {S a : ℕ → ℝ} {L : ℝ} (hS : ∀ n, S (n + 1) - S n = (-1) ^ n * a n)
    (ha : StrictAnti a) (hlim : Tendsto S atTop (𝓝 L)) :
    StrictMono (fun m => S (2 * m)) ∧ StrictAnti (fun m => S (2 * m + 1)) ∧
      (∀ m, S (2 * m) < L) ∧ (∀ m, L < S (2 * m + 1)) := by
  have e0 : ∀ m : ℕ, ((-1 : ℝ)) ^ (2 * m) = 1 := fun m => by rw [pow_mul]; norm_num
  have e1 : ∀ m : ℕ, ((-1 : ℝ)) ^ (2 * m + 1) = -1 := fun m => by rw [pow_succ, e0]; norm_num
  have he : StrictMono (fun m => S (2 * m)) := by
    refine strictMono_nat_of_lt_succ fun m => ?_
    have h1 := hS (2 * m)
    have h2 := hS (2 * m + 1)
    have h3 := ha (show 2 * m < 2 * m + 1 by omega)
    rw [e0] at h1
    rw [e1] at h2
    simp only [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    linarith
  have ho : StrictAnti (fun m => S (2 * m + 1)) := by
    refine strictAnti_nat_of_succ_lt fun m => ?_
    have h1 := hS (2 * m + 1)
    have h2 := hS (2 * (m + 1))
    have h3 := ha (show 2 * m + 1 < 2 * (m + 1) by omega)
    rw [e1] at h1
    rw [e0] at h2
    simp only [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] at h2 h3 ⊢
    linarith
  have hev : Tendsto (fun m => S (2 * m)) atTop (𝓝 L) :=
    hlim.comp (tendsto_atTop_mono (fun m => by dsimp only [id]; omega) tendsto_id)
  have hod : Tendsto (fun m => S (2 * m + 1)) atTop (𝓝 L) :=
    hlim.comp (tendsto_atTop_mono (fun m => by dsimp only [id]; omega) tendsto_id)
  refine ⟨he, ho, fun m => ?_, fun m => ?_⟩
  · exact (he (Nat.lt_succ_self m)).trans_le (he.monotone.ge_of_tendsto hev (m + 1))
  · exact (ho.antitone.le_of_tendsto hod (m + 1)).trans_lt (ho (Nat.lt_succ_self m))

/-- The real sine integral. -/
noncomputable def SiR (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, Real.sin (x * s) / (x * s) * x

/-- **Figure 6.3.2**: `Si` is real on the real axis. -/
theorem dlmf_6_3_F2_Si_real (x : ℝ) : Si x = SiR x := by
  rw [Si, SiR, ← intervalIntegral.integral_ofReal]
  congr 1
  funext s
  push_cast
  rfl

/-- The entire `sin t / t` on the real axis. -/
noncomputable def sincR (t : ℝ) : ℝ := (sincC t).re

theorem continuous_sincR : Continuous sincR :=
  continuous_re.comp (continuous_sincC.comp continuous_ofReal)

theorem sincR_of_ne {t : ℝ} (ht : t ≠ 0) : sincR t = Real.sin t / t := by
  rw [sincR, sincC_of_ne (ofReal_ne_zero.mpr ht), ← ofReal_sin, ← ofReal_div, ofReal_re]

theorem hasDerivAt_SiR (x : ℝ) : HasDerivAt SiR (sincR x) x := by
  have h : HasDerivAt Si (sincC x) (x : ℂ) := by rw [Si_eq_fun]; exact hasDerivAt_SiF x
  have h2 := h.real_of_complex
  have he : (fun y : ℝ => (Si y).re) = SiR := funext fun y => by
    rw [dlmf_6_3_F2_Si_real, ofReal_re]
  rwa [he] at h2

theorem SiR_zero : SiR 0 = 0 := by simp [SiR]

theorem tendsto_SiR : Tendsto SiR atTop (𝓝 (π / 2)) := by
  have h := (continuous_re.tendsto _).comp dlmf_6_2_14.1
  have h1 : ((π : ℂ) / 2).re = π / 2 := by simp
  rw [h1] at h
  refine h.congr fun x => ?_
  simp only [Function.comp, dlmf_6_3_F2_Si_real, ofReal_re]

theorem continuous_SiR : Continuous SiR :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_SiR x).continuousAt

/-- `sin t = (−1)ⁿ sin(t − nπ)`. -/
theorem sin_eq_neg_one_pow (t : ℝ) (n : ℕ) :
    Real.sin t = (-1) ^ n * Real.sin (t - n * π) := by
  rw [← Real.sin_add_nat_mul_pi, sub_add_cancel]

theorem neg_one_pow_mul_self_real (n : ℕ) : ((-1 : ℝ)) ^ n * (-1) ^ n = 1 := by
  rw [← mul_pow]; norm_num

/-- **Figure 6.3.2**: `Si` increases on `[nπ, (n + 1)π]` for even `n` and decreases for odd `n`
(`Si′(x) = sin x / x`). -/
theorem dlmf_6_3_F2_Si_mono (n : ℕ) :
    (Even n → StrictMonoOn SiR (Icc (n * π) ((n + 1) * π))) ∧
      (Odd n → StrictAntiOn SiR (Icc (n * π) ((n + 1) * π))) := by
  have hpi := Real.pi_pos
  have hsign : ∀ t ∈ interior (Icc ((n : ℝ) * π) ((n + 1) * π)),
      deriv SiR t = (-1) ^ n * (Real.sin (t - n * π) / t) ∧ 0 < Real.sin (t - n * π) / t := by
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht.1
    rw [(hasDerivAt_SiR t).deriv, sincR_of_ne ht0.ne', sin_eq_neg_one_pow t n]
    refine ⟨by ring, div_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
      (by linarith [ht.2])) ht0⟩
  constructor
  · intro hn
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_SiR.continuousOn fun t ht => ?_
    obtain ⟨h1, h2⟩ := hsign t ht
    rw [h1, hn.neg_one_pow, one_mul]
    exact h2
  · intro hn
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_SiR.continuousOn fun t ht => ?_
    obtain ⟨h1, h2⟩ := hsign t ht
    rw [h1, hn.neg_one_pow]
    linarith

/-- The `n`-th half-period increment of `Si` (up to the sign `(−1)ⁿ`). -/
noncomputable def siStep (n : ℕ) : ℝ := ∫ u in (0 : ℝ)..π, (-1) ^ n * sincR (u + n * π)

theorem siStep_integrand {n : ℕ} {u : ℝ} (hu : 0 < u) :
    (-1) ^ n * sincR (u + n * π) = Real.sin u / (u + n * π) := by
  have hnpi : (0 : ℝ) ≤ n * π := by positivity
  have hpos : 0 < u + n * π := by linarith
  rw [sincR_of_ne hpos.ne', Real.sin_add_nat_mul_pi, ← mul_div_assoc, ← mul_assoc,
    neg_one_pow_mul_self_real, one_mul]

theorem SiR_step (n : ℕ) :
    SiR ((n + 1 : ℕ) * π) - SiR (n * π) = (-1) ^ n * siStep n := by
  have hftc : ∫ t in (n * π)..((n + 1 : ℕ) * π), sincR t = SiR ((n + 1 : ℕ) * π) - SiR (n * π) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_SiR t)
      (continuous_sincR.intervalIntegrable _ _)
  rw [← hftc, siStep, intervalIntegral.integral_const_mul, ← mul_assoc, neg_one_pow_mul_self_real,
    one_mul, intervalIntegral.integral_comp_add_right (fun t => sincR t), zero_add]
  push_cast
  ring_nf

theorem siStep_strictAnti : StrictAnti siStep := by
  have hpi := Real.pi_pos
  refine strictAnti_nat_of_succ_lt fun n => ?_
  have hc : ∀ k : ℕ, Continuous fun u : ℝ => (-1) ^ k * sincR (u + k * π) := fun k =>
    continuous_const.mul (continuous_sincR.comp (continuous_id.add continuous_const))
  rw [← sub_pos, siStep, siStep, ← intervalIntegral.integral_sub
    ((hc n).intervalIntegrable _ _) ((hc (n + 1)).intervalIntegrable _ _)]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (((hc n).sub (hc (n + 1))).intervalIntegrable _ _) (fun u hu => ?_) hpi
  rw [siStep_integrand hu.1, siStep_integrand hu.1, sub_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2
  have hnpi : (0 : ℝ) ≤ n * π := by positivity
  have h1 : 0 < u + n * π := by linarith [hu.1]
  push_cast
  have h2 : 0 < u + (n + 1) * π := by linarith
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith

/-- The values `S(n) = Si(nπ)`. -/
theorem SiR_alternating :
    StrictMono (fun m : ℕ => SiR ((2 * m : ℕ) * π)) ∧
      StrictAnti (fun m : ℕ => SiR ((2 * m + 1 : ℕ) * π)) ∧
      (∀ m : ℕ, SiR ((2 * m : ℕ) * π) < π / 2) ∧ (∀ m : ℕ, π / 2 < SiR ((2 * m + 1 : ℕ) * π)) :=
  alternating_bounds (S := fun n : ℕ => SiR (n * π)) SiR_step siStep_strictAnti
    (tendsto_SiR.comp (tendsto_natCast_atTop_atTop.atTop_mul_const Real.pi_pos))

/-- **Figure 6.3.2**: the minima `Si(2mπ)` lie below `π/2` and increase; the maxima `Si((2m+1)π)`
lie above `π/2` and decrease. -/
theorem dlmf_6_3_F2_Si_extrema (m : ℕ) :
    SiR (2 * m * π) < π / 2 ∧ π / 2 < SiR ((2 * m + 1) * π) ∧
      SiR (2 * m * π) < SiR ((2 * m + 2) * π) ∧ SiR ((2 * m + 3) * π) < SiR ((2 * m + 1) * π) := by
  obtain ⟨he, ho, hl, hu⟩ := SiR_alternating
  have h1 := hl m
  have h2 := hu m
  have h3 := he (Nat.lt_succ_self m)
  have h4 := ho (Nat.lt_succ_self m)
  push_cast at h1 h2 h3 h4
  refine ⟨h1, h2, by convert h3 using 2; ring, by convert h4 using 2; ring⟩

/-- Every `x ≥ 0` lies in some `[nπ, (n + 1)π]`. -/
theorem exists_mem_Icc_nat_mul_pi {x : ℝ} (hx : 0 ≤ x) :
    ∃ n : ℕ, x ∈ Icc ((n : ℝ) * π) ((n + 1) * π) := by
  have hpi := Real.pi_pos
  refine ⟨⌊x / π⌋₊, ?_, ?_⟩
  · have := Nat.floor_le (div_nonneg hx hpi.le)
    rwa [le_div_iff₀ hpi] at this
  · have := Nat.lt_floor_add_one (x / π)
    rw [div_lt_iff₀ hpi] at this
    exact this.le

/-- **Figure 6.3.2**: `Si(x) > 0` for `x > 0`, and `Si` attains its maximum over `[0, ∞)` at `π`. -/
theorem dlmf_6_3_F2_Si_pos_max :
    (∀ x : ℝ, 0 < x → 0 < SiR x) ∧ IsMaxOn SiR (Ici 0) π := by
  obtain ⟨he, ho, -, -⟩ := SiR_alternating
  have hpi := Real.pi_pos
  have hS1 : ∀ m : ℕ, SiR ((2 * m + 1 : ℕ) * π) ≤ SiR π := fun m => by
    have := ho.antitone (Nat.zero_le m)
    simpa using this
  have hS0 : ∀ m : ℕ, 0 < m → 0 < SiR ((2 * m : ℕ) * π) := fun m hm => by
    have := he hm
    simpa [SiR_zero] using this
  have key : ∀ x : ℝ, 0 ≤ x → (0 < x → 0 < SiR x) ∧ SiR x ≤ SiR π := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_mem_Icc_nat_mul_pi hx
    have hl : ((n : ℝ) * π) ∈ Icc ((n : ℝ) * π) ((n + 1) * π) :=
      ⟨le_rfl, by nlinarith⟩
    have hr : (((n : ℝ) + 1) * π) ∈ Icc ((n : ℝ) * π) ((n + 1) * π) :=
      ⟨by nlinarith, le_rfl⟩
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hmono := ((dlmf_6_3_F2_Si_mono (m + m)).1 ⟨m, rfl⟩)
      have e1 : (((m + m : ℕ) : ℝ) + 1) * π = ((2 * m + 1 : ℕ) : ℝ) * π := by push_cast; ring
      have hup := hmono.monotoneOn hn hr hn.2
      rw [e1] at hup
      refine ⟨fun hx0 => ?_, hup.trans (hS1 m)⟩
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have := hmono hl hn (by simpa using hx0)
        simpa [SiR_zero] using this
      · have h0 := hS0 m hm
        have e2 : ((2 * m : ℕ) : ℝ) * π = ((m + m : ℕ) : ℝ) * π := by push_cast; ring
        rw [e2] at h0
        have hlow := hmono.monotoneOn hl hn hn.1
        linarith
    · have hanti := ((dlmf_6_3_F2_Si_mono (2 * m + 1)).2 ⟨m, rfl⟩)
      have hup := hanti.antitoneOn hl hn hn.1
      have hlow := hanti.antitoneOn hn hr hn.2
      have h0 := hS0 (m + 1) (Nat.succ_pos m)
      have e2 : ((2 * (m + 1) : ℕ) : ℝ) * π = (((2 * m + 1 : ℕ) : ℝ) + 1) * π := by
        push_cast; ring
      rw [e2] at h0
      exact ⟨fun _ => by linarith, hup.trans (hS1 m)⟩
  exact ⟨fun x hx => (key x hx.le).1 hx, fun x hx => (key x hx).2⟩

/-- **Figure 6.3.2**: `Si` crosses the line `π/2` exactly once in each `(nπ, (n + 1)π)`. -/
theorem dlmf_6_3_F2_Si_cross (n : ℕ) :
    ∃! x, x ∈ Ioo ((n : ℝ) * π) ((n + 1) * π) ∧ SiR x = π / 2 := by
  obtain ⟨-, -, hl, hu⟩ := SiR_alternating
  have hpi := Real.pi_pos
  have hle : (n : ℝ) * π ≤ (n + 1) * π := by nlinarith
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hmono := (dlmf_6_3_F2_Si_mono (m + m)).1 ⟨m, rfl⟩
    have h1 := hl m
    have h2 := hu m
    have e1 : ((2 * m : ℕ) : ℝ) * π = ((m + m : ℕ) : ℝ) * π := by push_cast; ring
    have e2 : ((2 * m + 1 : ℕ) : ℝ) * π = (((m + m : ℕ) : ℝ) + 1) * π := by push_cast; ring
    rw [e1] at h1
    rw [e2] at h2
    obtain ⟨x, hx, hval⟩ := intermediate_value_Ioo hle continuous_SiR.continuousOn ⟨h1, h2⟩
    exact ⟨x, ⟨hx, hval⟩, fun y hy => hmono.injOn (Ioo_subset_Icc_self hy.1)
      (Ioo_subset_Icc_self hx) (hy.2.trans hval.symm)⟩
  · have hanti := (dlmf_6_3_F2_Si_mono (2 * m + 1)).2 ⟨m, rfl⟩
    have h1 := hu m
    have h2 := hl (m + 1)
    have e2 : ((2 * (m + 1) : ℕ) : ℝ) * π = (((2 * m + 1 : ℕ) : ℝ) + 1) * π := by
      push_cast; ring
    rw [e2] at h2
    obtain ⟨x, hx, hval⟩ := intermediate_value_Ioo' hle continuous_SiR.continuousOn ⟨h2, h1⟩
    exact ⟨x, ⟨hx, hval⟩, fun y hy => hanti.injOn (Ioo_subset_Icc_self hy.1)
      (Ioo_subset_Icc_self hx) (hy.2.trans hval.symm)⟩

/-- The real `Cin`. -/
noncomputable def CinR (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, (1 - Real.cos (x * s)) / (x * s) * x

theorem Cin_ofReal (x : ℝ) : Cin x = CinR x := by
  rw [Cin, CinR, ← intervalIntegral.integral_ofReal]
  congr 1
  funext s
  push_cast
  rfl

/-- The real cosine integral `−Cin x + ln x + γ` (6.2.13). -/
noncomputable def CiR (x : ℝ) : ℝ := -CinR x + Real.log x + γ

/-- **Figure 6.3.2**: `Ci` is real on the positive real axis. -/
theorem dlmf_6_3_F2_Ci_real {x : ℝ} (hx : 0 < x) : Ci x = CiR x := by
  rw [(dlmf_6_2_13 (mem_slitPlane_of_re_pos (by simpa using hx))).2, Cin_ofReal, CiR,
    ← ofReal_log hx.le]
  push_cast
  ring

theorem continuous_CinR : Continuous CinR := by
  have : CinR = fun x : ℝ => (Cin x).re := funext fun x => by rw [Cin_ofReal, ofReal_re]
  rw [this]
  exact continuous_re.comp (dlmf_6_2_12_entire.continuous.comp continuous_ofReal)

theorem hasDerivAt_CiR {x : ℝ} (hx : 0 < x) : HasDerivAt CiR (Real.cos x / x) x := by
  have h := (hasDerivAt_Ci (mem_slitPlane_of_re_pos
    (show (0 : ℝ) < (x : ℂ).re by simpa using hx))).real_of_complex
  rw [← ofReal_cos, ← ofReal_div, ofReal_re] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with y hy
  rw [dlmf_6_3_F2_Ci_real hy, ofReal_re]

theorem continuousOn_CiR {s : Set ℝ} (hs : s ⊆ Ioi 0) : ContinuousOn CiR s :=
  fun _ hx => (hasDerivAt_CiR (hs hx)).continuousAt.continuousWithinAt

theorem tendsto_CiR : Tendsto CiR atTop (𝓝 0) := by
  have h := (continuous_re.tendsto _).comp dlmf_6_2_14.2
  rw [zero_re] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp, dlmf_6_3_F2_Ci_real hx, ofReal_re]

/-- **Figure 6.3.2**: `Ci(x) → −∞` as `x → 0+`. -/
theorem dlmf_6_3_F2_Ci_zero : Tendsto CiR (𝓝[>] 0) atBot := by
  have h2 : Tendsto (fun x => -CinR x + γ) (𝓝[>] 0) (𝓝 (-CinR 0 + γ)) :=
    (((continuous_CinR.tendsto 0).mono_left nhdsWithin_le_nhds).neg).add_const γ
  refine (Real.tendsto_log_nhdsGT_zero.atBot_add h2).congr fun x => ?_
  simp only [CiR]
  ring

/-- `cos t = −(−1)ⁿ sin(t − (n + 1/2)π)`. -/
theorem cos_eq_neg_one_pow (t : ℝ) (n : ℕ) :
    Real.cos t = -(-1) ^ n * Real.sin (t - (n + 1 / 2) * π) := by
  have h := Real.cos_add_nat_mul_pi (t - (n + 1 / 2) * π + π / 2) n
  rw [Real.cos_add_pi_div_two, show t - (n + 1 / 2) * π + π / 2 + n * π = t by ring] at h
  rw [h]
  ring

/-- **Figure 6.3.2**: `Ci` increases on `(0, π/2]`; on `[(n + 1/2)π, (n + 3/2)π]` it decreases for
even `n` and increases for odd `n` (`Ci′(x) = cos x / x`). -/
theorem dlmf_6_3_F2_Ci_mono :
    StrictMonoOn CiR (Ioc 0 (π / 2)) ∧ ∀ n : ℕ,
      (Even n → StrictAntiOn CiR (Icc ((n + 1 / 2) * π) ((n + 3 / 2) * π))) ∧
      (Odd n → StrictMonoOn CiR (Icc ((n + 1 / 2) * π) ((n + 3 / 2) * π))) := by
  have hpi := Real.pi_pos
  refine ⟨?_, fun n => ?_⟩
  · refine strictMonoOn_of_deriv_pos (convex_Ioc 0 _) (continuousOn_CiR Ioc_subset_Ioi_self)
      fun t ht => ?_
    rw [interior_Ioc] at ht
    rw [(hasDerivAt_CiR ht.1).deriv]
    exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩) ht.1
  have hsub : Icc (((n : ℝ) + 1 / 2) * π) ((n + 3 / 2) * π) ⊆ Ioi 0 := fun t ht => by
    have : (0 : ℝ) < (n + 1 / 2) * π := by positivity
    exact this.trans_le ht.1
  have hsign : ∀ t ∈ interior (Icc (((n : ℝ) + 1 / 2) * π) ((n + 3 / 2) * π)),
      deriv CiR t = -(-1) ^ n * (Real.sin (t - (n + 1 / 2) * π) / t) ∧
        0 < Real.sin (t - (n + 1 / 2) * π) / t := by
    intro t ht
    have ht0 : 0 < t := hsub (interior_subset ht)
    rw [interior_Icc] at ht
    rw [(hasDerivAt_CiR ht0).deriv, cos_eq_neg_one_pow t n]
    refine ⟨by ring, div_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
      (by linarith [ht.2])) ht0⟩
  constructor
  · intro hn
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuousOn_CiR hsub) fun t ht => ?_
    obtain ⟨h1, h2⟩ := hsign t ht
    rw [h1, hn.neg_one_pow]
    linarith
  · intro hn
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_CiR hsub) fun t ht => ?_
    obtain ⟨h1, h2⟩ := hsign t ht
    rw [h1, hn.neg_one_pow]
    linarith

/-- The `n`-th half-period increment of `Ci` (up to the sign `−(−1)ⁿ`). -/
noncomputable def ciStep (n : ℕ) : ℝ := ∫ u in (0 : ℝ)..π, Real.sin u / (u + (n + 1 / 2) * π)

theorem continuousOn_sin_div_shift (n : ℕ) :
    ContinuousOn (fun u : ℝ => Real.sin u / (u + (n + 1 / 2) * π)) (uIcc 0 π) := by
  have hpi := Real.pi_pos
  intro u hu
  rw [uIcc_of_le hpi.le] at hu
  have : (0 : ℝ) < (n + 1 / 2) * π := by positivity
  exact (Real.continuous_sin.continuousAt.div (continuous_id.add continuous_const).continuousAt
    (show u + ((n : ℝ) + 1 / 2) * π ≠ 0 by linarith [hu.1])).continuousWithinAt

theorem CiR_step (n : ℕ) :
    CiR (((n + 1 : ℕ) + 1 / 2) * π) - CiR ((n + 1 / 2) * π) = -(-1) ^ n * ciStep n := by
  have hpi := Real.pi_pos
  set a : ℝ := (n + 1 / 2) * π with ha
  have ha0 : 0 < a := by positivity
  have hb : (((n + 1 : ℕ) : ℝ) + 1 / 2) * π = π + a := by rw [ha]; push_cast; ring
  rw [hb]
  have hftc : ∫ t in a..(π + a), Real.cos t / t = CiR (π + a) - CiR a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_
    · rw [uIcc_of_le (by linarith)] at ht
      exact hasDerivAt_CiR (ha0.trans_le ht.1)
    · refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [uIcc_of_le (by linarith)] at ht
      exact (Real.continuous_cos.continuousAt.div continuousAt_id
        (show id t ≠ 0 from (ha0.trans_le ht.1).ne')).continuousWithinAt
  have hshift : ∫ t in a..(π + a), Real.cos t / t =
      ∫ u in (0 : ℝ)..π, Real.cos (u + a) / (u + a) := by
    rw [intervalIntegral.integral_comp_add_right (fun t => Real.cos t / t) a, zero_add]
  rw [← hftc, hshift, ciStep, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [cos_eq_neg_one_pow (u + a) n, ← ha, add_sub_cancel_right]
  ring

theorem ciStep_strictAnti : StrictAnti ciStep := by
  have hpi := Real.pi_pos
  refine strictAnti_nat_of_succ_lt fun n => ?_
  rw [← sub_pos, ciStep, ciStep, ← intervalIntegral.integral_sub
    (continuousOn_sin_div_shift n).intervalIntegrable
    (continuousOn_sin_div_shift (n + 1)).intervalIntegrable]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (((continuousOn_sin_div_shift n).sub (continuousOn_sin_div_shift (n + 1))).intervalIntegrable)
    (fun u hu => ?_) hpi
  have hs := Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2
  have hnpi : (0 : ℝ) ≤ n * π := by positivity
  have h1 : 0 < u + (n + 1 / 2) * π := by nlinarith [hu.1]
  have h2 : 0 < u + (((n + 1 : ℕ) : ℝ) + 1 / 2) * π := by push_cast; nlinarith [hu.1]
  rw [sub_pos, div_lt_div_iff₀ h2 h1]
  push_cast
  nlinarith

/-- The values `Ci((n + 1/2)π)` alternate in sign. -/
theorem CiR_alternating :
    StrictMono (fun m : ℕ => -CiR (((2 * m : ℕ) + 1 / 2) * π)) ∧
      StrictAnti (fun m : ℕ => -CiR (((2 * m + 1 : ℕ) + 1 / 2) * π)) ∧
      (∀ m : ℕ, -CiR (((2 * m : ℕ) + 1 / 2) * π) < 0) ∧
      (∀ m : ℕ, 0 < -CiR (((2 * m + 1 : ℕ) + 1 / 2) * π)) := by
  have hlim : Tendsto (fun n : ℕ => -CiR ((n + 1 / 2) * π)) atTop (𝓝 0) := by
    have h := (tendsto_CiR.comp ((tendsto_atTop_add_const_right _ (1 / 2 : ℝ)
      tendsto_natCast_atTop_atTop).atTop_mul_const Real.pi_pos)).neg
    rwa [neg_zero] at h
  exact alternating_bounds (S := fun n : ℕ => -CiR ((n + 1 / 2) * π))
    (fun n => by
      have := CiR_step n
      show -CiR (((n + 1 : ℕ) + 1 / 2) * π) - -CiR ((n + 1 / 2) * π) = (-1) ^ n * ciStep n
      linarith) ciStep_strictAnti hlim

/-- **Figure 6.3.2**: the local maxima `Ci((2m + 1/2)π)` are positive and decrease; the local minima
`Ci((2m + 3/2)π)` are negative and increase. -/
theorem dlmf_6_3_F2_Ci_extrema (m : ℕ) :
    0 < CiR ((2 * m + 1 / 2) * π) ∧ CiR ((2 * m + 3 / 2) * π) < 0 ∧
      CiR ((2 * m + 5 / 2) * π) < CiR ((2 * m + 1 / 2) * π) ∧
      CiR ((2 * m + 3 / 2) * π) < CiR ((2 * m + 7 / 2) * π) := by
  obtain ⟨he, ho, hl, hu⟩ := CiR_alternating
  have h1 := hl m
  have h2 := hu m
  have h3 := he (show m < m + 1 by omega)
  have h4 := ho (show m < m + 1 by omega)
  dsimp only at h3 h4
  have e1 : (((2 * m : ℕ) : ℝ) + 1 / 2) * π = (2 * m + 1 / 2) * π := by push_cast; ring
  have e2 : (((2 * m + 1 : ℕ) : ℝ) + 1 / 2) * π = (2 * m + 3 / 2) * π := by push_cast; ring
  have e3 : (((2 * (m + 1) : ℕ) : ℝ) + 1 / 2) * π = (2 * m + 5 / 2) * π := by push_cast; ring
  have e4 : (((2 * (m + 1) + 1 : ℕ) : ℝ) + 1 / 2) * π = (2 * m + 7 / 2) * π := by
    push_cast; ring
  rw [e1] at h1 h3
  rw [e2] at h2 h4
  rw [e3] at h3
  rw [e4] at h4
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Figure 6.3.2**: `Ci` has exactly one zero in `(0, π/2)` and exactly one in each
`((n + 1/2)π, (n + 3/2)π)`. -/
theorem dlmf_6_3_F2_Ci_zeros :
    (∃! x, x ∈ Ioo 0 (π / 2) ∧ CiR x = 0) ∧
      ∀ n : ℕ, ∃! x, x ∈ Ioo ((n + 1 / 2) * π) ((n + 3 / 2) * π) ∧ CiR x = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨hmono0, hmono⟩ := dlmf_6_3_F2_Ci_mono
  constructor
  · have hpos : 0 < CiR (π / 2) := by
      have := (dlmf_6_3_F2_Ci_extrema 0).1
      rwa [show (2 * ((0 : ℕ) : ℝ) + 1 / 2) * π = π / 2 by push_cast; ring] at this
    obtain ⟨ε, ⟨hε0, hε1⟩, hneg⟩ : ∃ ε ∈ Ioo 0 (π / 2), CiR ε < 0 :=
      ((dlmf_6_3_F2_Ci_zero.eventually (eventually_lt_atBot 0)).and
        (Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < π / 2))).exists.imp fun a h => ⟨h.2, h.1⟩
    obtain ⟨x, hx, hval⟩ := intermediate_value_Ioo hε1.le
      (continuousOn_CiR fun t ht => hε0.trans_le ht.1) ⟨hneg, hpos⟩
    refine ⟨x, ⟨⟨hε0.trans hx.1, hx.2⟩, hval⟩, fun y hy => ?_⟩
    exact hmono0.injOn (Ioo_subset_Ioc_self hy.1) ⟨hε0.trans hx.1, hx.2.le⟩
      (hy.2.trans hval.symm)
  · intro n
    have hsub : Icc (((n : ℝ) + 1 / 2) * π) ((n + 3 / 2) * π) ⊆ Ioi 0 := fun t ht => by
      have : (0 : ℝ) < (n + 1 / 2) * π := by positivity
      exact this.trans_le ht.1
    have hle : ((n : ℝ) + 1 / 2) * π ≤ (n + 3 / 2) * π := by nlinarith
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · obtain ⟨h1, h2, -, -⟩ := dlmf_6_3_F2_Ci_extrema m
      have e : ((m + m : ℕ) : ℝ) = 2 * m := by push_cast; ring
      rw [e] at hsub hle ⊢
      have hanti := (hmono (m + m)).1 ⟨m, rfl⟩
      rw [e] at hanti
      obtain ⟨x, hx, hval⟩ := intermediate_value_Ioo' hle (continuousOn_CiR hsub) ⟨h2, h1⟩
      exact ⟨x, ⟨hx, hval⟩, fun y hy => hanti.injOn (Ioo_subset_Icc_self hy.1)
        (Ioo_subset_Icc_self hx) (hy.2.trans hval.symm)⟩
    · obtain ⟨-, h1, -, -⟩ := dlmf_6_3_F2_Ci_extrema m
      obtain ⟨h2, -, -, -⟩ := dlmf_6_3_F2_Ci_extrema (m + 1)
      have e : ((2 * m + 1 : ℕ) : ℝ) = 2 * m + 1 := by push_cast; ring
      rw [e] at hsub hle ⊢
      have hmon := (hmono (2 * m + 1)).2 ⟨m, rfl⟩
      rw [e] at hmon
      have ea : (2 * (m : ℝ) + 1 + 1 / 2) * π = (2 * m + 3 / 2) * π := by ring
      have eb : (2 * (m : ℝ) + 1 + 3 / 2) * π = (2 * ((m + 1 : ℕ) : ℝ) + 1 / 2) * π := by
        push_cast; ring
      rw [ea, eb] at hle hmon ⊢
      rw [ea, eb] at hsub
      obtain ⟨x, hx, hval⟩ := intermediate_value_Ioo hle (continuousOn_CiR hsub) ⟨h1, h2⟩
      exact ⟨x, ⟨hx, hval⟩, fun y hy => hmon.injOn (Ioo_subset_Icc_self hy.1)
        (Ioo_subset_Icc_self hx) (hy.2.trans hval.symm)⟩

end Azurite.DLMF
