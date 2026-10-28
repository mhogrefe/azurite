/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9Integration
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# DLMF §1.9(iii): Cauchy's theorem with boundary continuity

DLMF 1.9.29–1.9.31 under DLMF's own hypotheses: `C` a simple closed (piecewise-`C¹`) contour,
`f` continuous within and on `C` and analytic within `C` — no analyticity across `C`.
`Section9Integration` proves them for `f` analytic on a neighbourhood of `C` and its interior.

* DLMF-facing: `dlmf_1_9_29_jordan`, `dlmf_1_9_30_jordan`, `dlmf_1_9_31_jordan`; winding-number
  forms `ClosedPiecewiseC1.contourIntegral_eq_zero_of_continuousOn`,
  `contourIntegral_div_sub_of_continuousOn`, `contourIntegral_div_sub_pow_of_continuousOn`
  (via `dslope`, continuous on the closed region by `continuousOn_dslope_of_continuousOn`).

Proof of Cauchy's theorem.  Fix `ε > 0`.
1. Smooth approximation: `f` extends continuously to `ℂ` (Tietze) and is uniformly approximated
   on the compact `K = interior ∪ C` by a smooth `φ` (`exists_contDiff_near`).  The difference
   contributes `≤ L ε` (`norm_contourIntegral_le`, `L = length`).
2. Cutoff: `h = ψ ⋆ ramp_δ(dist(·, Dᶜ))` (`cutoff`, `D` the interior) is smooth, vanishes within
   `δ/2` of `Dᶜ`, equals `1` beyond `3δ`, has `|1 − h| ≤ 5/4` and gradient `≤ 1/δ`
   (`abs_cutoff_sub_le`: convolution preserves the Lipschitz constant).
3. Green's theorem for `φ − h(φ − f)` (`C¹` on `ℂ`, equal to `φ` on `C`, to `f` deep inside):
   `∂̄` of it is `(1 − h) ∂̄φ − (φ − f) ∂̄h` inside, zero beyond `3δ`; so
   `‖∮ φ‖ ≤ 2 ((5/4) S + ε/δ) |{dist(·, C) < 4δ}|` (`norm_contourIntegral_le_of_near`, using
   `mem_thickening_of_infDist_compl_lt` and `|W| ≤ 1` for Jordan curves).
4. Minkowski bound `|{dist(·, C) < r}| ≤ A r` (`exists_volume_thickening_le`: each `C¹` piece is
   covered by `≈ M ℓ / r` disks of radius `2r`, `volume_thickening_image_le`).
   Hence `‖∮ φ‖ ≤ 10 S A δ + 8 A ε`; choosing `δ` small, `‖∮ f‖ ≤ (L + 8A + 1) ε`.
-/

open Complex MeasureTheory Set Metric Filter Topology Bornology
open scoped Interval Real Convolution

namespace Azurite.DLMF

/-! ### Area of a neighbourhood of a piecewise-`C¹` curve -/

theorem volume_ball_complex {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    volume (ball z r) = ENNReal.ofReal (π * r ^ 2) := by
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- The `r`-neighbourhood of an `M`-Lipschitz arc over `[α, β]` has area
`≤ 4π (M (β − α) r + 3 r²)`: it is covered by `≈ M (β − α)/r` disks of radius `2r`. -/
theorem volume_thickening_image_le {g : ℝ → ℂ} {α β M r : ℝ} (hαβ : α < β) (hM : 0 ≤ M)
    (hlip : ∀ s ∈ Icc α β, ∀ s' ∈ Icc α β, ‖g s - g s'‖ ≤ M * |s - s'|) (hr : 0 < r) :
    volume (thickening r (g '' Icc α β)) ≤
      ENNReal.ofReal (4 * π * (M * (β - α) * r + 3 * r ^ 2)) := by
  set q := M * (β - α) / r with hq
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hM (sub_pos.mpr hαβ).le) hr.le
  set N : ℕ := ⌈q⌉₊ + 1 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  set Δ := (β - α) / N with hΔ
  have hΔpos : 0 < Δ := div_pos (sub_pos.mpr hαβ) hNpos
  have hMΔ : M * Δ ≤ r := by
    have h1 : q ≤ N := by
      rw [hN]
      push_cast
      linarith [Nat.le_ceil q]
    rw [hq, div_le_iff₀ hr] at h1
    rw [hΔ, mul_div_assoc', div_le_iff₀ hNpos]
    linarith
  have hsub : thickening r (g '' Icc α β) ⊆
      ⋃ j ∈ Finset.range (N + 1), ball (g (α + j * Δ)) (2 * r) := by
    intro z hz
    obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := mem_thickening_iff.mp hz
    set j := ⌊(s - α) / Δ⌋₊ with hj
    have hx0 : 0 ≤ (s - α) / Δ := div_nonneg (by linarith [hs.1]) hΔpos.le
    have hjle : (j : ℝ) ≤ (s - α) / Δ := Nat.floor_le hx0
    have hjlt : (s - α) / Δ < j + 1 := Nat.lt_floor_add_one _
    have hxN : (s - α) / Δ ≤ N := by
      rw [div_le_iff₀ hΔpos, hΔ, mul_div_cancel₀ _ hNpos.ne']
      linarith [hs.2]
    have hjN : j ≤ N := by exact_mod_cast hjle.trans hxN
    have hjΔ : (j : ℝ) * Δ ≤ s - α := (le_div_iff₀ hΔpos).mp hjle
    have hjΔ' : s - α < (j + 1) * Δ := (div_lt_iff₀ hΔpos).mp hjlt
    have hsj : α + j * Δ ∈ Icc α β := ⟨le_add_of_nonneg_right (by positivity), by linarith [hs.2]⟩
    have hdist : |s - (α + j * Δ)| ≤ Δ := by
      rw [abs_le]
      constructor <;> nlinarith
    refine mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjN), ?_⟩
    rw [mem_ball]
    have hg : dist (g s) (g (α + j * Δ)) ≤ r := by
      rw [dist_eq_norm]
      exact (hlip s hs _ hsj).trans ((mul_le_mul_of_nonneg_left hdist hM).trans hMΔ)
    linarith [dist_triangle z (g s) (g (α + j * Δ))]
  have hceil : (⌈q⌉₊ : ℝ) < q + 1 := Nat.ceil_lt_add_one hq0
  calc volume (thickening r (g '' Icc α β))
      ≤ volume (⋃ j ∈ Finset.range (N + 1), ball (g (α + j * Δ)) (2 * r)) := measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range (N + 1), volume (ball (g (α + j * Δ)) (2 * r)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _j ∈ Finset.range (N + 1), ENNReal.ofReal (π * (2 * r) ^ 2) :=
        Finset.sum_congr rfl fun j _ => volume_ball_complex (by positivity) _
    _ = ENNReal.ofReal ((N + 1 : ℕ) • (π * (2 * r) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, ENNReal.ofReal_nsmul]
    _ ≤ ENNReal.ofReal (4 * π * (M * (β - α) * r + 3 * r ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [nsmul_eq_mul, hN]
        push_cast
        have hqr : q * r = M * (β - α) := by rw [hq]; field_simp
        have h1 : ((⌈q⌉₊ : ℝ) + 1 + 1) * (4 * π * r ^ 2) ≤ (q + 3) * (4 * π * r ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h2 : (q + 3) * (4 * π * r ^ 2) = 4 * π * (M * (β - α) * r + 3 * r ^ 2) := by
          rw [← hqr]
          ring
        nlinarith

end Azurite.DLMF

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

theorem exists_lipschitz_piece (i : ℕ) : ∃ M, 0 ≤ M ∧ (i < P.n →
    ∀ s ∈ Icc (P.t i) (P.t (i + 1)), ∀ s' ∈ Icc (P.t i) (P.t (i + 1)),
      ‖P.g i s - P.g i s'‖ ≤ M * |s - s'|) := by
  by_cases hi : i < P.n
  · obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (((P.contDiff i hi).continuous_deriv le_rfl).continuousOn (s := Icc (P.t i) (P.t (i + 1))))
    refine ⟨max M 0, le_max_right _ _, fun _ s hs s' hs' => ?_⟩
    have := (convex_Icc (P.t i) (P.t (i + 1))).norm_image_sub_le_of_norm_deriv_le
      (C := max M 0) (fun x _ => (P.contDiff i hi).differentiable one_ne_zero x)
      (fun x hx => (hM x hx).trans (le_max_left _ _)) hs' hs
    rwa [Real.norm_eq_abs] at this
  · exact ⟨0, le_rfl, fun h => absurd h hi⟩

/-- **Minkowski bound**: the `r`-neighbourhood of a closed piecewise-`C¹` curve has area `O(r)`. -/
theorem exists_volume_thickening_le : ∃ A, 0 ≤ A ∧ ∀ r, 0 < r → r ≤ 1 →
    volume (thickening r P.curve) ≤ ENNReal.ofReal (A * r) := by
  choose M hM0 hMl using P.exists_lipschitz_piece
  set A := π + ∑ i ∈ Finset.range P.n, 4 * π * (M i * (P.t (i + 1) - P.t i) + 3) with hA
  have hterm : ∀ i ∈ Finset.range P.n, 0 ≤ M i * (P.t (i + 1) - P.t i) := fun i hi =>
    mul_nonneg (hM0 i) (sub_pos.mpr (P.lt i (Finset.mem_range.mp hi))).le
  have hA0 : 0 ≤ A := add_nonneg Real.pi_pos.le (Finset.sum_nonneg fun i hi => by
    have := hterm i hi
    positivity)
  refine ⟨A, hA0, fun r hr hr1 => ?_⟩
  have hsub : thickening r P.curve ⊆ ball (c a) r ∪
      ⋃ i ∈ Finset.range P.n, thickening r (P.g i '' Icc (P.t i) (P.t (i + 1))) := by
    intro z hz
    obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := mem_thickening_iff.mp hz
    rcases Nat.eq_zero_or_pos P.n with hn | hn
    · left
      have hab : a = b := by
        have h2 := P.last
        rw [hn] at h2
        exact P.first.symm.trans h2
      have : s = a := le_antisymm (hab ▸ hs.2) hs.1
      subst this
      exact hzs
    · right
      obtain ⟨i, hi, hsi⟩ := P.exists_piece hs hn
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hi,
        mem_thickening_iff.mpr ⟨_, ⟨s, hsi, (P.eqOn i hi hsi).symm⟩, hzs⟩⟩
  have hpieces : ∀ i ∈ Finset.range P.n, 0 ≤ 4 * π * (M i * (P.t (i + 1) - P.t i) * r +
      3 * r ^ 2) := fun i hi => by
    have := hterm i hi
    positivity
  calc volume (thickening r P.curve)
      ≤ volume (ball (c a) r) + ∑ i ∈ Finset.range P.n,
          volume (thickening r (P.g i '' Icc (P.t i) (P.t (i + 1)))) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add_right (measure_biUnion_finset_le _ _) _))
    _ ≤ ENNReal.ofReal (π * r ^ 2) + ∑ i ∈ Finset.range P.n,
          ENNReal.ofReal (4 * π * (M i * (P.t (i + 1) - P.t i) * r + 3 * r ^ 2)) :=
        add_le_add (Azurite.DLMF.volume_ball_complex hr.le _).le (Finset.sum_le_sum fun i hi =>
          Azurite.DLMF.volume_thickening_image_le (P.lt i (Finset.mem_range.mp hi)) (hM0 i)
            (hMl i (Finset.mem_range.mp hi)) hr)
    _ = ENNReal.ofReal (π * r ^ 2 + ∑ i ∈ Finset.range P.n,
          4 * π * (M i * (P.t (i + 1) - P.t i) * r + 3 * r ^ 2)) := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg hpieces),
          ENNReal.ofReal_sum_of_nonneg hpieces]
    _ ≤ ENNReal.ofReal (A * r) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hA, add_mul, Finset.sum_mul]
        have hr2 : r ^ 2 ≤ r := by nlinarith
        refine add_le_add (by nlinarith [Real.pi_pos]) (Finset.sum_le_sum fun i hi => ?_)
        have := hterm i hi
        nlinarith [Real.pi_pos]

/-- The length `∑ᵢ ∫ |gᵢ′|` of the curve. -/
noncomputable def length : ℝ :=
  ∑ i ∈ Finset.range P.n, ∫ s in P.t i..P.t (i + 1), ‖deriv (P.g i) s‖

theorem norm_contourIntegral_le {f : ℂ → ℂ} {ε : ℝ} (hε : ∀ z ∈ P.curve, ‖f z‖ ≤ ε) :
    ‖P.contourIntegral f‖ ≤ P.length * ε := by
  unfold ClosedPiecewiseC1.contourIntegral length
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.norm_integral_le_of_norm_le (P.lt i hi').le
    (ae_of_all _ fun s hs => ?_)
    ((((P.contDiff i hi').continuous_deriv le_rfl).norm.mul continuous_const).intervalIntegrable
      _ _)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hε _ (P.mem_curve_of_mem_piece hi' (Ioc_subset_Icc_self hs)))
    (norm_nonneg _)

theorem contourIntegral_sub {f₁ f₂ : ℂ → ℂ} (h₁ : ContinuousOn f₁ P.curve)
    (h₂ : ContinuousOn f₂ P.curve) :
    P.contourIntegral (fun z => f₁ z - f₂ z) = P.contourIntegral f₁ - P.contourIntegral f₂ := by
  unfold ClosedPiecewiseC1.contourIntegral
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [← intervalIntegral.integral_sub (P.intervalIntegrable_piece h₁ hi')
    (P.intervalIntegrable_piece h₂ hi')]
  congr 1
  ext s
  ring

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

/-! ### Smooth approximation and a Lipschitz cutoff -/

/-- A function continuous on a compact set is uniformly approximable there by smooth functions. -/
theorem exists_contDiff_near {K : Set ℂ} (hK : IsCompact K) {f : ℂ → ℂ} (hf : ContinuousOn f K)
    {ε : ℝ} (hε : 0 < ε) : ∃ φ : ℂ → ℂ, ContDiff ℝ 1 φ ∧ ∀ z ∈ K, ‖φ z - f z‖ ≤ ε := by
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hK.isClosed ⟨K.domRestrict f, hf.domRestrict⟩
  have hFK : ∀ z ∈ K, F z = f z := fun z hz => by
    have := congrArg (fun g : C(K, ℂ) => g ⟨z, hz⟩) hF
    exact this
  have huc : UniformContinuousOn F (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous F.continuous.continuousOn
  obtain ⟨δ, hδ, hFδ⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  obtain ⟨g, hg, hgF⟩ :=
    F.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (lt_min one_pos hδ)
  refine ⟨g, hg.of_le (by simp), fun z hz => ?_⟩
  rw [← hFK z hz, ← dist_eq_norm]
  refine hgF z ε fun y hy => ?_
  rw [mem_ball, lt_min_iff] at hy
  exact (hFδ y (mem_cthickening_of_dist_le _ z _ _ hz hy.1.le) z (self_subset_cthickening _ hz)
    hy.2).le

/-- The ramp `t ↦ min (max (t/δ − 1) 0) 1`: `0` for `t ≤ δ`, `1` for `t ≥ 2δ`. -/
noncomputable def ramp (δ t : ℝ) : ℝ := min (max (t / δ - 1) 0) 1

theorem abs_ramp_sub_le {δ : ℝ} (hδ : 0 < δ) (s t : ℝ) :
    |ramp δ s - ramp δ t| ≤ |s - t| / δ := by
  unfold ramp
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
  refine (abs_max_sub_max_le_abs _ _ _).trans_eq ?_
  rw [show s / δ - 1 - (t / δ - 1) = (s - t) / δ by ring, abs_div, abs_of_pos hδ]

theorem ramp_eq_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) : ramp δ t = 0 := by
  have : t / δ - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hδ]; exact ht
  simp [ramp, max_eq_right this]

theorem ramp_eq_one {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) : ramp δ t = 1 := by
  have : 1 ≤ t / δ - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith
  simp [ramp, max_eq_left (zero_le_one.trans this), this]

theorem ramp_mem_Icc (δ t : ℝ) : ramp δ t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

theorem continuous_ramp {δ : ℝ} : Continuous (ramp δ) := by
  unfold ramp
  fun_prop

/-- The bump used for the cutoff. -/
noncomputable def cutBump {δ : ℝ} (hδ : 0 < δ) : ContDiffBump (0 : ℂ) :=
  ⟨δ / 8, δ / 4, by positivity, by linarith⟩

/-- The Lipschitz profile `ramp δ (dist(z, Sᶜ))`. -/
noncomputable def cutProfile (S : Set ℂ) (δ : ℝ) (z : ℂ) : ℝ := ramp δ (infDist z Sᶜ)

/-- The smooth cutoff: `0` within `δ/2` of `Sᶜ`, `1` beyond `3δ`, gradient `≤ 1/δ`. -/
noncomputable def cutoff (S : Set ℂ) {δ : ℝ} (hδ : 0 < δ) : ℂ → ℝ :=
  (cutBump hδ).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] cutProfile S δ

theorem continuous_cutProfile (S : Set ℂ) (δ : ℝ) : Continuous (cutProfile S δ) :=
  continuous_ramp.comp (continuous_infDist_pt Sᶜ)

theorem abs_cutProfile_sub_le (S : Set ℂ) {δ : ℝ} (hδ : 0 < δ) (x y : ℂ) :
    |cutProfile S δ x - cutProfile S δ y| ≤ 1 / δ * dist x y := by
  refine (abs_ramp_sub_le hδ _ _).trans ?_
  rw [one_div_mul_eq_div]
  gcongr
  rw [abs_sub_le_iff]
  constructor <;> linarith [infDist_le_infDist_add_dist (x := x) (y := y) (s := Sᶜ),
    infDist_le_infDist_add_dist (x := y) (y := x) (s := Sᶜ), dist_comm x y]

theorem contDiff_cutoff (S : Set ℂ) {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ 1 (cutoff S hδ) :=
  (cutBump hδ).hasCompactSupport_normed.contDiff_convolution_left _ (cutBump hδ).contDiff_normed
    (continuous_cutProfile S δ).locallyIntegrable

theorem abs_cutoff_sub_le (S : Set ℂ) {δ : ℝ} (hδ : 0 < δ) (x y : ℂ) :
    |cutoff S hδ x - cutoff S hδ y| ≤ 1 / δ * dist x y := by
  set ψ := cutBump hδ
  have hc := continuous_cutProfile S δ
  unfold cutoff
  rw [convolution_def, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hint : ∀ w, Integrable (fun t => ψ.normed volume t * cutProfile S δ (w - t)) := fun w =>
    (ψ.continuous_normed.mul
      (hc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport_normed.mul_right)
  rw [← integral_sub (hint x) (hint y), ← Real.norm_eq_abs]
  calc ‖∫ t, (ψ.normed volume t * cutProfile S δ (x - t) -
        ψ.normed volume t * cutProfile S δ (y - t))‖
      ≤ ∫ t, ψ.normed volume t * (1 / δ * dist x y) := by
        refine norm_integral_le_of_norm_le (ψ.integrable_normed.mul_const _)
          (ae_of_all _ fun t => ?_)
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (ψ.nonneg_normed t)]
        refine mul_le_mul_of_nonneg_left ?_ (ψ.nonneg_normed t)
        have := abs_cutProfile_sub_le S hδ (x - t) (y - t)
        rwa [dist_sub_right] at this
    _ = 1 / δ * dist x y := by rw [integral_mul_const, ψ.integral_normed, one_mul]

theorem cutoff_eq_cutProfile (S : Set ℂ) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (h : ∀ y ∈ ball z (δ / 4), cutProfile S δ y = cutProfile S δ z) :
    cutoff S hδ z = cutProfile S δ z :=
  (cutBump hδ).normed_convolution_eq_right h

theorem cutoff_eq_zero (S : Set ℂ) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : infDist z Sᶜ < δ / 2) :
    cutoff S hδ z = 0 := by
  have h0 : ∀ y ∈ ball z (δ / 4), cutProfile S δ y = 0 := fun y hy => by
    refine ramp_eq_zero hδ ?_
    have := infDist_le_infDist_add_dist (x := y) (y := z) (s := Sᶜ)
    rw [mem_ball] at hy
    linarith
  rw [cutoff_eq_cutProfile S hδ fun y hy =>
      (h0 y hy).trans (h0 z (mem_ball_self (by positivity))).symm,
    h0 z (mem_ball_self (by positivity))]

theorem cutoff_eq_one (S : Set ℂ) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : 3 * δ < infDist z Sᶜ) :
    cutoff S hδ z = 1 := by
  have h1 : ∀ y ∈ ball z (δ / 4), cutProfile S δ y = 1 := fun y hy => by
    refine ramp_eq_one hδ ?_
    have := infDist_le_infDist_add_dist (x := z) (y := y) (s := Sᶜ)
    rw [mem_ball, dist_comm] at hy
    linarith
  rw [cutoff_eq_cutProfile S hδ fun y hy =>
      (h1 y hy).trans (h1 z (mem_ball_self (by positivity))).symm,
    h1 z (mem_ball_self (by positivity))]

theorem abs_one_sub_cutoff_le (S : Set ℂ) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    |1 - cutoff S hδ z| ≤ 5 / 4 := by
  have h := (cutBump hδ).dist_normed_convolution_le (μ := volume) (x₀ := z) (ε := 1 / 4)
    (continuous_cutProfile S δ).aestronglyMeasurable fun y hy => by
      rw [Real.dist_eq]
      refine (abs_cutProfile_sub_le S hδ y z).trans ?_
      have : dist y z < δ / 4 := hy
      rw [one_div_mul_eq_div, div_le_iff₀ hδ]
      linarith
  rw [Real.dist_eq] at h
  have hm := ramp_mem_Icc δ (infDist z Sᶜ)
  change |cutoff S hδ z - cutProfile S δ z| ≤ 1 / 4 at h
  rw [abs_le] at h ⊢
  unfold cutProfile at h
  constructor <;> linarith [hm.1, hm.2]

theorem norm_fderiv_cutoff_le (S : Set ℂ) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ‖fderiv ℝ (fun w => (cutoff S hδ w : ℂ)) z‖ ≤ 1 / δ := by
  have hlip : LipschitzWith (Real.toNNReal (1 / δ)) (fun w => (cutoff S hδ w : ℂ)) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs,
        Real.coe_toNNReal _ (by positivity)]
      exact abs_cutoff_sub_le S hδ x y
  have := norm_fderiv_le_of_lipschitz ℝ (x₀ := z) hlip
  rwa [Real.coe_toNNReal _ (by positivity)] at this

/-! ### `∂̄` calculus -/

open Azurite.JordanCurve

theorem norm_dbar_le (u : ℂ → ℂ) (p : ℂ) : ‖dbar u p‖ ≤ ‖fderiv ℝ u p‖ := by
  unfold dbar
  have h1 : ‖fderiv ℝ u p 1‖ ≤ ‖fderiv ℝ u p‖ := by
    simpa using (fderiv ℝ u p).le_opNorm 1
  have h2 : ‖fderiv ℝ u p I‖ ≤ ‖fderiv ℝ u p‖ := by
    simpa using (fderiv ℝ u p).le_opNorm I
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  have := norm_add_le (fderiv ℝ u p 1) (I * fderiv ℝ u p I)
  rw [norm_mul, norm_I, one_mul] at this
  linarith

theorem dbar_sub {u v : ℂ → ℂ} {p : ℂ} (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) : dbar (fun z => u z - v z) p = dbar u p - dbar v p := by
  simp only [dbar, fderiv_fun_sub hu hv, FunLike.coe_sub, Pi.sub_apply]
  ring

theorem dbar_mul {u v : ℂ → ℂ} {p : ℂ} (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    dbar (fun z => u z * v z) p = u p * dbar v p + v p * dbar u p := by
  simp only [dbar, fderiv_fun_mul hu hv, FunLike.coe_add, Pi.add_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem dbar_congr {u v : ℂ → ℂ} {p : ℂ} (h : u =ᶠ[𝓝 p] v) : dbar u p = dbar v p := by
  simp only [dbar, h.fderiv_eq]

/-! ### Geometry of the interior -/

/-- A point of an open set `S` at distance `< r` from `Sᶜ` is within `r` of the boundary set
`C` whenever `closure S ⊆ S ∪ C`. -/
theorem mem_thickening_of_infDist_compl_lt {S C : Set ℂ} (hS : IsOpen S)
    (hcl : closure S ⊆ S ∪ C) (hne : Sᶜ.Nonempty) {z : ℂ} (hz : z ∈ S) {r : ℝ}
    (hzr : infDist z Sᶜ < r) : z ∈ thickening r C := by
  obtain ⟨q, hq, hdist⟩ := hS.isClosed_compl.exists_infDist_eq_dist hne z
  have hd : 0 < dist z q := by
    rw [dist_pos]
    rintro rfl
    exact hq hz
  have hqcl : q ∈ closure S := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set d := dist z q
    set t := min (ε / (2 * d)) 1 with ht
    have ht0 : 0 < t := lt_min (by positivity) one_pos
    have ht1 : t ≤ 1 := min_le_right _ _
    have htd : t * d ≤ ε / 2 := by
      have : t ≤ ε / (2 * d) := min_le_left _ _
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    refine ⟨q + t * (z - q), ?_, ?_⟩
    · apply ball_infDist_compl_subset (x := z)
      rw [mem_ball, hdist, dist_comm, dist_eq_norm,
        show z - (q + t * (z - q)) = ((1 - t : ℝ) : ℂ) * (z - q) by push_cast; ring, norm_mul,
        norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), ← dist_eq_norm]
      nlinarith
    · rw [dist_eq_norm, show q - (q + t * (z - q)) = -((t : ℂ) * (z - q)) by ring, norm_neg,
        norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht0, ← dist_eq_norm]
      linarith
  rcases hcl hqcl with h | h
  · exact absurd h hq
  · exact mem_thickening_iff.mpr ⟨q, h, hdist ▸ hzr⟩

end Azurite.DLMF

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

open Azurite.DLMF

theorem norm_windingNumber_le (hJ : IsJordanCurve c a b) {p : ℂ} (hp : p ∉ P.curve) :
    ‖(P.windingNumber p : ℂ)‖ ≤ 1 ∧ (p ∉ jordanInterior c a b → P.windingNumber p = 0) := by
  obtain ⟨w, hw, hall⟩ := P.exists_windingNumber_eq_one_or_neg_one hJ
  rcases (compl_image_eq_union (c := c) (a := a) (b := b)).subset hp with h | h
  · refine ⟨?_, fun h' => absurd h h'⟩
    rw [hall p h]
    rcases hw with rfl | rfl <;> simp
  · have h0 := P.windingNumber_eq_zero_of_mem_jordanExterior h
    exact ⟨by simp [h0], fun _ => h0⟩

/-- **The key estimate.** For `f` analytic inside a Jordan curve and a `C¹` function `φ` within
`ε` of `f` inside, `‖∮ φ‖ ≤ 2 ((5/4) S + ε/δ) · |{dist(·, C) < 4δ}|`, where `S` bounds `‖Dφ‖`
inside.  (Green's theorem for `φ − h·(φ − f)`, with `h` the cutoff of width `δ`.) -/
theorem norm_contourIntegral_le_of_near (hJ : IsJordanCurve c a b) {f φ : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b)) (hφ : ContDiff ℝ 1 φ) {ε S δ : ℝ}
    (hε : 0 ≤ ε) (hS0 : 0 ≤ S) (hδ : 0 < δ)
    (happrox : ∀ z ∈ jordanInterior c a b, ‖φ z - f z‖ ≤ ε)
    (hSφ : ∀ z ∈ jordanInterior c a b, ‖fderiv ℝ φ z‖ ≤ S) :
    ‖P.contourIntegral φ‖ ≤
      2 * ((5 / 4 * S + ε / δ) * (volume (thickening (4 * δ) P.curve)).toReal) := by
  classical
  set D := jordanInterior c a b with hD
  have hDo : IsOpen D := isOpen_jordanInterior hJ.continuousOn
  set h := cutoff D hδ with hh
  have hhc : ContDiff ℝ 1 fun w => (h w : ℂ) := ofRealCLM.contDiff.comp (contDiff_cutoff D hδ)
  set u : ℂ → ℂ := fun z => if z ∈ D then (h z : ℂ) * (φ z - f z) else 0 with hu
  have hfc : ∀ z ∈ D, ContDiffAt ℝ 1 f z := fun z hz =>
    (((hfd.contDiffOn (n := 1) hDo).contDiffAt (hDo.mem_nhds hz)).restrict_scalars ℝ)
  have hcompl0 : ∀ z ∉ D, infDist z Dᶜ = 0 := fun z hz => infDist_zero_of_mem hz
  have hopen_near : ∀ r, IsOpen {w : ℂ | infDist w Dᶜ < r} := fun r =>
    isOpen_lt (continuous_infDist_pt _) continuous_const
  have hu_out : ∀ z, infDist z Dᶜ < δ / 2 → u =ᶠ[𝓝 z] 0 := fun z hz =>
    eventually_of_mem ((hopen_near _).mem_nhds hz) fun w hw => by
      have h0 : h w = 0 := cutoff_eq_zero D hδ hw
      simp only [hu, Pi.zero_apply, h0, ofReal_zero, zero_mul, ite_self]
  have hu_in : ∀ z ∈ D, u =ᶠ[𝓝 z] fun w => (h w : ℂ) * (φ w - f w) := fun z hz =>
    eventually_of_mem (hDo.mem_nhds hz) fun w hw => by simp only [hu, hw, ↓reduceIte]
  have huc : ContDiff ℝ 1 u := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ D
    · exact (hhc.contDiffAt.mul (hφ.contDiffAt.sub (hfc z hz))).congr_of_eventuallyEq
        (hu_in z hz)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (hu_out z (by rw [hcompl0 z hz]; positivity))
  have hcurveD : ∀ z ∈ P.curve, z ∉ D := fun z hz hzD => jordanInterior_subset hzD hz
  have hgreen : P.contourIntegral φ = 2 * I * ∫ p, dbar (fun z => φ z - u z) p *
      (P.windingNumber p : ℂ) := by
    rw [← P.contourIntegral_eq_integral_dbar' (hφ.sub huc)]
    refine P.contourIntegral_congr fun z hz => ?_
    simp only [hu, hcurveD z hz, ↓reduceIte, sub_zero]
  set T := thickening (4 * δ) P.curve with hT
  set M := 5 / 4 * S + ε / δ with hM
  have hM0 : 0 ≤ M := by positivity
  have hne : Dᶜ.Nonempty := ⟨c a, hcurveD _ ⟨a, ⟨le_rfl, P.a_le_b⟩, rfl⟩⟩
  have hbound : ∀ᵐ p ∂volume, ‖dbar (fun z => φ z - u z) p * (P.windingNumber p : ℂ)‖ ≤
      T.indicator (fun _ => M) p := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp P.volume_curve] with p hp
    obtain ⟨hW1, hW0⟩ := P.norm_windingNumber_le hJ hp
    by_cases hpD : p ∉ D
    · rw [hW0 hpD]
      simp only [Int.cast_zero, mul_zero, norm_zero]
      exact indicator_nonneg (fun _ _ => hM0) p
    push Not at hpD
    have hfp : DifferentiableAt ℂ f p := hfd.differentiableAt (hDo.mem_nhds hpD)
    by_cases hfar : 3 * δ < infDist p Dᶜ
    · have hev : (fun z => φ z - u z) =ᶠ[𝓝 p] f := by
        filter_upwards [hDo.mem_nhds hpD, isOpen_lt continuous_const (continuous_infDist_pt Dᶜ)
          |>.mem_nhds hfar] with w hwD hw
        simp only [hu, hwD, ↓reduceIte, hh, cutoff_eq_one D hδ hw, ofReal_one, one_mul]
        ring
      rw [dbar_congr hev, Azurite.DLMF.dbar_eq_zero hfp EventuallyEq.rfl, zero_mul, norm_zero]
      exact indicator_nonneg (fun _ _ => hM0) p
    push Not at hfar
    have hpT : p ∈ T := mem_thickening_of_infDist_compl_lt hDo
      (closure_jordanInterior_subset hJ.continuousOn) hne hpD (by linarith)
    rw [indicator_of_mem hpT]
    have hφd : DifferentiableAt ℝ φ p := hφ.differentiable one_ne_zero p
    have hfd' : DifferentiableAt ℝ f p := hfp.restrictScalars ℝ
    have hhd : DifferentiableAt ℝ (fun w => (h w : ℂ)) p := hhc.differentiable one_ne_zero p
    have hev : (fun z => φ z - u z) =ᶠ[𝓝 p] fun z => φ z - (h z : ℂ) * (φ z - f z) := by
      filter_upwards [hu_in p hpD] with w hw
      rw [hw]
    have hval : dbar (fun z => φ z - u z) p =
        (1 - h p) * dbar φ p - (φ p - f p) * dbar (fun w => (h w : ℂ)) p := by
      rw [dbar_congr hev, dbar_sub (u := φ) (v := fun z => (h z : ℂ) * (φ z - f z)) hφd
          (hhd.mul (hφd.sub hfd')),
        dbar_mul (u := fun w => (h w : ℂ)) (v := fun z => φ z - f z) hhd (hφd.sub hfd'),
        dbar_sub (u := φ) (v := f) hφd hfd', Azurite.DLMF.dbar_eq_zero hfp EventuallyEq.rfl]
      ring
    rw [hval, norm_mul]
    have hA : ‖(1 - (h p : ℂ)) * dbar φ p‖ ≤ 5 / 4 * S := by
      rw [norm_mul, show (1 - (h p : ℂ)) = ((1 - h p : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs]
      exact mul_le_mul (abs_one_sub_cutoff_le D hδ p)
        ((norm_dbar_le _ _).trans (hSφ p hpD)) (norm_nonneg _) (by norm_num)
    have hB : ‖(φ p - f p) * dbar (fun w => (h w : ℂ)) p‖ ≤ ε / δ := by
      rw [norm_mul, div_eq_mul_one_div]
      exact mul_le_mul (happrox p hpD)
        ((norm_dbar_le _ _).trans (norm_fderiv_cutoff_le D hδ p)) (norm_nonneg _) hε
    calc ‖(1 - (h p : ℂ)) * dbar φ p - (φ p - f p) * dbar (fun w => (h w : ℂ)) p‖ *
          ‖(P.windingNumber p : ℂ)‖
        ≤ (5 / 4 * S + ε / δ) * 1 :=
          mul_le_mul ((norm_sub_le _ _).trans (add_le_add hA hB)) hW1 (norm_nonneg _) hM0
      _ = M := mul_one _
  have hTfin : volume T ≠ ⊤ := (P.isCompact_curve.isBounded.thickening).measure_lt_top.ne
  have hTm : MeasurableSet T := isOpen_thickening.measurableSet
  have hint : Integrable (T.indicator fun _ => M) :=
    (integrableOn_const hTfin).integrable_indicator hTm
  rw [hgreen, norm_mul, show ‖(2 : ℂ) * I‖ = 2 by simp]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_of_norm_le hint hbound).trans_eq ?_)
    zero_le_two
  rw [integral_indicator_const _ hTm, smul_eq_mul, measureReal_def, mul_comm]

theorem isCompact_jordanInterior_union (hJ : IsJordanCurve c a b) :
    IsCompact (jordanInterior c a b ∪ P.curve) := by
  obtain ⟨M, hM⟩ := P.isCompact_curve.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_of_closure_subset ?_) ?_
  · rw [closure_union]
    rintro z (hz | hz)
    · exact closure_jordanInterior_subset hJ.continuousOn hz
    · exact Or.inr (P.isCompact_curve.isClosed.closure_subset hz)
  · exact (isBounded_closedBall.subset (jordanInterior_subset_closedBall (le_max_right M 0)
      (hM.trans (closedBall_subset_closedBall (le_max_left M 0))))).union
      P.isCompact_curve.isBounded

theorem length_nonneg : 0 ≤ P.length :=
  Finset.sum_nonneg fun i hi => intervalIntegral.integral_nonneg
    (P.lt i (Finset.mem_range.mp hi)).le fun _ _ => norm_nonneg _

/-- **Cauchy's theorem with boundary continuity**: for a Jordan curve `C` and `f` continuous
on `C` and its interior, analytic in the interior, `∮_C f dz = 0`. -/
theorem contourIntegral_eq_zero_of_continuousOn (hJ : IsJordanCurve c a b) {f : ℂ → ℂ}
    (hfc : ContinuousOn f (jordanInterior c a b ∪ P.curve))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b)) : P.contourIntegral f = 0 := by
  have hK := P.isCompact_jordanInterior_union hJ
  obtain ⟨A, hA0, hA⟩ := P.exists_volume_thickening_le
  have hL0 := P.length_nonneg
  set B := P.length + 8 * A + 1 with hBdef
  have hB : 0 < B := by positivity
  have key : ∀ ε > 0, ‖P.contourIntegral f‖ ≤ B * ε := by
    intro ε hε
    obtain ⟨φ, hφ, hφf⟩ := exists_contDiff_near hK hfc hε
    obtain ⟨S₀, hS₀⟩ :=
      hK.exists_bound_of_continuousOn (hφ.continuous_fderiv one_ne_zero).continuousOn
    set S := max S₀ 0 with hSdef
    have hS0 : 0 ≤ S := le_max_right _ _
    set δ := min (1 / 4) (ε / (10 * S * A + 1)) with hδdef
    have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ1 : 4 * δ ≤ 1 := by
      have := min_le_left (1 / 4 : ℝ) (ε / (10 * S * A + 1))
      linarith
    have hδε : 10 * S * A * δ ≤ ε := by
      have h1 : δ ≤ ε / (10 * S * A + 1) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    have hvol : (volume (thickening (4 * δ) P.curve)).toReal ≤ A * (4 * δ) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hA _ (by positivity) hδ1)
    have hφbound := P.norm_contourIntegral_le_of_near hJ hfd hφ hε.le hS0 hδ
      (fun z hz => hφf z (Or.inl hz)) fun z hz => (hS₀ z (Or.inl hz)).trans (le_max_left _ _)
    have hdiff : ‖P.contourIntegral (fun z => f z - φ z)‖ ≤ P.length * ε :=
      P.norm_contourIntegral_le fun z hz => by
        rw [norm_sub_rev]
        exact hφf z (Or.inr hz)
    have hsplit : P.contourIntegral f =
        P.contourIntegral (fun z => f z - φ z) + P.contourIntegral φ := by
      rw [P.contourIntegral_sub (hfc.mono subset_union_right) hφ.continuous.continuousOn]
      ring
    have hM : 0 ≤ 5 / 4 * S + ε / δ := by positivity
    have hφbound' : ‖P.contourIntegral φ‖ ≤ 2 * ((5 / 4 * S + ε / δ) * (A * (4 * δ))) :=
      hφbound.trans (by gcongr)
    have hexp : 2 * ((5 / 4 * S + ε / δ) * (A * (4 * δ))) = 10 * S * A * δ + 8 * A * ε := by
      field_simp
      ring
    have hBε : B * ε = P.length * ε + 8 * A * ε + ε := by rw [hBdef]; ring
    rw [hsplit]
    linarith [norm_add_le (P.contourIntegral (fun z => f z - φ z)) (P.contourIntegral φ)]
  by_contra hne
  have hpos : 0 < ‖P.contourIntegral f‖ := norm_pos_iff.mpr hne
  have h1 := key (‖P.contourIntegral f‖ / (2 * B)) (by positivity)
  have h2 : B * (‖P.contourIntegral f‖ / (2 * B)) = ‖P.contourIntegral f‖ / 2 := by
    field_simp
  linarith

theorem continuousOn_dslope_of_continuousOn (hJ : IsJordanCurve c a b) {f : ℂ → ℂ}
    (hfc : ContinuousOn f (jordanInterior c a b ∪ P.curve))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ jordanInterior c a b) :
    ContinuousOn (dslope f z₀) (jordanInterior c a b ∪ P.curve) := by
  intro z hz
  by_cases hzz : z = z₀
  · subst hzz
    exact (continuousAt_dslope_same.mpr (hfd.differentiableAt
      ((isOpen_jordanInterior hJ.continuousOn).mem_nhds hz₀))).continuousWithinAt
  · exact (continuousWithinAt_dslope_of_ne hzz).mpr (hfc z hz)

/-- **Cauchy's integral formula with boundary continuity** (winding-number form). -/
theorem contourIntegral_div_sub_of_continuousOn (hJ : IsJordanCurve c a b) {f : ℂ → ℂ}
    (hfc : ContinuousOn f (jordanInterior c a b ∪ P.curve))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ jordanInterior c a b) :
    P.contourIntegral (fun z => f z / (z - z₀)) = 2 * π * I * P.windingNumber z₀ * f z₀ := by
  have hp : z₀ ∉ P.curve := hz₀.1
  have hDo := isOpen_jordanInterior hJ.continuousOn
  have hG : DifferentiableOn ℂ (dslope f z₀) (jordanInterior c a b) :=
    (differentiableOn_dslope (hDo.mem_nhds hz₀)).mpr hfd
  have hGc := P.continuousOn_dslope_of_continuousOn hJ hfc hfd hz₀
  have heq : EqOn (fun z => f z / (z - z₀)) (fun z => dslope f z₀ z + f z₀ * ((z - z₀) ^ 1)⁻¹)
      P.curve := by
    intro z hz
    have hzp : z ≠ z₀ := fun h => hp (h ▸ hz)
    have hne := P.sub_ne_zero_of_mem_curve hp hz
    simp only [dslope_of_ne _ hzp, slope_def_field, pow_one]
    field_simp
    ring
  rw [P.contourIntegral_congr heq, P.contourIntegral_add (f₁ := dslope f z₀)
      (f₂ := fun z => f z₀ * ((z - z₀) ^ 1)⁻¹) (hGc.mono subset_union_right)
      (continuousOn_const.mul (P.continuousOn_inv_sub_pow hp 1)),
    P.contourIntegral_eq_zero_of_continuousOn hJ hGc hG, P.contourIntegral_const_mul]
  simp only [pow_one]
  rw [P.contourIntegral_inv_eq hp]
  ring

/-- **Cauchy's integral formula for derivatives with boundary continuity**. -/
theorem contourIntegral_div_sub_pow_of_continuousOn (hJ : IsJordanCurve c a b) {z₀ : ℂ}
    (hz₀ : z₀ ∈ jordanInterior c a b) (n : ℕ) {f : ℂ → ℂ}
    (hfc : ContinuousOn f (jordanInterior c a b ∪ P.curve))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b)) :
    P.contourIntegral (fun z => f z / (z - z₀) ^ (n + 1)) =
      2 * π * I * P.windingNumber z₀ * (iteratedDeriv n f z₀ / n.factorial) := by
  have hp : z₀ ∉ P.curve := hz₀.1
  have hDo := isOpen_jordanInterior hJ.continuousOn
  induction n generalizing f with
  | zero => simpa using P.contourIntegral_div_sub_of_continuousOn hJ hfc hfd hz₀
  | succ n ih =>
    have hG : DifferentiableOn ℂ (dslope f z₀) (jordanInterior c a b) :=
      (differentiableOn_dslope (hDo.mem_nhds hz₀)).mpr hfd
    have hGc := P.continuousOn_dslope_of_continuousOn hJ hfc hfd hz₀
    have heq : EqOn (fun z => f z / (z - z₀) ^ (n + 1 + 1))
        (fun z => dslope f z₀ z / (z - z₀) ^ (n + 1) + f z₀ * ((z - z₀) ^ (n + 2))⁻¹)
        P.curve := by
      intro z hz
      have hzp : z ≠ z₀ := fun h => hp (h ▸ hz)
      have hne := P.sub_ne_zero_of_mem_curve hp hz
      simp only [dslope_of_ne _ hzp, slope_def_field]
      field_simp
      ring
    have hc1 : ContinuousOn (fun z => dslope f z₀ z / (z - z₀) ^ (n + 1)) P.curve :=
      (hGc.mono subset_union_right).div ((continuous_sub_right z₀).pow _).continuousOn
        fun z hz => pow_ne_zero _ (P.sub_ne_zero_of_mem_curve hp hz)
    rw [P.contourIntegral_congr heq, P.contourIntegral_add
        (f₂ := fun z => f z₀ * ((z - z₀) ^ (n + 2))⁻¹) hc1
        (continuousOn_const.mul (P.continuousOn_inv_sub_pow hp _)),
      ih hGc hG, P.contourIntegral_const_mul, P.contourIntegral_inv_pow_eq_zero hp,
      Azurite.DLMF.iteratedDeriv_succ_eq_dslope (hDo.mem_nhds hz₀) hfd, Nat.factorial_succ]
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn1 : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
    push_cast
    field_simp
    ring

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

open Azurite.JordanCurve

variable {c : ℝ → ℂ} {a b : ℝ}

/-- **DLMF 1.9.29** (Cauchy's theorem) under DLMF's hypotheses: `C` a simple closed contour,
`f` continuous within and on `C` and analytic within `C`. -/
theorem dlmf_1_9_29_jordan (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    {f : ℂ → ℂ} (hfc : ContinuousOn f (jordanInterior c a b ∪ c '' Icc a b))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b)) : contourIntegral f c a b = 0 := by
  rw [← P.contourIntegral_eq (hfc.mono subset_union_right)]
  exact P.contourIntegral_eq_zero_of_continuousOn hJ hfc hfd

/-- **DLMF 1.9.30** (Cauchy's integral formula) under DLMF's hypotheses. -/
theorem dlmf_1_9_30_jordan (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ}
    (hfc : ContinuousOn f (jordanInterior c a b ∪ c '' Icc a b))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ jordanInterior c a b) :
    f z₀ = 1 / (2 * π * I) * contourIntegral (fun z => f z / (z - z₀)) c a b := by
  have hc : ContinuousOn (fun z => f z / (z - z₀)) P.curve :=
    (hfc.mono subset_union_right).div (continuousOn_id.sub continuousOn_const)
      fun _ hz => P.sub_ne_zero_of_mem_curve hz₀.1 hz
  rw [← P.contourIntegral_eq hc, P.contourIntegral_div_sub_of_continuousOn hJ hfc hfd hz₀,
    hpos z₀ hz₀, Int.cast_one, mul_one, one_div, inv_mul_cancel_left₀ two_pi_I_ne_zero]

/-- **DLMF 1.9.31** (Cauchy's integral formula for derivatives) under DLMF's hypotheses. -/
theorem dlmf_1_9_31_jordan (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ}
    (hfc : ContinuousOn f (jordanInterior c a b ∪ c '' Icc a b))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ jordanInterior c a b) (n : ℕ) :
    iteratedDeriv n f z₀ = n.factorial / (2 * π * I) *
      contourIntegral (fun z => f z / (z - z₀) ^ (n + 1)) c a b := by
  have hc : ContinuousOn (fun z => f z / (z - z₀) ^ (n + 1)) P.curve :=
    (hfc.mono subset_union_right).div ((continuous_sub_right z₀).pow _).continuousOn
      fun _ hz => pow_ne_zero _ (P.sub_ne_zero_of_mem_curve hz₀.1 hz)
  rw [← P.contourIntegral_eq hc, P.contourIntegral_div_sub_pow_of_continuousOn hJ hz₀ n hfc hfd,
    hpos z₀ hz₀, Int.cast_one, mul_one]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 := two_pi_I_ne_zero
  field_simp

end Azurite.DLMF
