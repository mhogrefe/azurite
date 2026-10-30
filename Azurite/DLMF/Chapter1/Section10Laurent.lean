/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9Series
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# DLMF §1.10(iii): Laurent Series

Formalizations of <https://dlmf.nist.gov/1.10.iii> (Mathlib has no Laurent expansion theorem).

* Cauchy's formula on an annulus: `two_pi_I_mul_eq_annulus` (via `dslope` and Mathlib's annulus
  form of Cauchy's theorem), with the inner geometric expansion `hasSum_inner_laurent` (the outer
  one is Mathlib's `hasSum_two_pi_I_cauchyPowerSeries_integral`).
* 1.10.7: `laurentCoeff` (`aₙ = (2πi)⁻¹ ∮ f(z)/(z − z₀)^{n+1} dz`), `laurentCoeff_eq`
  (independent of `r ∈ (r₁, r₂)`), `norm_laurentCoeff_le` (Cauchy's estimate).
* 1.10.6: `annulus`, `hasSum_laurent` (both halves), `dlmf_1_10_6` (as a doubly-infinite series,
  §1.9(v)), `dlmf_1_10_6_uniform` (uniform on closed sub-annuli, both halves absolutely convergent),
  `dlmf_1_10_6_compact` (uniform on compact sets).  For `r₂ = ∞` apply these with any finite
  `r₂ > |z − z₀|`.
* Isolated singularities (`r₁ = 0`, coefficients on `|z − z₀| = R/2`): `IsIsolatedSingularity`,
  `IsRemovableSingularity`, `IsPoleOfOrder`, `IsPole`, `IsEssentialSingularity`; `isPole_iff`
  (finitely many, at least one, nonzero negative coefficients), `singularity_trichotomy`,
  `IsRemovableSingularity.hasSum` (the Laurent series is the Taylor series),
  `isRemovableSingularity_of_tendsto` (removable when `lim_{z→z₀} f(z)` exists),
  `sin_div_removable` (`(sin z)/z` at `0`); `residue`, `residue_eq`; `IsMeromorphicDLMF`;
  singularities at infinity via `f(1/z)` (`IsRemovableSingularityAtInfty`, `IsPoleOfOrderAtInfty`,
  `IsEssentialSingularityAtInfty`).
* Picard's theorem and the naming of `∞` as an essential singularity of a meromorphic function
  with infinitely many poles: `Section10Picard.lean`.
-/

open Filter Topology Set Metric Complex MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-! ### Cauchy's formula on an annulus -/

/-- The inner geometric expansion: for `|w − c| = R < |u|`,
`∮ (c + u − w)⁻¹ f(w) dw = ∑ₙ ∮ (w − c)ⁿ/u^{n+1} f(w) dw`. -/
theorem hasSum_inner_laurent {f : ℂ → ℂ} {c u : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
    (hR : 0 < R) (hu : R < ‖u‖) :
    HasSum (fun n : ℕ => ∮ w in C(c, R), (w - c) ^ n / u ^ (n + 1) * f w)
      (∮ w in C(c, R), (c + u - w)⁻¹ * f w) := by
  have hu0 : 0 < ‖u‖ := hR.trans hu
  have hu0' : u ≠ 0 := norm_pos_iff.mp hu0
  set q := R / ‖u‖ with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one hu0).2 hu
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => ‖f (circleMap c R θ)‖ * (q * q ^ n)) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · have h1 : Measurable fun θ : ℝ => deriv (circleMap c R) θ := by
      simp only [deriv_circleMap]; fun_prop
    have h2 : Measurable fun θ : ℝ => (circleMap c R θ - c) ^ n / u ^ (n + 1) := by fun_prop
    exact h1.aestronglyMeasurable.smul (h2.aestronglyMeasurable.mul hf.def'.1)
  · refine Eventually.of_forall fun θ _ => le_of_eq ?_
    rw [deriv_circleMap, smul_eq_mul, norm_mul, norm_mul, norm_mul, norm_div, norm_pow, norm_pow,
      circleMap_sub_center, norm_circleMap_zero, norm_I, abs_of_pos hR, hqdef, div_pow]
    field_simp
    ring
  · exact Eventually.of_forall fun θ _ =>
      ((summable_geometric_of_lt_one hq0 hq1).mul_left q).mul_left _
  · simpa only [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1] using
      hf.norm.mul_continuousOn continuousOn_const
  · refine Eventually.of_forall fun θ _ => ?_
    set w := circleMap c R θ
    have hw : ‖(w - c) / u‖ < 1 := by
      rw [norm_div, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]
      exact hq1
    have hne : (1 : ℂ) - (w - c) / u ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [← h, norm_one] at hw
      exact lt_irrefl _ hw
    have h := ((hasSum_geometric_of_norm_lt_one hw).mul_right (u⁻¹ * f w)).mul_left
      (deriv (circleMap c R) θ)
    convert h using 1
    · funext n
      rw [smul_eq_mul, div_pow, pow_succ]
      field_simp
    · rw [smul_eq_mul]
      congr 1
      have hne' : c + u - w ≠ 0 := by
        intro h0
        apply hne
        rw [show w - c = u by linear_combination -h0, div_self hu0', sub_self]
      rw [← mul_assoc, ← mul_inv, sub_mul, one_mul, div_mul_cancel₀ _ hu0',
        show u - (w - c) = c + u - w by ring]

/-- **Cauchy's integral formula on an annulus**: for `f` analytic on the closed annulus
`ρ₁ ≤ |w − c| ≤ ρ₂` and `ρ₁ < |z − c| < ρ₂`,
`2πi f(z) = ∮_{ρ₂} f(w)/(w − z) dw + ∮_{ρ₁} f(w)/(z − w) dw`. -/
theorem two_pi_I_mul_eq_annulus {f : ℂ → ℂ} {c z : ℂ} {ρ₁ ρ₂ : ℝ} (h0 : 0 < ρ₁)
    (h1 : ρ₁ < ‖z - c‖) (h2 : ‖z - c‖ < ρ₂)
    (hf : DifferentiableOn ℂ f (closedBall c ρ₂ \ ball c ρ₁)) :
    2 * π * I * f z = (∮ w in C(c, ρ₂), (w - z)⁻¹ * f w) + ∮ w in C(c, ρ₁), (z - w)⁻¹ * f w := by
  have hzA : z ∈ ball c ρ₂ \ closedBall c ρ₁ := by
    rw [Set.mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm, not_le]
    exact ⟨h2, h1⟩
  have hnhds : closedBall c ρ₂ \ ball c ρ₁ ∈ 𝓝 z := by
    refine mem_of_superset ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hzA) ?_
    exact sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall
  have hfz : DifferentiableAt ℂ f z := hf.differentiableAt hnhds
  set g := dslope f z
  have hgc : ContinuousOn g (closedBall c ρ₂ \ ball c ρ₁) := by
    intro w hw
    by_cases hwz : w = z
    · subst hwz
      exact (continuousAt_dslope_same.mpr hfz).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne hwz).mpr (hf.continuousOn w hw)
  have hgd : ∀ w ∈ (ball c ρ₂ \ closedBall c ρ₁) \ {z}, DifferentiableAt ℂ g w := by
    rintro w ⟨hw, hwz⟩
    have hwn : closedBall c ρ₂ \ ball c ρ₁ ∈ 𝓝 w := by
      refine mem_of_superset ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hw) ?_
      exact sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall
    exact (differentiableAt_dslope_of_ne hwz).mpr (hf.differentiableAt hwn)
  have hann := circleIntegral_eq_of_differentiable_on_annulus_off_countable h0
    (h1.trans h2).le (countable_singleton z) hgc hgd
  -- `g = (w − z)⁻¹ (f w − f z)` on both circles
  have hsph : ∀ ρ, ρ = ρ₁ ∨ ρ = ρ₂ → EqOn g (fun w => (w - z)⁻¹ * f w - f z * (w - z)⁻¹)
      (sphere c ρ) := by
    intro ρ hρ w hw
    have hwz : w ≠ z := by
      rintro rfl
      rw [mem_sphere, dist_eq_norm] at hw
      rcases hρ with rfl | rfl <;> linarith
    simp only [g, dslope_of_ne _ hwz, slope_def_field]
    rw [div_eq_inv_mul]
    ring
  have hcont : ∀ ρ, 0 < ρ → ρ = ρ₁ ∨ ρ = ρ₂ → ContinuousOn f (sphere c ρ) := by
    intro ρ hρ0 hρ w hw
    refine (hf.continuousOn w ?_).mono ?_
    · rw [mem_sphere] at hw
      rw [Set.mem_sdiff, mem_closedBall, mem_ball, not_lt]
      rcases hρ with rfl | rfl <;> constructor <;> linarith
    · intro x hx
      rw [mem_sphere] at hx
      rw [Set.mem_sdiff, mem_closedBall, mem_ball, not_lt]
      rcases hρ with rfl | rfl <;> constructor <;> linarith
  have hinvc : ∀ ρ, 0 < ρ → ρ = ρ₁ ∨ ρ = ρ₂ → ContinuousOn (fun w => (w - z)⁻¹) (sphere c ρ) := by
    intro ρ _ hρ w hw
    refine ((continuous_sub_right z).continuousAt.inv₀ ?_).continuousWithinAt
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0, mem_sphere, dist_eq_norm] at hw
    rcases hρ with rfl | rfl <;> linarith
  have hint : ∀ ρ, 0 < ρ → ρ = ρ₁ ∨ ρ = ρ₂ →
      (∮ w in C(c, ρ), g w) = (∮ w in C(c, ρ), (w - z)⁻¹ * f w) -
        f z * ∮ w in C(c, ρ), (w - z)⁻¹ := by
    intro ρ hρ0 hρ
    rw [circleIntegral.integral_congr hρ0.le (hsph ρ hρ), circleIntegral.integral_sub,
      circleIntegral.integral_const_mul]
    · exact ((hinvc ρ hρ0 hρ).mul (hcont ρ hρ0 hρ)).circleIntegrable hρ0.le
    · exact (continuousOn_const.mul (hinvc ρ hρ0 hρ)).circleIntegrable hρ0.le
  have hout : (∮ w in C(c, ρ₂), (w - z)⁻¹) = 2 * π * I :=
    circleIntegral.integral_sub_inv_of_mem_ball (by rw [mem_ball, dist_eq_norm]; exact h2)
  have hin : (∮ w in C(c, ρ₁), (w - z)⁻¹) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable h0.le countable_empty ?_ ?_
    · intro w hw
      refine ((continuous_sub_right z).continuousAt.inv₀ ?_).continuousWithinAt
      intro h00
      rw [sub_eq_zero] at h00
      rw [h00, mem_closedBall, dist_eq_norm] at hw
      linarith
    · intro w hw
      have hw' : w ∈ ball c ρ₁ := hw.1
      refine ((differentiableAt_id.sub_const z).inv ?_)
      intro h00
      rw [sub_eq_zero, id] at h00
      rw [h00, mem_ball, dist_eq_norm] at hw'
      linarith
  have hneg : (∮ w in C(c, ρ₁), (z - w)⁻¹ * f w) = -∮ w in C(c, ρ₁), (w - z)⁻¹ * f w := by
    rw [show -(∮ w in C(c, ρ₁), (w - z)⁻¹ * f w) = (-1) * ∮ w in C(c, ρ₁), (w - z)⁻¹ * f w by
      ring, ← circleIntegral.integral_const_mul]
    refine circleIntegral.integral_congr h0.le fun w _ => ?_
    show (z - w)⁻¹ * f w = -1 * ((w - z)⁻¹ * f w)
    rw [← neg_sub w z, inv_neg]
    ring
  rw [hint ρ₂ (h0.trans (h1.trans h2)) (Or.inr rfl), hint ρ₁ h0 (Or.inl rfl), hout, hin] at hann
  rw [hneg]
  linear_combination (-1 : ℂ) * hann

/-! ### Laurent coefficients -/

/-- The annulus `r₁ < |z − z₀| < r₂`. -/
def annulus (z₀ : ℂ) (r₁ r₂ : ℝ) : Set ℂ := {z | r₁ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r₂}

/-- **DLMF 1.10.7**: the Laurent coefficient `aₙ = (2πi)⁻¹ ∮_{|z−z₀|=r} f(z)/(z − z₀)^{n+1} dz`. -/
noncomputable def laurentCoeff (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n : ℤ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ z in C(z₀, r), f z / (z - z₀) ^ (n + 1)

theorem closedAnnulus_subset {z₀ : ℂ} {r₁ r₂ ρ₁ ρ₂ : ℝ} (h₁ : r₁ < ρ₁) (h₂ : ρ₂ < r₂) :
    closedBall z₀ ρ₂ \ ball z₀ ρ₁ ⊆ annulus z₀ r₁ r₂ := by
  intro w hw
  rw [Set.mem_sdiff, mem_closedBall, mem_ball, not_lt, dist_eq_norm] at hw
  exact ⟨by linarith [hw.2], by linarith [hw.1]⟩

theorem sub_ne_zero_of_mem_closedAnnulus {z₀ w : ℂ} {ρ₁ ρ₂ : ℝ} (h0 : 0 < ρ₁)
    (hw : w ∈ closedBall z₀ ρ₂ \ ball z₀ ρ₁) : w - z₀ ≠ 0 := by
  intro h
  rw [Set.mem_sdiff, mem_ball, dist_eq_norm, h, norm_zero] at hw
  exact hw.2 h0

/-- **DLMF 1.10.7**, independence of the radius: the coefficients are the same for every
`r ∈ (r₁, r₂)`. -/
theorem laurentCoeff_eq {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f (annulus z₀ r₁ r₂)) {r r' : ℝ} (hr : r ∈ Ioo r₁ r₂)
    (hr' : r' ∈ Ioo r₁ r₂) (n : ℤ) : laurentCoeff f z₀ r n = laurentCoeff f z₀ r' n := by
  have key : ∀ ρ ρ' : ℝ, ρ ∈ Ioo r₁ r₂ → ρ' ∈ Ioo r₁ r₂ → ρ ≤ ρ' →
      (∮ z in C(z₀, ρ'), f z / (z - z₀) ^ (n + 1)) = ∮ z in C(z₀, ρ), f z / (z - z₀) ^ (n + 1) := by
    intro ρ ρ' hρ hρ' hle
    have h0 : 0 < ρ := lt_of_le_of_lt hr₁ hρ.1
    have hsub := closedAnnulus_subset (z₀ := z₀) hρ.1 hρ'.2
    refine circleIntegral_eq_of_differentiable_on_annulus_off_countable h0 hle countable_empty
      ?_ ?_
    · intro w hw
      exact ((hf.continuousOn w (hsub hw)).mono hsub).div
        ((continuous_sub_right z₀).continuousAt.zpow₀ (n + 1)
          (Or.inl (sub_ne_zero_of_mem_closedAnnulus h0 hw))).continuousWithinAt
        (zpow_ne_zero _ (sub_ne_zero_of_mem_closedAnnulus h0 hw))
    · intro w hw
      have hw' : w ∈ closedBall z₀ ρ' \ ball z₀ ρ := by
        rw [Set.mem_sdiff] at hw ⊢
        exact ⟨ball_subset_closedBall hw.1.1, fun h => hw.1.2 (ball_subset_closedBall h)⟩
      have hne := sub_ne_zero_of_mem_closedAnnulus h0 hw'
      have hopen : IsOpen (annulus z₀ r₁ r₂) :=
        (isOpen_lt continuous_const (continuous_sub_right z₀).norm).inter
          (isOpen_lt (continuous_sub_right z₀).norm continuous_const)
      exact (hf.differentiableAt (hopen.mem_nhds (hsub hw'))).div
        ((differentiableAt_id.sub_const z₀).zpow (Or.inl hne)) (zpow_ne_zero _ hne)
  unfold laurentCoeff
  rcases le_total r r' with h | h
  · rw [key r r' hr hr' h]
  · rw [key r' r hr' hr h]

theorem isOpen_annulus (z₀ : ℂ) (r₁ r₂ : ℝ) : IsOpen (annulus z₀ r₁ r₂) :=
  (isOpen_lt continuous_const (continuous_sub_right z₀).norm).inter
    (isOpen_lt (continuous_sub_right z₀).norm continuous_const)

/-- The two halves of the Laurent expansion at a point of the annulus. -/
theorem hasSum_laurent {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f (annulus z₀ r₁ r₂)) {r : ℝ} (hr : r ∈ Ioo r₁ r₂) {z : ℂ}
    (hz : z ∈ annulus z₀ r₁ r₂) :
    ∃ S₁ S₂, HasSum (fun n : ℕ => laurentCoeff f z₀ r n * (z - z₀) ^ n) S₁ ∧
      HasSum (fun m : ℕ => laurentCoeff f z₀ r (-((m + 1 : ℕ) : ℤ)) *
        (z - z₀) ^ (-((m + 1 : ℕ) : ℤ))) S₂ ∧ S₁ + S₂ = f z := by
  set u := z - z₀ with hu
  obtain ⟨hz1, hz2⟩ := hz
  set ρ₁ := (r₁ + ‖u‖) / 2 with hρ₁
  set ρ₂ := (‖u‖ + r₂) / 2 with hρ₂
  have h0 : 0 < ρ₁ := by rw [hρ₁]; linarith
  have h1 : ρ₁ < ‖u‖ := by rw [hρ₁]; linarith
  have h2 : ‖u‖ < ρ₂ := by rw [hρ₂]; linarith
  have hρ₁m : ρ₁ ∈ Ioo r₁ r₂ := ⟨by rw [hρ₁]; linarith, by rw [hρ₁]; linarith⟩
  have hρ₂m : ρ₂ ∈ Ioo r₁ r₂ := ⟨by rw [hρ₂]; linarith, by rw [hρ₂]; linarith⟩
  have hsub := closedAnnulus_subset (z₀ := z₀) hρ₁m.1 hρ₂m.2
  have hcauchy := two_pi_I_mul_eq_annulus h0 h1 h2 (hf.mono hsub)
  have hsph : ∀ ρ ∈ Ioo r₁ r₂, CircleIntegrable f z₀ ρ := fun ρ hρ =>
    (hf.continuousOn.mono fun w hw => by
      rw [mem_sphere, dist_eq_norm] at hw
      exact ⟨by rw [hw]; exact hρ.1, by rw [hw]; exact hρ.2⟩).circleIntegrable
      (lt_of_le_of_lt hr₁ hρ.1).le
  have h2piI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  -- outer half
  have hout := hasSum_two_pi_I_cauchyPowerSeries_integral (hsph ρ₂ hρ₂m) h2
  have hout' : HasSum (fun n : ℕ => 2 * π * I * (laurentCoeff f z₀ r n * u ^ n))
      (∮ w in C(z₀, ρ₂), (w - z)⁻¹ * f w) := by
    rw [show z = z₀ + u by rw [hu]; ring]
    convert hout using 1
    · funext n
      rw [laurentCoeff_eq hr₁ hf hr hρ₂m, laurentCoeff]
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h2piI, one_mul, mul_comm,
        ← circleIntegral.integral_const_mul]
      refine circleIntegral.integral_congr (h0.trans (h1.trans h2)).le fun w hw => ?_
      have hne : w - z₀ ≠ 0 := by
        intro h
        rw [mem_sphere, dist_eq_norm, h, norm_zero] at hw
        linarith
      simp only [smul_eq_mul]
      rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, div_pow]
      field_simp
      ring
  -- inner half
  have hin := hasSum_inner_laurent (hsph ρ₁ hρ₁m) h0 h1
  have hin' : HasSum (fun m : ℕ => 2 * π * I * (laurentCoeff f z₀ r (-((m + 1 : ℕ) : ℤ)) *
      u ^ (-((m + 1 : ℕ) : ℤ)))) (∮ w in C(z₀, ρ₁), (z - w)⁻¹ * f w) := by
    rw [show z = z₀ + u by rw [hu]; ring]
    convert hin using 1
    funext m
    rw [laurentCoeff_eq hr₁ hf hr hρ₁m, laurentCoeff]
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h2piI, one_mul, mul_comm,
      ← circleIntegral.integral_const_mul]
    refine circleIntegral.integral_congr h0.le fun w hw => ?_
    have hne : w - z₀ ≠ 0 := by
      intro h
      rw [mem_sphere, dist_eq_norm, h, norm_zero] at hw
      linarith
    have hu0 : u ≠ 0 := norm_pos_iff.mp (h0.trans h1)
    rw [show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by push_cast; ring, zpow_neg, zpow_neg,
      zpow_natCast, zpow_natCast]
    field_simp
  have hA : HasSum (fun n : ℕ => laurentCoeff f z₀ r n * u ^ n)
      ((∮ w in C(z₀, ρ₂), (w - z)⁻¹ * f w) / (2 * π * I)) := by
    convert hout'.div_const (2 * π * I) using 1
    funext n
    field_simp
  have hB : HasSum (fun m : ℕ => laurentCoeff f z₀ r (-((m + 1 : ℕ) : ℤ)) *
      u ^ (-((m + 1 : ℕ) : ℤ))) ((∮ w in C(z₀, ρ₁), (z - w)⁻¹ * f w) / (2 * π * I)) := by
    convert hin'.div_const (2 * π * I) using 1
    funext m
    field_simp
  refine ⟨_, _, hA, hB, ?_⟩
  rw [← add_div, ← hcauchy]
  field_simp

/-- **DLMF 1.10.6**: `f(z) = ∑_{n=−∞}^{∞} aₙ (z − z₀)ⁿ` in the annulus, as a doubly-infinite
series (`M`, `N → ∞` independently, §1.9(v)), with the coefficients 1.10.7 taken on any circle
`|z − z₀| = r`, `r ∈ (r₁, r₂)`. -/
theorem dlmf_1_10_6 {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f (annulus z₀ r₁ r₂)) {r : ℝ} (hr : r ∈ Ioo r₁ r₂) {z : ℂ}
    (hz : z ∈ annulus z₀ r₁ r₂) :
    DoubleSeriesConverges (fun n : ℤ => laurentCoeff f z₀ r n * (z - z₀) ^ n) (f z) := by
  obtain ⟨S₁, S₂, h1, h2, hsum⟩ := hasSum_laurent hr₁ hf hr hz
  unfold DoubleSeriesConverges
  rw [← hsum, ← prod_atTop_atTop_eq]
  have hA : Tendsto (partialSum fun k : ℕ => laurentCoeff f z₀ r k * (z - z₀) ^ (k : ℤ)) atTop
      (𝓝 S₁) := by
    simp only [zpow_natCast]
    exact seriesConverges_iff.mpr h1.tendsto_sum_nat
  refine ((hA.comp tendsto_snd).add (h2.tendsto_sum_nat.comp tendsto_fst)).congr fun p => ?_
  rw [show p = (p.1, p.2) from rfl, doublePartialSum_eq]
  rfl

/-- Cauchy's estimate for the Laurent coefficients: `|aₙ| ≤ M ρ^{−n}` if `|f| ≤ M` on
`|z − z₀| = ρ`. -/
theorem norm_laurentCoeff_le {f : ℂ → ℂ} {z₀ : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ w ∈ sphere z₀ ρ, ‖f w‖ ≤ M) (n : ℤ) : ‖laurentCoeff f z₀ ρ n‖ ≤ M * ρ ^ (-n) := by
  have hb : ∀ w ∈ sphere z₀ ρ, ‖f w / (w - z₀) ^ (n + 1)‖ ≤ M / ρ ^ (n + 1) := by
    intro w hw
    rw [norm_div, norm_zpow, show ‖w - z₀‖ = ρ by rw [← dist_eq_norm]; exact hw]
    exact div_le_div_of_nonneg_right (hM w hw) (by positivity)
  have hI := circleIntegral.norm_integral_le_of_norm_le_const hρ.le hb
  have hn : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [laurentCoeff, norm_mul, hn]
  calc (2 * π)⁻¹ * ‖∮ z in C(z₀, ρ), f z / (z - z₀) ^ (n + 1)‖
      ≤ (2 * π)⁻¹ * (2 * π * ρ * (M / ρ ^ (n + 1))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M * ρ ^ (-n) := by
        rw [zpow_add_one₀ hρ.ne', zpow_neg]
        field_simp

theorem summable_geometric_aux {q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun k : ℕ => C * q ^ k :=
  (summable_geometric_of_lt_one hq0 hq1).mul_left C

/-- DLMF §1.10(iii): the Laurent series converges uniformly on every closed sub-annulus
`ρ₁ ≤ |z − z₀| ≤ ρ₂` (`r₁ < ρ₁ ≤ ρ₂ < r₂`), and both halves converge absolutely there. -/
theorem dlmf_1_10_6_uniform {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f (annulus z₀ r₁ r₂)) {r : ℝ} (hr : r ∈ Ioo r₁ r₂) {ρ₁ ρ₂ : ℝ}
    (h₁ : r₁ < ρ₁) (h₁₂ : ρ₁ ≤ ρ₂) (h₂ : ρ₂ < r₂) :
    DoubleSeriesConvergesUniformlyOn (fun n z => laurentCoeff f z₀ r n * (z - z₀) ^ n) f
        {z | ρ₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ ρ₂} ∧
      ∀ z ∈ {z | ρ₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ ρ₂},
        SeriesConvergesAbsolutely (fun k : ℕ => laurentCoeff f z₀ r k * (z - z₀) ^ k) ∧
        SeriesConvergesAbsolutely (fun k : ℕ => laurentCoeff f z₀ r (-((k + 1 : ℕ) : ℤ)) *
          (z - z₀) ^ (-((k + 1 : ℕ) : ℤ))) := by
  set K := {z : ℂ | ρ₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ ρ₂}
  set σ₁ := (r₁ + ρ₁) / 2 with hσ₁
  set σ₂ := (ρ₂ + r₂) / 2 with hσ₂
  have hρ₁0 : 0 < ρ₁ := lt_of_le_of_lt hr₁ h₁
  have hσ₁0 : 0 < σ₁ := by rw [hσ₁]; linarith
  have hσ₁m : σ₁ ∈ Ioo r₁ r₂ := ⟨by rw [hσ₁]; linarith, by rw [hσ₁]; linarith⟩
  have hσ₂m : σ₂ ∈ Ioo r₁ r₂ := ⟨by rw [hσ₂]; linarith, by rw [hσ₂]; linarith⟩
  have hσ₂0 : 0 < σ₂ := by rw [hσ₂]; linarith
  clear_value σ₁ σ₂
  have hsphere : ∀ σ ∈ Ioo r₁ r₂, ∃ M, 0 ≤ M ∧ ∀ w ∈ sphere z₀ σ, ‖f w‖ ≤ M := by
    intro σ hσ
    obtain ⟨M, hM⟩ := (isCompact_sphere z₀ σ).exists_bound_of_continuousOn
      (hf.continuousOn.mono fun w hw => by
        rw [mem_sphere, dist_eq_norm] at hw
        exact ⟨by rw [hw]; exact hσ.1, by rw [hw]; exact hσ.2⟩)
    exact ⟨max M 0, le_max_right _ _, fun w hw => (hM w hw).trans (le_max_left _ _)⟩
  obtain ⟨M₁, hM₁0, hM₁⟩ := hsphere σ₁ hσ₁m
  obtain ⟨M₂, hM₂0, hM₂⟩ := hsphere σ₂ hσ₂m
  set q₁ := σ₁ / ρ₁ with hq₁
  set q₂ := ρ₂ / σ₂ with hq₂
  have hq₁0 : 0 ≤ q₁ := by positivity
  have hq₁1 : q₁ < 1 := by rw [hq₁, div_lt_one hρ₁0, hσ₁]; linarith
  have hq₂0 : 0 ≤ q₂ := by rw [hq₂]; exact div_nonneg (hρ₁0.le.trans h₁₂) hσ₂0.le
  have hq₂1 : q₂ < 1 := by rw [hq₂, div_lt_one hσ₂0, hσ₂]; linarith
  have hpos : ∀ k : ℕ, ∀ z ∈ K,
      ‖laurentCoeff f z₀ r k * (z - z₀) ^ (k : ℤ)‖ ≤ M₂ * q₂ ^ k := by
    intro k z hz
    rw [laurentCoeff_eq hr₁ hf hr hσ₂m, norm_mul, zpow_natCast, norm_pow]
    have hb := norm_laurentCoeff_le hσ₂0 hM₂ k
    rw [zpow_neg, zpow_natCast] at hb
    calc ‖laurentCoeff f z₀ σ₂ k‖ * ‖z - z₀‖ ^ k ≤ M₂ * (σ₂ ^ k)⁻¹ * ρ₂ ^ k :=
          mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hz.2 k) (by positivity)
            (by positivity)
      _ = M₂ * q₂ ^ k := by rw [hq₂, div_pow, div_eq_mul_inv]; ring
  have hneg : ∀ k : ℕ, ∀ z ∈ K,
      ‖laurentCoeff f z₀ r (-((k + 1 : ℕ) : ℤ)) * (z - z₀) ^ (-((k + 1 : ℕ) : ℤ))‖ ≤
        M₁ * q₁ * q₁ ^ k := by
    intro k z hz
    rw [laurentCoeff_eq hr₁ hf hr hσ₁m, norm_mul, norm_zpow]
    have hb := norm_laurentCoeff_le hσ₁0 hM₁ (-((k + 1 : ℕ) : ℤ))
    rw [neg_neg, zpow_natCast] at hb
    rw [zpow_neg, zpow_natCast]
    calc ‖laurentCoeff f z₀ σ₁ (-((k + 1 : ℕ) : ℤ))‖ * (‖z - z₀‖ ^ (k + 1))⁻¹
        ≤ M₁ * σ₁ ^ (k + 1) * (ρ₁ ^ (k + 1))⁻¹ :=
          mul_le_mul hb (inv_anti₀ (by positivity) (pow_le_pow_left₀ hρ₁0.le hz.1 _))
            (by positivity) (by positivity)
      _ = M₁ * q₁ * q₁ ^ k := by
          rw [hq₁, div_pow, pow_succ σ₁ k, pow_succ ρ₁ k, mul_inv, div_eq_mul_inv]; ring
  have hU1 := dlmf_1_9_v_Mtest (F := fun (k : ℕ) z => laurentCoeff f z₀ r k * (z - z₀) ^ (k : ℤ))
    ⟨_, seriesConverges_iff.mpr (summable_geometric_aux (C := M₂) hq₂0 hq₂1).hasSum.tendsto_sum_nat⟩
    hpos
  have hU2 := dlmf_1_9_v_Mtest
    (F := fun (k : ℕ) z => laurentCoeff f z₀ r (-((k + 1 : ℕ) : ℤ)) *
      (z - z₀) ^ (-((k + 1 : ℕ) : ℤ)))
    ⟨_, seriesConverges_iff.mpr
      (summable_geometric_aux (C := M₁ * q₁) hq₁0 hq₁1).hasSum.tendsto_sum_nat⟩ hneg
  obtain ⟨g, hg⟩ := (dlmf_1_9_v_doubly_uniform
    (F := fun n z => laurentCoeff f z₀ r n * (z - z₀) ^ n) (S := K)).mpr
    ⟨⟨_, hU1⟩, ⟨_, hU2⟩⟩
  refine ⟨?_, fun z hz => ⟨?_, ?_⟩⟩
  · unfold DoubleSeriesConvergesUniformlyOn at hg ⊢
    refine hg.congr_right fun z hz => ?_
    have hzA : z ∈ annulus z₀ r₁ r₂ := ⟨by linarith [hz.1], by linarith [hz.2]⟩
    exact tendsto_nhds_unique (hg.tendsto_at hz) (dlmf_1_10_6 hr₁ hf hr hzA)
  · rw [seriesConvergesAbsolutely_iff]
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (summable_geometric_aux (C := M₂) hq₂0 hq₂1)
    have := hpos k z hz
    rwa [zpow_natCast] at this
  · rw [seriesConvergesAbsolutely_iff]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hneg k z hz)
      (summable_geometric_aux (C := M₁ * q₁) hq₁0 hq₁1)

/-- DLMF §1.10(iii): the Laurent series converges uniformly on compact subsets of the annulus. -/
theorem dlmf_1_10_6_compact {f : ℂ → ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (hf : DifferentiableOn ℂ f (annulus z₀ r₁ r₂)) {r : ℝ} (hr : r ∈ Ioo r₁ r₂) {K : Set ℂ}
    (hK : IsCompact K) (hKA : K ⊆ annulus z₀ r₁ r₂) :
    DoubleSeriesConvergesUniformlyOn (fun n z => laurentCoeff f z₀ r n * (z - z₀) ^ n) f K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  have hc : ContinuousOn (fun z => ‖z - z₀‖) K := (continuous_sub_right z₀).norm.continuousOn
  obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne hc
  obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hne hc
  have hsub : K ⊆ {z | ‖a - z₀‖ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ ‖b - z₀‖} := fun z hz =>
    ⟨hamin hz, hbmax hz⟩
  exact ((dlmf_1_10_6_uniform hr₁ hf hr (hKA ha).1 ((hamin hb).trans le_rfl) (hKA hb).2).1).mono
    hsub

/-! ### Isolated singularities -/

/-- `z₀` is an isolated singularity of `f`: `f` is analytic in the punctured neighbourhood
`0 < |z − z₀| < R` but not at `z₀`. -/
def IsIsolatedSingularity (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) : Prop :=
  0 < R ∧ DifferentiableOn ℂ f (annulus z₀ 0 R) ∧ ¬ DifferentiableAt ℂ f z₀

/-- The singularity is removable: `aₙ = 0` for all `n < 0` (coefficients on `|z − z₀| = R/2`). -/
def IsRemovableSingularity (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) : Prop :=
  ∀ n < 0, laurentCoeff f z₀ (R / 2) n = 0

/-- `z₀` is a pole of order `m`: `−m` is the first negative index (from `−∞`) with `a_{−m} ≠ 0`. -/
def IsPoleOfOrder (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (m : ℕ) : Prop :=
  0 < m ∧ laurentCoeff f z₀ (R / 2) (-(m : ℤ)) ≠ 0 ∧
    ∀ n < -(m : ℤ), laurentCoeff f z₀ (R / 2) n = 0

/-- `z₀` is a pole. -/
def IsPole (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) : Prop := ∃ m, IsPoleOfOrder f z₀ R m

/-- `z₀` is an isolated essential singularity: `aₙ ≠ 0` for infinitely many negative `n`. -/
def IsEssentialSingularity (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) : Prop :=
  {n : ℤ | n < 0 ∧ laurentCoeff f z₀ (R / 2) n ≠ 0}.Infinite

/-- DLMF §1.10(iii): `z₀` is a pole iff `aₙ ≠ 0` for at least one, but only finitely many,
negative `n`. -/
theorem isPole_iff {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} :
    IsPole f z₀ R ↔ (∃ n < 0, laurentCoeff f z₀ (R / 2) n ≠ 0) ∧
      {n : ℤ | n < 0 ∧ laurentCoeff f z₀ (R / 2) n ≠ 0}.Finite := by
  constructor
  · rintro ⟨m, hm, hne, hzero⟩
    refine ⟨⟨-(m : ℤ), by omega, hne⟩, (Set.finite_Icc (-(m : ℤ)) (-1)).subset ?_⟩
    rintro n ⟨hn, hn0⟩
    refine ⟨?_, by omega⟩
    by_contra h
    exact hn0 (hzero n (by omega))
  · rintro ⟨⟨n₀, hn₀, hne₀⟩, hfin⟩
    obtain ⟨b, hb⟩ := hfin.bddBelow
    obtain ⟨lb, ⟨hlb, hlbne⟩, hleast⟩ := Int.exists_least_of_bdd
      (P := fun n => n < 0 ∧ laurentCoeff f z₀ (R / 2) n ≠ 0) ⟨b, fun z hz => hb hz⟩
      ⟨n₀, hn₀, hne₀⟩
    refine ⟨lb.natAbs, by omega, ?_, fun n hn => ?_⟩
    · rwa [Int.ofNat_natAbs_of_nonpos hlb.le, neg_neg]
    · rw [Int.ofNat_natAbs_of_nonpos hlb.le, neg_neg] at hn
      by_contra h
      exact absurd (hleast n ⟨by omega, h⟩) (not_le.mpr hn)

/-- DLMF §1.10(iii): an isolated singularity is exactly one of removable, a pole, or essential. -/
theorem singularity_trichotomy (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) :
    (IsRemovableSingularity f z₀ R ∨ IsPole f z₀ R ∨ IsEssentialSingularity f z₀ R) ∧
      ¬ (IsRemovableSingularity f z₀ R ∧ IsPole f z₀ R) ∧
      ¬ (IsRemovableSingularity f z₀ R ∧ IsEssentialSingularity f z₀ R) ∧
      ¬ (IsPole f z₀ R ∧ IsEssentialSingularity f z₀ R) := by
  set S := {n : ℤ | n < 0 ∧ laurentCoeff f z₀ (R / 2) n ≠ 0}
  have hrem : IsRemovableSingularity f z₀ R ↔ S = ∅ := by
    simp only [IsRemovableSingularity, Set.eq_empty_iff_forall_notMem, S, Set.mem_ofPred_eq,
      not_and, not_not]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h0 : S = ∅
    · exact Or.inl (hrem.mpr h0)
    by_cases hfin : S.Finite
    · obtain ⟨n, hn⟩ := Set.nonempty_iff_ne_empty.mpr h0
      exact Or.inr (Or.inl (isPole_iff.mpr ⟨⟨n, hn.1, hn.2⟩, hfin⟩))
    · exact Or.inr (Or.inr hfin)
  · rintro ⟨h1, h2⟩
    obtain ⟨⟨n, hn, hne⟩, -⟩ := isPole_iff.mp h2
    exact hne (h1 n hn)
  · rintro ⟨h1, h2⟩
    apply h2
    show S.Finite
    rw [hrem.mp h1]
    exact Set.finite_empty
  · rintro ⟨h1, h2⟩
    exact h2 (isPole_iff.mp h1).2

/-- DLMF §1.10(iii): at a removable singularity the Laurent series is the Taylor series:
`f(z) = ∑_{n ≥ 0} aₙ (z − z₀)ⁿ` for `0 < |z − z₀| < R`. -/
theorem IsRemovableSingularity.hasSum {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (annulus z₀ 0 R)) (h : IsRemovableSingularity f z₀ R) {z : ℂ}
    (hz : z ∈ annulus z₀ 0 R) :
    HasSum (fun n : ℕ => laurentCoeff f z₀ (R / 2) n * (z - z₀) ^ n) (f z) := by
  have hR : 0 < R := lt_trans hz.1 hz.2
  obtain ⟨S₁, S₂, h1, h2, hsum⟩ := hasSum_laurent (r := R / 2) le_rfl hf
    ⟨by linarith, by linarith⟩ hz
  have hzero : S₂ = 0 := by
    refine h2.unique ?_
    convert hasSum_zero with m
    rw [h _ (by omega), zero_mul]
  rw [hzero, add_zero] at hsum
  rw [← hsum]
  exact h1

/-- DLMF §1.10(iii): an isolated singularity is removable when `lim_{z→z₀} f(z)` exists. -/
theorem isRemovableSingularity_of_tendsto {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (annulus z₀ 0 R)) {L : ℂ} (hL : Tendsto f (𝓝[≠] z₀) (𝓝 L)) :
    IsRemovableSingularity f z₀ R := by
  have hev := hL.eventually (Metric.ball_mem_nhds L one_pos)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδf⟩ := hev
  intro n hn
  set k := n.natAbs with hk
  have hkn : (k : ℤ) = -n := Int.ofNat_natAbs_of_nonpos hn.le
  have hk0 : k ≠ 0 := by omega
  have hbound : ∀ ρ ∈ Ioo (0 : ℝ) (min δ R),
      ‖laurentCoeff f z₀ (R / 2) n‖ ≤ (‖L‖ + 1) * ρ ^ k := by
    intro ρ hρ
    rw [laurentCoeff_eq le_rfl hf ⟨by linarith, by linarith⟩
      ⟨hρ.1, hρ.2.trans_le (min_le_right _ _)⟩ n]
    have hM : ∀ w ∈ sphere z₀ ρ, ‖f w‖ ≤ ‖L‖ + 1 := by
      intro w hw
      have hwd : dist w z₀ = ρ := hw
      have hfw := hδf (by rw [hwd]; exact hρ.2.trans_le (min_le_left _ _))
        (by
          intro h
          rw [mem_singleton_iff] at h
          rw [h, dist_self] at hwd
          linarith [hρ.1])
      have hfw' : dist (f w) L < 1 := hfw
      rw [dist_eq_norm] at hfw'
      linarith [norm_sub_norm_le (f w) L]
    have := norm_laurentCoeff_le hρ.1 hM n
    rwa [← hkn, zpow_natCast] at this
  have hlim : Tendsto (fun ρ : ℝ => (‖L‖ + 1) * ρ ^ k) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_pow k).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0)) |>.const_mul
      (‖L‖ + 1)
    rwa [zero_pow hk0, mul_zero] at this
  have hle : ‖laurentCoeff f z₀ (R / 2) n‖ ≤ 0 :=
    ge_of_tendsto hlim (by
      filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hR)] with ρ hρ
      exact hbound ρ hρ)
  exact norm_le_zero_iff.mp hle

/-- DLMF §1.10(iii) example: `(sin z)/z` has a removable (isolated) singularity at `z = 0`. -/
theorem sin_div_removable :
    IsIsolatedSingularity (fun z => sin z / z) 0 1 ∧
      IsRemovableSingularity (fun z => sin z / z) 0 1 := by
  have hlim : Tendsto (fun z => sin z / z) (𝓝[≠] 0) (𝓝 1) := by
    have := hasDerivAt_iff_tendsto_slope.mp (Complex.hasDerivAt_sin 0)
    rw [Complex.cos_zero] at this
    refine this.congr fun z => ?_
    simp [slope_def_field]
  have hd : DifferentiableOn ℂ (fun z => sin z / z) (annulus 0 0 1) := fun z hz => by
    have hz0 : z ≠ 0 := by
      intro h
      have := hz.1
      rw [h, sub_zero, norm_zero] at this
      exact lt_irrefl _ this
    exact (Complex.differentiable_sin z |>.div differentiableAt_id hz0).differentiableWithinAt
  refine ⟨⟨one_pos, hd, fun hdiff => ?_⟩, isRemovableSingularity_of_tendsto one_pos hd hlim⟩
  have hc := hdiff.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have := tendsto_nhds_unique hc hlim
  simp at this

/-- The residue `Res_{z=z₀}[f(z)] = a_{−1}`. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) : ℂ := laurentCoeff f z₀ (R / 2) (-1)

/-- The residue is `(2πi)⁻¹ ∮_{|z−z₀|=r} f(z) dz` for every `r ∈ (0, R)`. -/
theorem residue_eq {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f (annulus z₀ 0 R))
    {r : ℝ} (hr : r ∈ Ioo 0 R) :
    residue f z₀ R = (2 * π * I)⁻¹ * ∮ z in C(z₀, r), f z := by
  rw [residue, laurentCoeff_eq le_rfl hf ⟨by linarith [hr.1, hr.2], by linarith [hr.1, hr.2]⟩ hr,
    laurentCoeff]
  simp

/-- A meromorphic function (DLMF): its only singularities in `ℂ` are poles. -/
def IsMeromorphicDLMF (f : ℂ → ℂ) : Prop :=
  ∀ z₀, AnalyticAt ℂ f z₀ ∨ ∃ R > 0, DifferentiableOn ℂ f (annulus z₀ 0 R) ∧ IsPole f z₀ R

/-- Singularities at infinity are classified as those of `f(1/z)` at `z = 0`. -/
def IsRemovableSingularityAtInfty (f : ℂ → ℂ) (R : ℝ) : Prop :=
  IsRemovableSingularity (fun w => f w⁻¹) 0 R

/-- A pole of order `m` at infinity. -/
def IsPoleOfOrderAtInfty (f : ℂ → ℂ) (R : ℝ) (m : ℕ) : Prop :=
  IsPoleOfOrder (fun w => f w⁻¹) 0 R m

/-- An essential singularity at infinity. -/
def IsEssentialSingularityAtInfty (f : ℂ → ℂ) (R : ℝ) : Prop :=
  IsEssentialSingularity (fun w => f w⁻¹) 0 R

end Azurite.DLMF
