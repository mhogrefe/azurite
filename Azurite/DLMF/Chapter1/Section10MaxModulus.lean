/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Schwarz

/-!
# DLMF §1.10(v): Maximum-Modulus Principle

Formalizations of <https://dlmf.nist.gov/1.10.v> (a domain is an open preconnected set).

* Analytic functions: `dlmf_1_10_v_maxModulus` (an interior maximum of `|f|` forces `f` constant),
  `dlmf_1_10_v_boundary` (on a bounded set, `|f|` attains its maximum over `D̄` on `∂D`), from
  Mathlib's `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` and
  `Complex.exists_mem_frontier_isMaxOn_norm`.
* Harmonic functions: `dlmf_1_10_v_harmonic` (maximum principle; locally `u = ℜF` with `F` analytic,
  and `|e^F| = e^u`, `harmonic_eventually_eq_of_isMax`, then connectedness),
  `dlmf_1_10_v_harmonic_boundary` (bounded domain: maximum on `∂D`).
* Schwarz's lemma: `dlmf_1_10_11` (`|f(z)| ≤ M|z|/R`, `|f′(0)| ≤ M/R`), `dlmf_1_10_11_eq_iff`
  (equality at some `z ≠ 0` or for `f′(0)` iff `f(z) = Az`, `|A| = M/R`), from Mathlib's
  `Complex.dist_le_div_mul_dist_of_mapsTo_ball`, `Complex.norm_deriv_le_div_of_mapsTo_ball` and
  `Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'`.
-/

open Filter Topology Set Metric Complex Bornology

namespace Azurite.DLMF

/-! ### Analytic functions -/

/-- DLMF §1.10(v): if `f` is analytic in a domain `D` and `|f(z)| ≤ |f(z₀)|` on `D`, `z₀ ∈ D`,
then `f` is constant in `D`. -/
theorem dlmf_1_10_v_maxModulus {f : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hf : DifferentiableOn ℂ f D) {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hle : ∀ z ∈ D, ‖f z‖ ≤ ‖f z₀‖) :
    ∀ z ∈ D, f z = f z₀ :=
  fun _ hz => Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hDc hDo hf hz₀ hle hz

/-- DLMF §1.10(v): for `D` bounded, `f` continuous on `D̄` and analytic in `D`, `|f|` attains its
maximum (over `D̄`) on `∂D` (neither openness nor connectedness of `D` is needed). -/
theorem dlmf_1_10_v_boundary {f : ℂ → ℂ} {D : Set ℂ} (hDb : IsBounded D)
    (hne : D.Nonempty) (hfc : ContinuousOn f (closure D)) (hfd : DifferentiableOn ℂ f D) :
    ∃ z ∈ frontier D, ∀ w ∈ closure D, ‖f w‖ ≤ ‖f z‖ :=
  Complex.exists_mem_frontier_isMaxOn_norm hDb hne ⟨hfd, hfc⟩

/-! ### Harmonic functions -/

/-- Local step: a harmonic function with a maximum at `z` is constant near `z`. -/
theorem harmonic_eventually_eq_of_isMax {u : ℂ → ℝ} {D : Set ℂ} (hDo : IsOpen D)
    (hu : InnerProductSpace.HarmonicOnNhd u D) {z : ℂ} (hz : z ∈ D)
    (hle : ∀ w ∈ D, u w ≤ u z) : ∃ ε > 0, ball z ε ⊆ D ∧ ∀ w ∈ ball z ε, u w = u z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hDo z hz
  obtain ⟨F, hF, hFu⟩ := (hu.mono hball).exists_analyticOnNhd_ball_re_eq
  refine ⟨ε, hε, hball, fun w hw => ?_⟩
  set g : ℂ → ℂ := fun w => exp (F w)
  have hgd : DifferentiableOn ℂ g (ball z ε) :=
    fun w hw => ((hF w hw).differentiableAt.cexp).differentiableWithinAt
  have hnorm : ∀ w ∈ ball z ε, ‖g w‖ = Real.exp (u w) := fun w hw => by
    simp only [g, norm_exp]
    exact congrArg Real.exp (hFu hw)
  have hmax : ∀ w ∈ ball z ε, ‖g w‖ ≤ ‖g z‖ := fun w hw => by
    rw [hnorm w hw, hnorm z (mem_ball_self hε)]
    exact Real.exp_le_exp.mpr (hle w (hball hw))
  have hconst := dlmf_1_10_v_maxModulus isOpen_ball (convex_ball z ε).isPreconnected hgd
    (mem_ball_self hε) hmax w hw
  have := congrArg norm hconst
  rw [hnorm w hw, hnorm z (mem_ball_self hε)] at this
  exact Real.exp_injective this

/-- DLMF §1.10(v): if `u` is harmonic in a domain `D`, `z₀ ∈ D`, and `u(z) ≤ u(z₀)` on `D`, then
`u` is constant in `D`. -/
theorem dlmf_1_10_v_harmonic {u : ℂ → ℝ} {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hu : InnerProductSpace.HarmonicOnNhd u D) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (hle : ∀ z ∈ D, u z ≤ u z₀) : ∀ z ∈ D, u z = u z₀ := by
  set A := {z : ℂ | ∃ ε > 0, ball z ε ⊆ D ∧ ∀ w ∈ ball z ε, u w = u z₀}
  set B := D ∩ u ⁻¹' Iio (u z₀)
  have hAo : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro z ⟨ε, hε, hball, hconst⟩
    refine ⟨ε / 2, half_pos hε, fun y hy => ⟨ε / 2, half_pos hε, fun w hw => hball ?_,
      fun w hw => hconst w ?_⟩⟩
    all_goals
      rw [mem_ball] at hy hw ⊢
      linarith [dist_triangle w y z]
  have hBo : IsOpen B := hu.continuousOn.isOpen_inter_preimage hDo isOpen_Iio
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z ⟨ε, hε, -, hconst⟩ ⟨-, hzB⟩
    have := hconst z (mem_ball_self hε)
    simp only [mem_preimage, mem_Iio] at hzB
    linarith
  have hcover : D ⊆ A ∪ B := by
    intro z hz
    rcases (hle z hz).lt_or_eq with h | h
    · exact Or.inr ⟨hz, h⟩
    · left
      obtain ⟨ε, hε, hball, hconst⟩ := harmonic_eventually_eq_of_isMax hDo hu hz
        (fun w hw => h ▸ hle w hw)
      exact ⟨ε, hε, hball, fun w hw => (hconst w hw).trans h⟩
  have hA0 : (D ∩ A).Nonempty := by
    obtain ⟨ε, hε, hball, hconst⟩ := harmonic_eventually_eq_of_isMax hDo hu hz₀ hle
    exact ⟨z₀, hz₀, ε, hε, hball, hconst⟩
  intro z hz
  obtain ⟨ε, hε, -, hconst⟩ :=
    hDc.subset_left_of_subset_union hAo hBo hdisj hcover hA0 hz
  exact hconst z (mem_ball_self hε)

/-- DLMF §1.10(v): for `D` a bounded domain, `u` continuous on `D̄` and harmonic in `D`, `u`
attains its maximum (over `D̄`) at a point of `∂D`. -/
theorem dlmf_1_10_v_harmonic_boundary {u : ℂ → ℝ} {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hDb : IsBounded D) (hne : D.Nonempty)
    (huc : ContinuousOn u (closure D)) (hu : InnerProductSpace.HarmonicOnNhd u D) :
    ∃ z ∈ frontier D, ∀ w ∈ closure D, u w ≤ u z := by
  obtain ⟨w, hw, hmax⟩ := hDb.isCompact_closure.exists_isMaxOn hne.closure huc
  by_cases hwf : w ∈ frontier D
  · exact ⟨w, hwf, hmax⟩
  have hwD : w ∈ D := by
    rw [← hDo.interior_eq, ← closure_sdiff_frontier]
    exact ⟨hw, hwf⟩
  have hconst := dlmf_1_10_v_harmonic hDo hDc hu hwD fun z hz => hmax (subset_closure hz)
  have hfront : (frontier D).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨hne, fun h => ?_⟩
    rw [h] at hDb
    exact NormedSpace.unbounded_univ ℂ ℂ hDb
  obtain ⟨z, hz⟩ := hfront
  refine ⟨z, hz, fun y hy => ?_⟩
  have hclosure : EqOn u (fun _ => u w) (closure D) :=
    (show EqOn u (fun _ => u w) D from hconst).of_subset_closure huc continuousOn_const
      subset_closure Subset.rfl
  rw [hclosure hy, hclosure (frontier_subset_closure hz)]

/-! ### Schwarz's lemma -/

/-- **DLMF 1.10.11** (Schwarz's lemma): for `f` analytic in `|z| < R` with `|f| ≤ M` and
`f(0) = 0`, `|f(z)| ≤ M|z|/R` and `|f′(0)| ≤ M/R`. -/
theorem dlmf_1_10_11 {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hM : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) (h0 : f 0 = 0) :
    (∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M * ‖z‖ / R) ∧ ‖deriv f 0‖ ≤ M / R := by
  have hmaps : MapsTo f (ball 0 R) (closedBall (f 0) M) := fun z hz => by
    rw [h0, mem_closedBall_zero_iff]
    exact hM z hz
  refine ⟨fun z hz => ?_, Complex.norm_deriv_le_div_of_mapsTo_ball hf hmaps hR⟩
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf hmaps hz
  rw [h0, dist_zero_right, dist_zero_right] at this
  rw [mul_div_right_comm]
  exact this

/-- DLMF §1.10(v): equality holds in 1.10.11 (at some `z ≠ 0`, or for `f′(0)`) iff `f(z) = Az` with
`|A| = M/R`. -/
theorem dlmf_1_10_11_eq_iff {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hM : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M)
    (h0 : f 0 = 0) :
    ((∃ z ∈ ball (0 : ℂ) R, z ≠ 0 ∧ ‖f z‖ = M * ‖z‖ / R) ∨ ‖deriv f 0‖ = M / R) ↔
      ∃ A : ℂ, ‖A‖ = M / R ∧ EqOn f (fun z => A * z) (ball 0 R) := by
  have hmaps : MapsTo f (ball 0 R) (closedBall (f 0) M) := fun z hz => by
    rw [h0, mem_closedBall_zero_iff]
    exact hM z hz
  constructor
  · intro h
    have hz₀ : ∃ z₀ ∈ ball (0 : ℂ) R, ‖dslope f 0 z₀‖ = M / R := by
      rcases h with ⟨z, hz, hz0, heq⟩ | hd
      · refine ⟨z, hz, ?_⟩
        rw [dslope_of_ne _ hz0, slope_def_field, h0, sub_zero, sub_zero, norm_div, heq]
        field_simp [norm_ne_zero_iff.mpr hz0]
      · exact ⟨0, mem_ball_self hR, by rw [dslope_same]; exact hd⟩
    obtain ⟨C, hC, hEq⟩ := Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' hf hmaps hz₀
    refine ⟨C, hC, fun z hz => ?_⟩
    rw [hEq hz]
    simp [h0, mul_comm]
  · rintro ⟨A, hA, hEq⟩
    right
    have hev : f =ᶠ[𝓝 0] fun z => A * z := eventually_of_mem (ball_mem_nhds 0 hR) hEq
    rw [hev.deriv_eq, ← hA]
    simp

end Azurite.DLMF
