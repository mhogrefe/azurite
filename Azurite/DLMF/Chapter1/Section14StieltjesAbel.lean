/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Integration by parts against a primitive; Abel's test for improper integrals

Tools for the conditionally convergent integrals of DLMF §1.14(vi).

* `integral_mul_eq_primitive`: `∫_a^b g h = (∫_a^b g) h(b) − ∫_a^b (∫_a^u g) h′(u) du` for `g`
  merely integrable and `h` of class `C¹` (Fubini on the triangle; Mathlib's integration by parts
  needs differentiable, or real absolutely continuous, factors).
* `norm_integral_mul_le_abel` (Abel's bound `‖∫_a^b g h‖ ≤ B (‖h(b)‖ + ∫_a^b ‖h′‖)` when the
  primitive of `g` stays within `B`).
* `cauchy_of_tendsto_integral`, `exists_tendsto_integral_of_cauchy` (Cauchy's criterion for
  improper integrals at `∞`), `exists_bound_of_tendsto_integral`.
-/

open Set Filter Topology MeasureTheory

namespace Azurite.DLMF

/-- **Integration by parts against the primitive of an integrable function** (Fubini):
`∫_a^b g h = (∫_a^b g) h(b) − ∫_a^b (∫_a^u g) h′(u) du` for `g` integrable and `h` of class `C¹`. -/
theorem integral_mul_eq_primitive {g h h' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hh : ∀ t ∈ Icc a b, HasDerivAt h (h' t) t)
    (hh' : ContinuousOn h' (Icc a b)) :
    ∫ t in a..b, g t * h t =
      (∫ t in a..b, g t) * h b - ∫ u in a..b, (∫ t in a..u, g t) * h' u := by
  have hgI : IntegrableOn g (Ioc a b) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hg
  have hh'I : IntegrableOn h' (Ioc a b) := (hh'.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- `h t = h b − ∫_t^b h'`
  have hftc : ∀ t ∈ Icc a b, h t = h b - ∫ u in t..b, h' u := by
    intro t ht
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hh u (by
        rw [uIcc_of_le ht.2] at hu; exact ⟨ht.1.trans hu.1, hu.2⟩))
      ((hh'.mono (Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc ht.2)]
    ring
  set F : ℝ → ℝ → ℂ := fun t u => if t < u then g t * h' u else 0 with hF
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
    have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * h' p.2)
        ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) :=
      Integrable.mul_prod hgI hh'I
    have heq : Function.uncurry F = {p : ℝ × ℝ | p.1 < p.2}.indicator
        (fun p : ℝ × ℝ => g p.1 * h' p.2) := by
      funext p
      simp only [Function.uncurry, hF, indicator, mem_ofPred_eq]
    rw [heq]
    exact hprod.indicator (measurableSet_lt measurable_fst measurable_snd)
  have hswap := integral_integral_swap hFint
  have hinner_u : ∀ t ∈ Ioc a b, ∫ u in Ioc a b, F t u = g t * ∫ u in t..b, h' u := by
    intro t ht
    have : ∀ u, F t u = (Ioi t).indicator (fun u => g t * h' u) u := fun u => by
      rw [indicator_apply]; rfl
    have hset : Ioc a b ∩ Ioi t = Ioc t b := by
      ext u; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨ht.1.trans h1, h2⟩, h1⟩
    rw [integral_congr_ae (ae_of_all _ this), setIntegral_indicator measurableSet_Ioi, hset,
      intervalIntegral.integral_of_le ht.2, integral_const_mul]
  have hinner_t : ∀ u ∈ Ioc a b, ∫ t in Ioc a b, F t u = (∫ t in a..u, g t) * h' u := by
    intro u hu
    have : ∀ t, F t u = (Iio u).indicator (fun t => g t * h' u) t := fun t => by
      rw [indicator_apply]; rfl
    have hset : Ioc a b ∩ Iio u = Ioo a u := by
      ext t; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le.trans hu.2⟩, h2⟩
    rw [integral_congr_ae (ae_of_all _ this), setIntegral_indicator measurableSet_Iio, hset,
      intervalIntegral.integral_of_le hu.1.le, integral_mul_const, integral_Ioc_eq_integral_Ioo]
  have hL : ∫ t in a..b, g t * (∫ u in t..b, h' u) = ∫ u in a..b, (∫ t in a..u, g t) * h' u := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    rw [setIntegral_congr_fun measurableSet_Ioc fun t ht => (hinner_u t ht).symm,
      setIntegral_congr_fun measurableSet_Ioc fun u hu => (hinner_t u hu).symm]
    exact hswap
  calc ∫ t in a..b, g t * h t
      = ∫ t in a..b, (g t * h b - g t * ∫ u in t..b, h' u) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hab] at ht
        rw [hftc t ht]; ring
    _ = (∫ t in a..b, g t) * h b - ∫ u in a..b, (∫ t in a..u, g t) * h' u := by
        rw [intervalIntegral.integral_sub (hg.mul_const _), intervalIntegral.integral_mul_const,
          hL]
        refine (hg.mul_continuousOn ?_)
        exact intervalIntegral.continuousOn_primitive_interval_left
          (by rw [uIcc_of_le hab]; exact hh'.integrableOn_Icc)

/-- **Abel's bound**: if the primitive `∫_a^u g` stays in the ball of radius `B` on `[a, b]`, then
`‖∫_a^b g h‖ ≤ B (‖h(b)‖ + ∫_a^b ‖h′‖)`. -/
theorem norm_integral_mul_le_abel {g h h' : ℝ → ℂ} {a b B : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hh : ∀ t ∈ Icc a b, HasDerivAt h (h' t) t)
    (hh' : ContinuousOn h' (Icc a b)) (hB : ∀ u ∈ Icc a b, ‖∫ t in a..u, g t‖ ≤ B) :
    ‖∫ t in a..b, g t * h t‖ ≤ B * (‖h b‖ + ∫ u in a..b, ‖h' u‖) := by
  rw [integral_mul_eq_primitive hab hg hh hh']
  have h1 : ‖∫ u in a..b, (∫ t in a..u, g t) * h' u‖ ≤ ∫ u in a..b, B * ‖h' u‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun u hu => ?_) ?_
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB u ⟨hu.1.le, hu.2⟩) (norm_nonneg _)
    · exact (hh'.norm.intervalIntegrable_of_Icc hab).const_mul B
  rw [intervalIntegral.integral_const_mul] at h1
  calc _ ≤ ‖(∫ t in a..b, g t) * h b‖ + ‖∫ u in a..b, (∫ t in a..u, g t) * h' u‖ :=
        norm_sub_le _ _
    _ ≤ B * ‖h b‖ + B * ∫ u in a..b, ‖h' u‖ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hB b ⟨hab, le_rfl⟩) (norm_nonneg _)) h1
    _ = _ := by ring

/-- A convergent improper integral satisfies Cauchy's criterion. -/
theorem cauchy_of_tendsto_integral {g : ℝ → ℂ} {a : ℝ} {L : ℂ}
    (hg : ∀ R, a ≤ R → IntervalIntegrable g volume a R)
    (hL : Tendsto (fun R => ∫ t in a..R, g t) atTop (𝓝 L)) {η : ℝ} (hη : 0 < η) :
    ∃ T, a ≤ T ∧ ∀ u u', T ≤ u → T ≤ u' → ‖∫ t in u..u', g t‖ ≤ η := by
  obtain ⟨T₀, hT⟩ := eventually_atTop.mp (hL.eventually (Metric.closedBall_mem_nhds L
    (half_pos hη)))
  refine ⟨max T₀ a, le_max_right _ _, fun u u' hu hu' => ?_⟩
  have ha : ∀ x, max T₀ a ≤ x → a ≤ x := fun x hx => (le_max_right _ _).trans hx
  have e : ∫ t in u..u', g t = ((∫ t in a..u', g t) - L) - ((∫ t in a..u, g t) - L) := by
    rw [← intervalIntegral.integral_interval_sub_left (hg u' (ha u' hu')) (hg u (ha u hu))]
    ring
  rw [e]
  have h1 := hT u' ((le_max_left _ _).trans hu')
  have h2 := hT u ((le_max_left _ _).trans hu)
  rw [dist_eq_norm] at h1 h2
  linarith [norm_sub_le ((∫ t in a..u', g t) - L) ((∫ t in a..u, g t) - L)]

/-- **Cauchy's criterion** for improper integrals. -/
theorem exists_tendsto_integral_of_cauchy {φ : ℝ → ℂ} {a : ℝ}
    (hφ : ∀ R, a ≤ R → IntervalIntegrable φ volume a R)
    (h : ∀ η > 0, ∃ T, a ≤ T ∧ ∀ R R', T ≤ R → R ≤ R' → ‖∫ t in R..R', φ t‖ ≤ η) :
    ∃ L, Tendsto (fun R => ∫ t in a..R, φ t) atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.mpr fun ε hε => ?_)
  obtain ⟨T, haT, hT⟩ := h (ε / 2) (half_pos hε)
  refine ⟨T, fun n hn => ?_⟩
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left (hφ n (haT.trans hn)) (hφ T haT)]
  exact (hT T n le_rfl hn).trans_lt (half_lt_self hε)

/-- The partial integrals of a convergent improper integral are bounded. -/
theorem exists_bound_of_tendsto_integral {g : ℝ → ℂ} {a : ℝ} {L : ℂ}
    (hg : ∀ R, a ≤ R → IntervalIntegrable g volume a R)
    (hL : Tendsto (fun R => ∫ t in a..R, g t) atTop (𝓝 L)) :
    ∃ B, ∀ u, a ≤ u → ‖∫ t in a..u, g t‖ ≤ B := by
  obtain ⟨T₀, hT⟩ := eventually_atTop.mp (hL.eventually (Metric.closedBall_mem_nhds L one_pos))
  set T := max T₀ a
  have hc : ContinuousOn (fun u => ∫ t in a..u, g t) (Icc a T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := a) (b := T)
      (f := g) (by
        rw [uIcc_of_le (le_max_right _ _)]
        exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le (le_max_right _ _)).mp
            (hg T (le_max_right _ _))))
    rwa [uIcc_of_le (le_max_right _ _)] at this
  obtain ⟨B₁, hB₁⟩ := (isCompact_Icc (a := a) (b := T)).exists_bound_of_continuousOn hc.norm
  refine ⟨max B₁ (‖L‖ + 1), fun u hu => ?_⟩
  by_cases huT : u ≤ T
  · have := hB₁ u ⟨hu, huT⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  · have h := hT u ((le_max_left _ _).trans (le_of_not_ge huT))
    rw [dist_eq_norm] at h
    have := norm_le_norm_add_norm_sub' (∫ t in a..u, g t) L
    exact (by linarith : ‖∫ t in a..u, g t‖ ≤ ‖L‖ + 1).trans (le_max_right _ _)

end Azurite.DLMF
