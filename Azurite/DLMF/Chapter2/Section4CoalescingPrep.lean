/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Analysis.Complex.RemovableSingularity
import Azurite.DLMF.Chapter2.Section4CoalescingExists

/-!
# DLMF §2.4(v): preparation of `p(α, t)` near the confluence

Functions `G(α, t)` analytic in `t` and continuous in `(α, t)` (DLMF's hypotheses in §2.4(v)).
The difference quotient `dslope (G α) c` is again analytic in `t` and, by Cauchy's formula
`dslope G c s = (2πi)⁻¹ ∮ G(ξ)/((ξ − c)(ξ − s)) dξ`, jointly continuous
(`continuousOn_dslope_param`). Dividing three times gives the prepared form
`p(α, t̂ + s) = p(α, t̂) + ε₁(α)s + ε₂(α)s² + s³V(α, s)` (`CFUPrep`), with `ε₁ = ∂ₜp(α, t̂)`,
`ε₂ = ∂ₜ²p(α, t̂)/2`, `V(α, 0) = ∂ₜ³p(α, t̂)/6`, all continuous in `α`, and `V` analytic in `s`,
jointly continuous and nonvanishing on a fixed disc for `α` near `α̂`.
-/

open Set Filter Topology Complex Metric
open scoped Real

namespace Azurite.DLMF

/-- Cauchy's formula for the difference quotient: for `G` analytic on `|ξ − c| ≤ r` and
`|s − c| < r`, `dslope G c s = (2πi)⁻¹ ∮ G(ξ)/((ξ − c)(ξ − s)) dξ`. -/
theorem dslope_eq_circleIntegral {G : ℂ → ℂ} {c s : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) (hs : s ∈ ball c r) :
    dslope G c s = (2 * π * I)⁻¹ * ∮ ξ in C(c, r), G ξ / ((ξ - c) * (ξ - s)) := by
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  by_cases hsc : s = c
  · subst hsc
    rw [dslope_same]
    have h1 := hG.deriv_eq_smul_circleIntegral hr
    have h2 : (∮ ξ in C(s, r), G ξ / ((ξ - s) * (ξ - s))) =
        ∮ ξ in C(s, r), (1 / (ξ - s) ^ 2) • G ξ := by
      refine circleIntegral.integral_congr hr.le fun ξ _ => ?_
      rw [smul_eq_mul]
      ring
    rw [h2, h1, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2πI, one_mul]
  · have hc := hG.circleIntegral_sub_inv_smul (mem_ball_self hr)
    have hs' := hG.circleIntegral_sub_inv_smul hs
    have hsc' : s - c ≠ 0 := sub_ne_zero.mpr hsc
    have hGc : ContinuousOn G (sphere c r) :=
      hG.continuousOn.mono sphere_subset_closedBall
    have hGc' : ContinuousOn G (sphere c |r|) := by
      rw [abs_of_pos hr]
      exact hGc
    have hi1 : CircleIntegrable (fun ξ => (ξ - s)⁻¹ • G ξ) c r :=
      (circleIntegrable_sub_inv_iff.mpr (Or.inr (by
        rw [abs_of_pos hr]
        exact fun h => (mem_ball.mp hs).ne (mem_sphere.mp h)))).smul_continuousOn hGc'
    have hi2 : CircleIntegrable (fun ξ => (ξ - c)⁻¹ • G ξ) c r :=
      (circleIntegrable_sub_inv_iff.mpr (Or.inr (by
        rw [abs_of_pos hr]
        exact fun h => hr.ne' (by simpa using (mem_sphere.mp h).symm)))).smul_continuousOn hGc'
    have h2 : (∮ ξ in C(c, r), G ξ / ((ξ - c) * (ξ - s))) =
        (s - c)⁻¹ • ∮ ξ in C(c, r), ((ξ - s)⁻¹ • G ξ - (ξ - c)⁻¹ • G ξ) := by
      rw [← circleIntegral.integral_smul]
      refine circleIntegral.integral_congr hr.le fun ξ hξ => ?_
      have h1 : ξ - c ≠ 0 := sub_ne_zero.mpr (ne_of_mem_sphere hξ hr.ne')
      have h3 : ξ - s ≠ 0 := by
        intro h0
        rw [sub_eq_zero] at h0
        rw [h0] at hξ
        exact absurd (mem_ball.mp hs) (not_lt.mpr (mem_sphere.mp hξ).ge)
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [h2, circleIntegral.integral_sub hi1 hi2, hs', hc, dslope_of_ne _ hsc, slope_def_field,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_sub, div_eq_inv_mul]
    rw [show (s - c)⁻¹ * (2 * π * I * (G s - G c)) = 2 * π * I * ((s - c)⁻¹ * (G s - G c)) by ring,
      ← mul_assoc, inv_mul_cancel₀ h2πI, one_mul]

variable {ι : Type*} [TopologicalSpace ι]

/-- The difference quotient of a family analytic in `t` and jointly continuous is jointly
continuous. -/
theorem continuousOn_dslope_param {G : ι → ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hG : ∀ α, DifferentiableOn ℂ (G α) (ball c R))
    (hcont : ContinuousOn (fun q : ι × ℂ => G q.1 q.2) (univ ×ˢ ball c R)) :
    ContinuousOn (fun q : ι × ℂ => dslope (G q.1) c q.2) (univ ×ˢ ball c R) := by
  intro q₀ hq₀
  have hd : dist q₀.2 c < R := mem_ball.mp hq₀.2
  obtain ⟨r, hr0, hsr, hrR⟩ : ∃ r, 0 < r ∧ dist q₀.2 c < r ∧ r < R :=
    ⟨(dist q₀.2 c + R) / 2, by linarith [dist_nonneg (x := q₀.2) (y := c)], by linarith,
      by linarith⟩
  set S : Set (ι × ℂ) := univ ×ˢ ball c r with hS
  set Φ : ι × ℂ → ℂ := fun q => (2 * π * I)⁻¹ * ∮ ξ in C(c, r), G q.1 ξ / ((ξ - c) * (ξ - q.2))
    with hΦdef
  have hΦ : ContinuousOn Φ S := by
    rw [continuousOn_iff_continuous_domRestrict]
    show Continuous fun x : S => (2 * π * I)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
      deriv (circleMap c r) θ • (G (x : ι × ℂ).1 (circleMap c r θ) /
        ((circleMap c r θ - c) * (circleMap c r θ - (x : ι × ℂ).2)))
    refine continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2 * π))
    show Continuous fun p : S × ℝ => deriv (circleMap c r) p.2 •
      (G (p.1 : ι × ℂ).1 (circleMap c r p.2) /
        ((circleMap c r p.2 - c) * (circleMap c r p.2 - (p.1 : ι × ℂ).2)))
    simp only [deriv_circleMap]
    have hGc : Continuous fun p : S × ℝ => G (p.1 : ι × ℂ).1 (circleMap c r p.2) := by
      refine hcont.comp_continuous (f := fun p : S × ℝ => ((p.1 : ι × ℂ).1, circleMap c r p.2))
        (by fun_prop) fun p => ⟨trivial, ?_⟩
      rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0]
      exact hrR
    have hden : Continuous fun p : S × ℝ =>
        (circleMap c r p.2 - c) * (circleMap c r p.2 - (p.1 : ι × ℂ).2) := by fun_prop
    have hden0 : ∀ p : S × ℝ,
        (circleMap c r p.2 - c) * (circleMap c r p.2 - (p.1 : ι × ℂ).2) ≠ 0 := fun p =>
      mul_ne_zero (sub_ne_zero.mpr (circleMap_ne_center hr0.ne'))
        (sub_ne_zero.mpr (circleMap_ne_mem_ball p.1.2.2 _))
    exact (by fun_prop : Continuous fun p : S × ℝ => circleMap 0 r p.2 * I).smul
      (hGc.div hden hden0)
  have heq : EqOn (fun q : ι × ℂ => dslope (G q.1) c q.2) Φ S := fun q hq =>
    dslope_eq_circleIntegral hr0 ((hG q.1).mono (closedBall_subset_ball hrR)) hq.2
  have hopen : IsOpen S := isOpen_univ.prod isOpen_ball
  have hmem : q₀ ∈ S := ⟨trivial, mem_ball.mpr hsr⟩
  exact ((hΦ.congr heq).continuousAt (hopen.mem_nhds hmem)).continuousWithinAt

/-! ### Taylor coefficients of iterated difference quotients -/

/-- `d/dz [(dslope ·)^n f](a) = f^{(n+1)}(a)/(n+1)!`. -/
theorem deriv_iterate_dslope {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (n : ℕ) :
    deriv ((Function.swap dslope a)^[n] f) a =
      iteratedDeriv (n + 1) f a / ((n + 1).factorial : ℂ) := by
  have hp := hf.hasFPowerSeriesAt
  rw [(HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope n hp).deriv]
  change (FormalMultilinearSeries.fslope^[n] _).coeff 1 = _
  rw [FormalMultilinearSeries.coeff_iterate_fslope, add_comm 1 n]
  show (FormalMultilinearSeries.ofScalars ℂ fun k => iteratedDeriv k f a / (k.factorial : ℂ))
    (n + 1) (fun _ => (1 : ℂ)) = _
  rw [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one]

/-! ### The prepared form -/

section Prep

variable (p : ι → ℂ → ℂ) (t₀ : ℂ)

/-- `D₁(α, s) = (p(α,s) − p(α,t₀))/(s − t₀)`. -/
noncomputable def cfuD₁ (α : ι) : ℂ → ℂ := dslope (p α) t₀

/-- `D₂(α, s) = (D₁(α,s) − D₁(α,t₀))/(s − t₀)`. -/
noncomputable def cfuD₂ (α : ι) : ℂ → ℂ := dslope (cfuD₁ p t₀ α) t₀

/-- `V(α, s) = (D₂(α,s) − D₂(α,t₀))/(s − t₀)`, the cubic coefficient function. -/
noncomputable def cfuV (α : ι) : ℂ → ℂ := dslope (cfuD₂ p t₀ α) t₀

/-- `ε₁(α) = ∂ₜp(α, t₀)`. -/
noncomputable def cfuEps₁ (α : ι) : ℂ := deriv (p α) t₀

/-- `ε₂(α) = ∂ₜ²p(α, t₀)/2`. -/
noncomputable def cfuEps₂ (α : ι) : ℂ := deriv (cfuD₁ p t₀ α) t₀

omit [TopologicalSpace ι] in
/-- The prepared form `p(α, s) = p(α,t₀) + ε₁(s − t₀) + ε₂(s − t₀)² + (s − t₀)³ V(α, s)`. -/
theorem cfu_prep (α : ι) (s : ℂ) :
    p α s = p α t₀ + cfuEps₁ p t₀ α * (s - t₀) + cfuEps₂ p t₀ α * (s - t₀) ^ 2 +
      (s - t₀) ^ 3 * cfuV p t₀ α s := by
  have h1 : (s - t₀) * dslope (p α) t₀ s = p α s - p α t₀ := by
    rw [← smul_eq_mul]
    exact sub_smul_dslope _ _ _
  have h2 : (s - t₀) * dslope (dslope (p α) t₀) t₀ s = dslope (p α) t₀ s - deriv (p α) t₀ := by
    rw [← dslope_same (p α) t₀, ← smul_eq_mul]
    exact sub_smul_dslope _ _ _
  have h3 : (s - t₀) * dslope (dslope (dslope (p α) t₀) t₀) t₀ s =
      dslope (dslope (p α) t₀) t₀ s - deriv (dslope (p α) t₀) t₀ := by
    rw [← dslope_same (dslope (p α) t₀) t₀, ← smul_eq_mul]
    exact sub_smul_dslope _ _ _
  show p α s = p α t₀ + deriv (p α) t₀ * (s - t₀) + deriv (dslope (p α) t₀) t₀ * (s - t₀) ^ 2 +
    (s - t₀) ^ 3 * dslope (dslope (dslope (p α) t₀) t₀) t₀ s
  linear_combination -h1 - (s - t₀) * h2 - (s - t₀) ^ 2 * h3

variable {p t₀} {R : ℝ}

omit [TopologicalSpace ι] in
theorem differentiableOn_cfuV (hR : 0 < R) (hp : ∀ α, DifferentiableOn ℂ (p α) (ball t₀ R))
    (α : ι) : DifferentiableOn ℂ (cfuV p t₀ α) (ball t₀ R) := by
  have hn : ball t₀ R ∈ 𝓝 t₀ := isOpen_ball.mem_nhds (mem_ball_self hR)
  exact (Complex.differentiableOn_dslope hn).mpr ((Complex.differentiableOn_dslope hn).mpr
    ((Complex.differentiableOn_dslope hn).mpr (hp α)))

theorem continuousOn_cfuV (hR : 0 < R) (hp : ∀ α, DifferentiableOn ℂ (p α) (ball t₀ R))
    (hcont : ContinuousOn (fun q : ι × ℂ => p q.1 q.2) (univ ×ˢ ball t₀ R)) :
    ContinuousOn (fun q : ι × ℂ => cfuV p t₀ q.1 q.2) (univ ×ˢ ball t₀ R) := by
  have hn : ball t₀ R ∈ 𝓝 t₀ := isOpen_ball.mem_nhds (mem_ball_self hR)
  have h1 := continuousOn_dslope_param hp hcont
  have h2 := continuousOn_dslope_param (G := cfuD₁ p t₀)
    (fun α => (Complex.differentiableOn_dslope hn).mpr (hp α)) h1
  exact continuousOn_dslope_param (G := cfuD₂ p t₀)
    (fun α => (Complex.differentiableOn_dslope hn).mpr
      ((Complex.differentiableOn_dslope hn).mpr (hp α))) h2

theorem continuous_cfuEps₁ (hR : 0 < R) (hp : ∀ α, DifferentiableOn ℂ (p α) (ball t₀ R))
    (hcont : ContinuousOn (fun q : ι × ℂ => p q.1 q.2) (univ ×ˢ ball t₀ R)) :
    Continuous fun α => cfuEps₁ p t₀ α := by
  have h1 := continuousOn_dslope_param hp hcont
  have := h1.comp_continuous (f := fun α : ι => (α, t₀)) (by fun_prop)
    (fun α => ⟨trivial, mem_ball_self hR⟩)
  simpa [Function.comp_def, cfuEps₁, dslope_same] using this

theorem continuous_cfuEps₂ (hR : 0 < R) (hp : ∀ α, DifferentiableOn ℂ (p α) (ball t₀ R))
    (hcont : ContinuousOn (fun q : ι × ℂ => p q.1 q.2) (univ ×ˢ ball t₀ R)) :
    Continuous fun α => cfuEps₂ p t₀ α := by
  have hn : ball t₀ R ∈ 𝓝 t₀ := isOpen_ball.mem_nhds (mem_ball_self hR)
  have h1 := continuousOn_dslope_param hp hcont
  have h2 := continuousOn_dslope_param (G := cfuD₁ p t₀)
    (fun α => (Complex.differentiableOn_dslope hn).mpr (hp α)) h1
  have := h2.comp_continuous (f := fun α : ι => (α, t₀)) (by fun_prop)
    (fun α => ⟨trivial, mem_ball_self hR⟩)
  simpa [Function.comp_def, cfuEps₂, dslope_same] using this

omit [TopologicalSpace ι] in
theorem cfuEps₂_eq {α : ι} (hp : AnalyticAt ℂ (p α) t₀) :
    cfuEps₂ p t₀ α = iteratedDeriv 2 (p α) t₀ / 2 := by
  have := deriv_iterate_dslope hp 1
  have e : (Function.swap dslope t₀)^[1] (p α) = dslope (p α) t₀ := rfl
  rw [e] at this
  norm_num [Nat.factorial] at this
  exact this

omit [TopologicalSpace ι] in
theorem cfuV_self {α : ι} (hp : AnalyticAt ℂ (p α) t₀) :
    cfuV p t₀ α t₀ = iteratedDeriv 3 (p α) t₀ / 6 := by
  have := deriv_iterate_dslope hp 2
  have e : (Function.swap dslope t₀)^[2] (p α) = dslope (dslope (p α) t₀) t₀ := rfl
  rw [e] at this
  norm_num [Nat.factorial] at this
  rw [cfuV, dslope_same]
  exact this

/-- If `∂ₜ³p(α̂, t₀) ≠ 0`, then `V ≠ 0` on a fixed disc around `t₀` for all `α` near `α̂`. -/
theorem exists_cfuV_ne_zero (hR : 0 < R) (hp : ∀ α, DifferentiableOn ℂ (p α) (ball t₀ R))
    (hcont : ContinuousOn (fun q : ι × ℂ => p q.1 q.2) (univ ×ˢ ball t₀ R)) {α₀ : ι}
    (h3 : iteratedDeriv 3 (p α₀) t₀ ≠ 0) :
    ∃ N ∈ 𝓝 α₀, ∃ r > 0, r ≤ R ∧ ∀ α ∈ N, ∀ s ∈ ball t₀ r, cfuV p t₀ α s ≠ 0 := by
  have hV := continuousOn_cfuV hR hp hcont
  have hopen : IsOpen (univ ×ˢ ball t₀ R : Set (ι × ℂ)) := isOpen_univ.prod isOpen_ball
  have hmem : ((α₀, t₀) : ι × ℂ) ∈ univ ×ˢ ball t₀ R := ⟨trivial, mem_ball_self hR⟩
  have hc : ContinuousAt (fun q : ι × ℂ => cfuV p t₀ q.1 q.2) (α₀, t₀) :=
    hV.continuousAt (hopen.mem_nhds hmem)
  have hne : cfuV p t₀ α₀ t₀ ≠ 0 := by
    rw [cfuV_self ((hp α₀).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR)))]
    exact div_ne_zero h3 (by norm_num)
  have hev : {z : ι × ℂ | cfuV p t₀ z.1 z.2 ≠ 0} ∈ 𝓝 (α₀, t₀) := hc.eventually_ne hne
  obtain ⟨N, hN, T, hT, hNT⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.mp hT
  refine ⟨N, hN, min r₁ R, lt_min hr₁ hR, min_le_right _ _, fun α hα s hs => ?_⟩
  exact @hNT (α, s) ⟨hα, hball (ball_subset_ball (min_le_left _ _) hs)⟩

end Prep

end Azurite.DLMF
