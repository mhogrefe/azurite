/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5Expansion
import Azurite.DLMF.Chapter2.Section5LaplaceStrip
import Azurite.DLMF.Chapter2.Section6Regularization

/-!
# DLMF §2.6(iv): the expansion 2.6.62

`I(x) = ∑_{j<n} a_j 𝓜h(j+α) x^{−j−α} + ∑_{k<n} b_k 𝓜f(1−k−β) x^{−k−β} + δₙ(x)`,
`δₙ(x) = ∫₀^∞ fₙ(t) hₙ(xt) dt`, when `α ≠ β` (`dlmf_2_6_62`).

DLMF obtains this formally from 2.6.57 and the regularization 2.6.59–2.6.61, and refers to Wong
for the rigorous derivation. Here it is derived from §2.5(ii): the Parseval formula 2.5.5 at a
line `ℜz = p` in the strip of convergence, the contour shift 2.5.35 to `ℜz = q` across the poles
`j + α` (of `𝓜f(1−z)`) and `k + β` (of `𝓜h(z)`), the residues (`residue_at_zero_pole`,
`residue_at_inf_pole`), and the identification of the shifted line integral with `δₙ(x)` by the
Parseval formula for the pair `(fₙ, hₙ)`, whose Mellin transforms are the continued `𝓜f`, `𝓜h`
(2.6.60 and its `h`-analogue). As in 2.5.35 the shift needs the decay 2.5.34 of the continued
`G(z) = 𝓜f(1−z) 𝓜h(z)` on the strip and its integrability on the two lines; these are
hypotheses (DLMF: "for rigorous derivations … see Wong"). `dlmf_2_6_62_remainder`:
`δₙ(x) = o(x^{−q})` as `x → +∞` (2.5.36).

The logarithmic case `α = β` is not formalized (`docs/dlmf_plan.md`).
-/

open MeasureTheory Filter Topology Set Complex Metric Asymptotics
open scoped Real

namespace Azurite.DLMF

/-- The continued product `G(z) = 𝓜f(1 − z) 𝓜h(z)` of 2.5.32, with `𝓜f` continued from the left
(2.5.25–2.5.26) and `𝓜h` continued from the right (2.5.27, 2.6.18). -/
noncomputable def regG (f h : ℝ → ℂ) (a bs : ℕ → ℂ) (α β : ℝ) (z : ℂ) : ℂ :=
  MellinZeroSetup.mellinContZero f a α (1 - z) * mellinCont h bs β z

/-- **DLMF 2.6.62**, the remainder `δₙ(x) = ∫₀^∞ fₙ(t) hₙ(xt) dt`. -/
noncomputable def regDelta (f h : ℝ → ℂ) (a bs : ℕ → ℂ) (α β : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  mellinConvInt (zeroRem f a α n) (stieltjesRem h bs β n) x

section Setup

variable {f h : ℝ → ℂ} {a bs : ℕ → ℂ} {α β b c : ℝ} (F : MellinZeroSetup f a α b)
  (H : MellinInfSetup h bs β c)
include F H

/-- `G` is analytic on `{1 − b < ℜz < q'} ∩ {−c < ℜz}` away from the poles `j + α`, `k + β` with
`j + α, k + β < q'`. -/
theorem differentiableAt_regG {z : ℂ} (hzb : 1 - b < z.re) (hzc : -c < z.re)
    (hα : ∀ j : ℕ, z ≠ j + α) (hβ : ∀ k : ℕ, z ≠ k + β) :
    DifferentiableAt ℂ (regG f h a bs α β) z := by
  have hF : DifferentiableAt ℂ (MellinZeroSetup.mellinContZero f a α) (1 - z) := by
    refine DifferentiableAt.add ?_ ?_
    · refine (dlmf_2_5_25 (zeroExp_mono α) F.f_exp F.f_loc (zeroExp_tendsto α)).2.1 (1 - z)
        fun j hj => hα j ?_
      simp only [zeroExp] at hj
      linear_combination -hj
    · exact differentiableAt_mellin_trunc₂ F.f_loc F.f_top (by simp; linarith)
  have hH : DifferentiableAt ℂ (mellinCont h bs β) z := by
    refine DifferentiableAt.add (differentiableAt_mellin_trunc₁ H.h_loc H.h_zero hzc) ?_
    exact differentiableAt_mellinTrunc₂ContZero H.h_loc StieltjesSetup.β_mono
      StieltjesSetup.β_tendsto H.h_exp fun k => hβ k
  exact (hF.comp z ((differentiableAt_const _).sub differentiableAt_id)).mul hH

/-- On the line `ℜz = p` with `max(1−b, −c) < p < min(α, β)`, `G` is the honest `𝓜f(1−z) 𝓜h(z)`. -/
theorem regG_eq_mellinG {z : ℂ} (hzb : 1 - b < z.re) (hzc : -c < z.re) (hzα : z.re < α)
    (hzβ : z.re < β) : regG f h a bs α β z = mellinG f h z := by
  rw [regG, mellinG, (F.mellinContZero_eq_mellin (by simp; linarith) (by simp; linarith)).2,
    (H.mellinCont_eq_mellin_rem (m := 0) hzc (Or.inl rfl) (by simpa using hzβ)).2,
    StieltjesSetup.rem_zero]

/-- On the line `ℜz = q` with `n − 1 + max(α, β) < q < n + min(α, β)`, `q > max(1−b, −c)`, `G` is
the honest `𝓜fₙ(1−z) 𝓜hₙ(z)`. -/
theorem regG_eq_mellinG_rem (n : ℕ) {z : ℂ} (hzb : 1 - b < z.re) (hzc : -c < z.re)
    (hα₁ : n - 1 + α < z.re) (hα₂ : z.re < n + α) (hβ₁ : n = 0 ∨ (n : ℝ) - 1 + β < z.re)
    (hβ₂ : z.re < n + β) :
    regG f h a bs α β z = mellinG (zeroRem f a α n) (stieltjesRem h bs β n) z := by
  rw [regG, mellinG, (F.dlmf_2_6_60 (n := n) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)).2, (H.mellinCont_eq_mellin_rem (m := n) hzc hβ₁ hβ₂).2]

end Setup

/-! ### The residues -/

/-- From an "eventually in the punctured neighbourhood" statement to a punctured ball. -/
theorem exists_ball_of_eventually_nhdsNE {z₀ : ℂ} {P : ℂ → Prop} (h : ∀ᶠ z in 𝓝[≠] z₀, P z) :
    ∃ ε > 0, ∀ z, dist z z₀ < ε → z ≠ z₀ → P z := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp h
  exact ⟨ε, hε, fun z hz hne => hsub ⟨Metric.mem_ball.mpr hz, hne⟩⟩

/-- The residue of `−x^{−z} G(z)` at a pole `z₀ = j + α` of `𝓜f(1 − z)`: `a_j x^{−z₀} 𝓜h(z₀)`.
Here `R` is a radius such that `F` is analytic on the punctured ball, `𝓜h` on the ball, and the
ball lies in `ℜz > 1 − b`. -/
theorem residue_at_zero_pole {f h : ℝ → ℂ} {a bs : ℕ → ℂ} {α β b : ℝ}
    (F : MellinZeroSetup f a α b) {x : ℝ} (hx : 0 < x) (j : ℕ) {R : ℝ} (hR : 0 < R)
    (hFd : DifferentiableOn ℂ (fun z => -((x : ℂ) ^ (-z) * regG f h a bs α β z))
      (annulus ((j : ℂ) + α) 0 R))
    (hHd : DifferentiableOn ℂ (mellinCont h bs β) (ball ((j : ℂ) + α) R))
    (hball : ∀ z ∈ ball ((j : ℂ) + α) R, 1 - b < z.re) :
    residue (fun z => -((x : ℂ) ^ (-z) * regG f h a bs α β z)) ((j : ℂ) + α) R =
      a j * (x : ℂ) ^ (-((j : ℂ) + α)) * mellinCont h bs β ((j : ℂ) + α) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  obtain ⟨g, hg, hgeq⟩ := (dlmf_2_5_25 (zeroExp_mono α) F.f_exp F.f_loc (zeroExp_tendsto α)).2.2 j
  have hw₀ : -zeroExp α j = 1 - ((j : ℂ) + α) := by simp only [zeroExp]; ring
  rw [hw₀] at hg hgeq
  set z₀ : ℂ := (j : ℂ) + α with hz₀
  clear_value z₀
  -- the principal part in the variable `z`
  have hev : ∀ᶠ z in 𝓝[≠] z₀, mellinTrunc₁Cont f a (zeroExp α) (1 - z) =
      -(a j) / (z - z₀) + g (1 - z) := by
    have hmap : Tendsto (fun z : ℂ => 1 - z) (𝓝[≠] z₀) (𝓝[≠] (1 - z₀)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_const.sub continuous_id).tendsto _).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h => hz (mem_singleton_iff.mpr (by linear_combination -(mem_singleton_iff.mp h)))
    filter_upwards [hmap.eventually hgeq] with z hz
    rw [hz]
    congr 1
    rw [show (1 - z) + zeroExp α j = -(z - z₀) by simp only [zeroExp, hz₀]; ring, div_neg, neg_div]
  obtain ⟨ε₁, hε₁, hP⟩ := exists_ball_of_eventually_nhdsNE hev
  obtain ⟨ε₂, hε₂, hg'⟩ := Metric.eventually_nhds_iff.mp
    ((hg.comp_of_eq (analyticAt_const.sub analyticAt_id) rfl).eventually_analyticAt)
  set r : ℝ := min R (min ε₁ ε₂) with hr
  have hr0 : 0 < r := lt_min hR (lt_min hε₁ hε₂)
  have hrR : r ≤ R := min_le_left _ _
  have hr₁ : r ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₂ : r ≤ ε₂ := (min_le_right _ _).trans (min_le_right _ _)
  rw [residue_eq_residue hFd hr0 hrR]
  set A : ℂ → ℂ := fun z => a j * (x : ℂ) ^ (-z) * mellinCont h bs β z with hA
  set G₁ : ℂ → ℂ := fun z => -((x : ℂ) ^ (-z) *
    ((g (1 - z) + mellin (trunc₂ f) (1 - z)) * mellinCont h bs β z)) with hG₁
  have hAd : DifferentiableOn ℂ A (ball z₀ r) :=
    DifferentiableOn.mul ((differentiableOn_const _).mul
      (differentiable_neg.const_cpow (Or.inl hx0)).differentiableOn)
      (hHd.mono (ball_subset_ball hrR))
  have hGd : DifferentiableOn ℂ G₁ (ball z₀ r) := by
    intro z hz
    have hzR : z ∈ ball z₀ R := ball_subset_ball hrR hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => g (1 - z)) z :=
      (hg' (lt_of_lt_of_le (mem_ball.mp hz) hr₂)).differentiableAt
    have h2 : DifferentiableAt ℂ (fun z : ℂ => mellin (trunc₂ f) (1 - z)) z :=
      (differentiableAt_mellin_trunc₂ F.f_loc F.f_top (by simp; linarith [hball z hzR])).comp z
        ((differentiableAt_const _).sub differentiableAt_id)
    exact ((((differentiable_neg.const_cpow (Or.inl hx0)).differentiableAt).mul
      ((h1.add h2).mul ((hHd z hzR).differentiableAt
        (isOpen_ball.mem_nhds hzR)))).neg).differentiableWithinAt
  refine (residue_eq_of_eq_div_add hr0 hAd hGd fun z hz => ?_).trans ?_
  · have hne : z ≠ z₀ := fun h => by simp [h, annulus] at hz
    have hz₁ : dist z z₀ < ε₁ := by rw [dist_eq_norm]; exact lt_of_lt_of_le hz.2 hr₁
    have hsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
    simp only [regG, MellinZeroSetup.mellinContZero, hA, hG₁]
    rw [hP z hz₁ hne]
    field_simp
    ring
  · simp only [hA]

/-- The residue of `−x^{−z} G(z)` at a pole `z₀ = k + β` of `𝓜h(z)`: `b_k x^{−z₀} 𝓜f(1 − z₀)`. -/
theorem residue_at_inf_pole {f h : ℝ → ℂ} {a bs : ℕ → ℂ} {α β c : ℝ}
    (H : MellinInfSetup h bs β c) {x : ℝ} (hx : 0 < x) (k : ℕ) {R : ℝ} (hR : 0 < R)
    (hFd : DifferentiableOn ℂ (fun z => -((x : ℂ) ^ (-z) * regG f h a bs α β z))
      (annulus ((k : ℂ) + β) 0 R))
    (hFc : DifferentiableOn ℂ (fun z => MellinZeroSetup.mellinContZero f a α (1 - z))
      (ball ((k : ℂ) + β) R))
    (hball : ∀ z ∈ ball ((k : ℂ) + β) R, -c < z.re) :
    residue (fun z => -((x : ℂ) ^ (-z) * regG f h a bs α β z)) ((k : ℂ) + β) R =
      bs k * (x : ℂ) ^ (-((k : ℂ) + β)) *
        MellinZeroSetup.mellinContZero f a α (1 - ((k : ℂ) + β)) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  obtain ⟨g, hg, hgeq⟩ := mellinTrunc₂ContZero_principal H.h_loc StieltjesSetup.β_mono
    StieltjesSetup.β_tendsto H.h_exp k
  set z₀ : ℂ := (k : ℂ) + β with hz₀
  clear_value z₀
  obtain ⟨ε₁, hε₁, hP⟩ := exists_ball_of_eventually_nhdsNE hgeq
  obtain ⟨ε₂, hε₂, hg'⟩ := Metric.eventually_nhds_iff.mp hg.eventually_analyticAt
  set r : ℝ := min R (min ε₁ ε₂) with hr
  have hr0 : 0 < r := lt_min hR (lt_min hε₁ hε₂)
  have hrR : r ≤ R := min_le_left _ _
  have hr₁ : r ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₂ : r ≤ ε₂ := (min_le_right _ _).trans (min_le_right _ _)
  rw [residue_eq_residue hFd hr0 hrR]
  set A : ℂ → ℂ := fun z => bs k * (x : ℂ) ^ (-z) * MellinZeroSetup.mellinContZero f a α (1 - z)
    with hA
  set G₁ : ℂ → ℂ := fun z => -((x : ℂ) ^ (-z) *
    (MellinZeroSetup.mellinContZero f a α (1 - z) * (mellin (trunc₁ h) z + g z))) with hG₁
  have hAd : DifferentiableOn ℂ A (ball z₀ r) :=
    DifferentiableOn.mul ((differentiableOn_const _).mul
      (differentiable_neg.const_cpow (Or.inl hx0)).differentiableOn)
      (hFc.mono (ball_subset_ball hrR))
  have hGd : DifferentiableOn ℂ G₁ (ball z₀ r) := by
    intro z hz
    have hzR : z ∈ ball z₀ R := ball_subset_ball hrR hz
    have h1 : DifferentiableAt ℂ g z := (hg' (lt_of_lt_of_le (mem_ball.mp hz) hr₂)).differentiableAt
    have h2 : DifferentiableAt ℂ (mellin (trunc₁ h)) z :=
      differentiableAt_mellin_trunc₁ H.h_loc H.h_zero (hball z hzR)
    exact ((((differentiable_neg.const_cpow (Or.inl hx0)).differentiableAt).mul
      (((hFc z hzR).differentiableAt (isOpen_ball.mem_nhds hzR)).mul
        (h2.add h1))).neg).differentiableWithinAt
  refine (residue_eq_of_eq_div_add hr0 hAd hGd fun z hz => ?_).trans ?_
  · have hne : z ≠ z₀ := fun h => by simp [h, annulus] at hz
    have hz₁ : dist z z₀ < ε₁ := by rw [dist_eq_norm]; exact lt_of_lt_of_le hz.2 hr₁
    have hsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
    simp only [regG, mellinCont, hA, hG₁]
    rw [hP z hz₁ hne]
    field_simp
    ring
  · simp only [hA]

/-! ### 2.6.62 -/

/-- The poles of `G` in the strip: `j + α` and `k + β`, `j, k < n`. -/
noncomputable def regPoles (α β : ℝ) (n : ℕ) : Finset ℂ :=
  (Finset.range n).image (fun j : ℕ => (j : ℂ) + α) ∪
    (Finset.range n).image (fun k : ℕ => (k : ℂ) + β)

theorem mem_regPoles {α β : ℝ} {n : ℕ} {z : ℂ} :
    z ∈ regPoles α β n ↔ (∃ j < n, z = j + α) ∨ ∃ k < n, z = k + β := by
  simp only [regPoles, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨k, hk, rfl⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨k, hk, rfl⟩

/-- `j + α ≠ k + β` when `α ≠ β`, `0 < α, β ≤ 1`. -/
theorem natCast_add_ne_natCast_add {α β : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hαβ : α ≠ β) (j k : ℕ) : (j : ℂ) + α ≠ k + β := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have hm : (((k : ℤ) - j : ℤ) : ℝ) = α - β := by push_cast; linarith
  have h1 : (-1 : ℤ) < (k : ℤ) - j := by exact_mod_cast (hm ▸ (by linarith : (-1 : ℝ) < α - β))
  have h2 : (k : ℤ) - j < 1 := by exact_mod_cast (hm ▸ (by linarith : α - β < (1 : ℝ)))
  have h3 : (k : ℤ) - j = 0 := by omega
  rw [h3] at hm
  exact hαβ (by push_cast at hm; linarith)

/-- **DLMF 2.6.62**: for `α ≠ β`, under the hypotheses of §2.5(ii) — a line `ℜz = p` in the strip
of convergence (`max(1−b, −c) < p < min(α, β)`), a line `ℜz = q` to the right of the first `n`
poles of each kind (`n − 1 + max(α, β) < q < n + min(α, β)`), the decay 2.5.34 of
`G(z) = 𝓜f(1−z) 𝓜h(z)` on the strip and its integrability on the two lines, and the
integrability conditions of the Parseval formula at `p` and at `q` —
`I(x) = ∑_{j<n} a_j 𝓜h(j+α) x^{−j−α} + ∑_{k<n} b_k 𝓜f(1−k−β) x^{−k−β} + δₙ(x)` for `x > 0`,
with `𝓜h`, `𝓜f` the continued transforms and `δₙ(x) = ∫₀^∞ fₙ(t) hₙ(xt) dt`. -/
theorem dlmf_2_6_62 {f h : ℝ → ℂ} {a bs : ℕ → ℂ} {α β b c : ℝ} (F : MellinZeroSetup f a α b)
    (H : MellinInfSetup h bs β c) (hαβ : α ≠ β) (n : ℕ) {p q : ℝ} (hp₁ : 1 - b < p) (hp₂ : -c < p)
    (hp₃ : p < α) (hp₄ : p < β) (hq₁ : n - 1 + α < q) (hq₂ : n - 1 + β < q) (hq₃ : q < n + α)
    (hq₄ : q < n + β) (hpq : p < q) {x : ℝ} (hx : 0 < x)
    (hint : VerticalIntegrable (mellin h) p ∨ Integrable fun y : ℝ => mellin f (1 - p - y * I))
    (h34 : ∀ ε > 0, ∀ᶠ y : ℝ in cocompact ℝ, ∀ σ ∈ Icc p q, ‖regG f h a bs α β (σ + y * I)‖ ≤ ε)
    (hGp : Integrable fun y : ℝ => regG f h a bs α β (p + y * I))
    (hGq : Integrable fun y : ℝ => regG f h a bs α β (q + y * I))
    (hint' : VerticalIntegrable (mellin (stieltjesRem h bs β n)) q ∨
      Integrable fun y : ℝ => mellin (zeroRem f a α n) (1 - q - y * I)) :
    mellinConvInt f h x =
      ∑ j ∈ Finset.range n, a j * mellinCont h bs β ((j : ℂ) + α) * (x : ℂ) ^ (-((j : ℂ) + α)) +
      ∑ k ∈ Finset.range n, bs k * MellinZeroSetup.mellinContZero f a α (1 - ((k : ℂ) + β)) *
        (x : ℂ) ^ (-((k : ℂ) + β)) +
      regDelta f h a bs α β n x := by
  have hα0 := F.α_pos
  have hα1 := F.α_le
  have hβ0 := H.β_pos
  have hβ1 := H.β_le
  -- the open set `U` and the poles `S`
  set p' : ℝ := max (1 - b) (-c) with hp'
  set q' : ℝ := (q + min (n + α) (n + β)) / 2 with hq'
  have hp'p : p' < p := max_lt hp₁ hp₂
  have hqq' : q < q' := by
    rw [hq']
    have := lt_min hq₃ hq₄
    linarith
  have hq'α : q' < n + α := by rw [hq']; linarith [min_le_left (n + α) (n + β)]
  have hq'β : q' < n + β := by rw [hq']; linarith [min_le_right (n + α) (n + β)]
  set U : Set ℂ := {z | p' < z.re ∧ z.re < q'} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hstrip : {z : ℂ | z.re ∈ Icc p q} ⊆ U := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  set S := regPoles α β n with hS
  have hSmem : ∀ s ∈ S, p < s.re ∧ s.re < q := by
    intro s hs
    rcases mem_regPoles.mp hs with ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
    · have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
      simp only [add_re, natCast_re, ofReal_re]
      constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
      simp only [add_re, natCast_re, ofReal_re]
      constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  -- analyticity of `G` on `U ∖ S`
  have hGd : DifferentiableOn ℂ (regG f h a bs α β) (U \ ↑S) := by
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, hzS⟩ := hz
    refine (differentiableAt_regG F H (by linarith [le_max_left (1 - b) (-c)])
      (by linarith [le_max_right (1 - b) (-c)]) (fun j hj => ?_)
      (fun k hk => ?_)).differentiableWithinAt
    · rcases lt_or_ge j n with hjn | hjn
      · exact hzS (Finset.mem_coe.mpr (mem_regPoles.mpr (Or.inl ⟨j, hjn, hj⟩)))
      · have : (n : ℝ) ≤ j := by exact_mod_cast hjn
        have := congrArg Complex.re hj
        simp at this
        linarith
    · rcases lt_or_ge k n with hkn | hkn
      · exact hzS (Finset.mem_coe.mpr (mem_regPoles.mpr (Or.inr ⟨k, hkn, hk⟩)))
      · have : (n : ℝ) ≤ k := by exact_mod_cast hkn
        have := congrArg Complex.re hk
        simp at this
        linarith
  -- `G` on the line `ℜz = p`
  have hGeq : ∀ y : ℝ, regG f h a bs α β (p + y * I) = mellinG f h (p + y * I) := fun y =>
    regG_eq_mellinG F H (by simp; linarith) (by simp; linarith) (by simp; linarith)
      (by simp; linarith)
  have hf : MellinConvergent f (1 - p) :=
    (F.mellinContZero_eq_mellin (by simp; linarith) (by simp; linarith)).1
  have hh : MellinConvergent h p := by
    have := (H.mellinCont_eq_mellin_rem (m := 0) (z := p) (by simpa using hp₂) (Or.inl rfl)
      (by simpa using hp₄)).1
    simpa [StieltjesSetup.rem_zero] using this
  -- isolating radii
  obtain ⟨R, hR⟩ := exists_isolating_radii S hUo fun s hs => by
    have := hSmem s (Finset.mem_coe.mp hs)
    exact ⟨by linarith, by linarith⟩
  have hshift := dlmf_2_5_35 hpq hf hh hint hx hUo hstrip hSmem hGd hGeq h34 hGp hGq R hR
  -- the residues
  have hres : ∀ s ∈ S, DifferentiableOn ℂ (fun z => -((x : ℂ) ^ (-z) * regG f h a bs α β z))
      (annulus s 0 (R s)) := by
    intro s hs z hz
    obtain ⟨hRs, hball, hsep⟩ := hR s hs
    have hzU : z ∈ U := hball (by rw [mem_ball, dist_eq_norm]; exact hz.2)
    have hzS : z ∉ (↑S : Set ℂ) := by
      intro hzS'
      have hzS' := Finset.mem_coe.mp hzS'
      by_cases hzs : z = s
      · rw [hzs] at hz
        exact absurd hz.1 (by simp)
      · have := hsep z hzS' hzs
        rw [dist_eq_norm] at this
        linarith [hz.2]
    have hUS : IsOpen (U \ ↑S) := hUo.sdiff S.finite_toSet.isClosed
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    exact ((((differentiable_neg.const_cpow (Or.inl hx0)).differentiableAt).mul
      ((hGd z ⟨hzU, hzS⟩).differentiableAt (hUS.mem_nhds ⟨hzU, hzS⟩))).neg).differentiableWithinAt
  -- poles are not in the ball around a different pole
  have hnot : ∀ s ∈ S, ∀ z ∈ ball s (R s), ∀ w ∈ S, w ≠ s → z ≠ w := by
    intro s hs z hz w hw hws hzw
    obtain ⟨-, -, hsep⟩ := hR s hs
    have := hsep w hw hws
    rw [hzw] at hz
    rw [mem_ball] at hz
    linarith
  have hres₁ : ∀ j ∈ Finset.range n,
      residue (fun z => -((x : ℂ) ^ (-z) * regG f h a bs α β z)) ((j : ℂ) + α) (R ((j : ℂ) + α)) =
      a j * (x : ℂ) ^ (-((j : ℂ) + α)) * mellinCont h bs β ((j : ℂ) + α) := by
    intro j hj
    have hs : (j : ℂ) + α ∈ S := mem_regPoles.mpr (Or.inl ⟨j, Finset.mem_range.mp hj, rfl⟩)
    obtain ⟨hRs, hball, -⟩ := hR _ hs
    refine residue_at_zero_pole F hx j hRs (hres _ hs) (fun z hz => ?_) fun z hz =>
      by linarith [(hball hz).1, le_max_left (1 - b) (-c)]
    have hzU := hball hz
    refine (DifferentiableAt.add (differentiableAt_mellin_trunc₁ H.h_loc H.h_zero
      (by linarith [hzU.1, le_max_right (1 - b) (-c)])) (differentiableAt_mellinTrunc₂ContZero
        H.h_loc StieltjesSetup.β_mono StieltjesSetup.β_tendsto H.h_exp
        fun k hk => ?_)).differentiableWithinAt
    rcases lt_or_ge k n with hkn | hkn
    · exact hnot _ hs z hz _ (mem_regPoles.mpr (Or.inr ⟨k, hkn, rfl⟩))
        (natCast_add_ne_natCast_add hβ0 hβ1 hα0 hα1 (Ne.symm hαβ) k j) hk
    · have : (n : ℝ) ≤ k := by exact_mod_cast hkn
      have := congrArg Complex.re hk
      simp at this
      linarith [hzU.2]
  have hres₂ : ∀ k ∈ Finset.range n,
      residue (fun z => -((x : ℂ) ^ (-z) * regG f h a bs α β z)) ((k : ℂ) + β) (R ((k : ℂ) + β)) =
      bs k * (x : ℂ) ^ (-((k : ℂ) + β)) *
        MellinZeroSetup.mellinContZero f a α (1 - ((k : ℂ) + β)) := by
    intro k hk
    have hs : (k : ℂ) + β ∈ S := mem_regPoles.mpr (Or.inr ⟨k, Finset.mem_range.mp hk, rfl⟩)
    obtain ⟨hRs, hball, -⟩ := hR _ hs
    refine residue_at_inf_pole H hx k hRs (hres _ hs) (fun z hz => ?_) fun z hz =>
      by linarith [(hball hz).1, le_max_right (1 - b) (-c)]
    have hzU := hball hz
    refine (DifferentiableAt.comp z (DifferentiableAt.add
      ((dlmf_2_5_25 (zeroExp_mono α) F.f_exp F.f_loc (zeroExp_tendsto α)).2.1 (1 - z)
        fun j hj => ?_)
      (differentiableAt_mellin_trunc₂ F.f_loc F.f_top
        (by simp; linarith [hzU.1, le_max_left (1 - b) (-c)])))
      ((differentiableAt_const _).sub differentiableAt_id)).differentiableWithinAt
    have hj' : z = j + α := by simp only [zeroExp] at hj; linear_combination -hj
    rcases lt_or_ge j n with hjn | hjn
    · exact hnot _ hs z hz _ (mem_regPoles.mpr (Or.inl ⟨j, hjn, rfl⟩))
        (natCast_add_ne_natCast_add hα0 hα1 hβ0 hβ1 hαβ j k) hj'
    · have : (n : ℝ) ≤ j := by exact_mod_cast hjn
      have := congrArg Complex.re hj'
      simp at this
      linarith [hzU.2]
  -- the sum over the poles
  have hdisj : Disjoint ((Finset.range n).image fun j : ℕ => (j : ℂ) + α)
      ((Finset.range n).image fun k : ℕ => (k : ℂ) + β) := by
    rw [Finset.disjoint_left]
    rintro z hz₁ hz₂
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz₁
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hz₂
    exact natCast_add_ne_natCast_add hα0 hα1 hβ0 hβ1 hαβ j k hk.symm
  have hinj₁ : ∀ x ∈ Finset.range n, ∀ y ∈ Finset.range n,
      (x : ℂ) + α = (y : ℂ) + α → x = y := fun x _ y _ hxy => by
    exact_mod_cast add_right_cancel hxy
  have hinj₂ : ∀ x ∈ Finset.range n, ∀ y ∈ Finset.range n,
      (x : ℂ) + β = (y : ℂ) + β → x = y := fun x _ y _ hxy => by
    exact_mod_cast add_right_cancel hxy
  rw [hS, regPoles, Finset.sum_union hdisj, Finset.sum_image hinj₁, Finset.sum_image hinj₂,
    Finset.sum_congr rfl hres₁, Finset.sum_congr rfl hres₂] at hshift
  -- the shifted line integral is `δₙ(x)`
  have hδ : (2 * π : ℂ)⁻¹ *
      (∫ y : ℝ, (x : ℂ) ^ (-((q : ℂ) + y * I)) * regG f h a bs α β (q + y * I)) =
      regDelta f h a bs α β n x := by
    have hf' : MellinConvergent (zeroRem f a α n) (1 - q) :=
      (F.dlmf_2_6_60 (n := n) (by simp; linarith) (by simp; linarith) (by simp; linarith)).1
    have hh' : MellinConvergent (stieltjesRem h bs β n) q := by
      refine (H.mellinCont_eq_mellin_rem (m := n) (z := q) (by simpa using (by linarith : -c < q))
        ?_ (by simpa using hq₄)).1
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact Or.inl hn
      · exact Or.inr (by simpa using hq₂)
    rw [regDelta, dlmf_2_5_5 hf' hh' hint' hx]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [regG_eq_mellinG_rem F H n (by simp; linarith) (by simp; linarith) (by simp; linarith)
      (by simp; linarith) ?_ (by simp; linarith), mellinG, mul_assoc]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr (by simp; linarith)
  rw [hshift, hδ]
  congr 2
  · exact Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun k _ => by ring

/-- **The remainder of 2.6.62**: `δₙ(x) = o(x^{−q})` as `x → +∞` (2.5.36), under the hypotheses
of `dlmf_2_6_62` for all large `x`. -/
theorem dlmf_2_6_62_remainder {f h : ℝ → ℂ} {a bs : ℕ → ℂ} {α β b c : ℝ}
    (F : MellinZeroSetup f a α b) (H : MellinInfSetup h bs β c) (n : ℕ) {q : ℝ} (hq₀ : 1 - b < q)
    (hq₀' : -c < q) (hq₁ : n - 1 + α < q) (hq₂ : n - 1 + β < q) (hq₃ : q < n + α) (hq₄ : q < n + β)
    (hint' : VerticalIntegrable (mellin (stieltjesRem h bs β n)) q ∨
      Integrable fun y : ℝ => mellin (zeroRem f a α n) (1 - q - y * I)) :
    IsLittleODLMF atTop (fun x : ℝ => regDelta f h a bs α β n x)
      fun x : ℝ => (x : ℂ) ^ (-(q : ℂ)) := by
  have hf' : MellinConvergent (zeroRem f a α n) (1 - q) :=
    (F.dlmf_2_6_60 (n := n) (by simp; linarith) (by simp; linarith) (by simp; linarith)).1
  have hh' : MellinConvergent (stieltjesRem h bs β n) q := by
    refine (H.mellinCont_eq_mellin_rem (m := n) (z := q) (by simpa using hq₀') ?_
      (by simpa using hq₄)).1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr (by simpa using hq₂)
  have h36 := dlmf_2_5_36 (mellinG (zeroRem f a α n) (stieltjesRem h bs β n)) q
  unfold IsLittleODLMF at h36 ⊢
  refine h36.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [regDelta, dlmf_2_5_5 hf' hh' hint' hx]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [mellinG, mul_assoc]

end Azurite.DLMF
