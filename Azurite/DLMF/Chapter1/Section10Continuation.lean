/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# DLMF §1.10(ii): Analytic Continuation

Formalizations of <https://dlmf.nist.gov/1.10.ii>.

* Identity theorem: `dlmf_1_10_ii_identity` (agreement on a set with a limit point in the domain
  `D = D₁ ∩ D₂`, assumed connected), `dlmf_1_10_ii_identity_arc` (agreement on an arc; `accPt_arc`).
* `IsAnalyticContinuation` (`(f₁, D₁)`, `(f₂, D₂)`), `IsAnalyticContinuation.unique`,
  `IsContinuationAlong` (continuation along a path by a chain of function elements).
* Functional equations: `dlmf_1_10_ii_functional` (an identity proven on a real segment holds on
  any connected domain of analyticity), `dlmf_1_10_ii_functional₂` (two variables: continue in
  each in turn), example `exp_add_of_real` (`e^{z + w} = e^z e^w` from the real case).
* 1.10.5 (Schwarz reflection principle): `dlmf_1_10_5`, for `f` analytic on an open `Ω` in the
  upper half-plane, continuous on `Ω ∪ L` (`L` real points) and real on `L`, with
  `Ω ∪ L ∪ conj Ω` open (in DLMF's setting `Ω` is the interior of a simple closed contour made of a
  real segment `AB` and an arc above it, `L` the open segment).  The continuation is
  `schwarzReflection f`; analyticity across `L` is Morera's theorem
  (`isConservativeOn_and_continuousOn_iff_isDifferentiableOn`) on small disks, with rectangle
  integrals split along the real axis (`rectBoundary_split`) and each half handled by Cauchy's
  theorem with boundary continuity.
-/

open Filter Topology Set Metric Complex ComplexConjugate
open scoped Interval

namespace Azurite.DLMF

/-! ### Identity theorem and analytic continuation -/

/-- DLMF §1.10(ii): analytic `f₁` on `D₁` and `f₂` on `D₂` that agree on a set with a limit point
in the domain `D = D₁ ∩ D₂` agree throughout `D`. -/
theorem dlmf_1_10_ii_identity {f₁ f₂ : ℂ → ℂ} {D₁ D₂ S : Set ℂ} (hD₁ : IsOpen D₁)
    (hD₂ : IsOpen D₂) (hf₁ : DifferentiableOn ℂ f₁ D₁) (hf₂ : DifferentiableOn ℂ f₂ D₂)
    (hD : IsPreconnected (D₁ ∩ D₂)) {z₀ : ℂ} (hz₀ : z₀ ∈ D₁ ∩ D₂) (hacc : AccPt z₀ (𝓟 S))
    (heq : EqOn f₁ f₂ S) : EqOn f₁ f₂ (D₁ ∩ D₂) := by
  have hU := hD₁.inter hD₂
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    ((hf₁.mono inter_subset_left).analyticOnNhd hU)
    ((hf₂.mono inter_subset_right).analyticOnNhd hU) hD hz₀ ?_
  rw [accPt_iff_frequently] at hacc
  rw [frequently_nhdsWithin_iff]
  exact hacc.mono fun y hy => ⟨heq hy.2, hy.1⟩

/-- An arc (continuous injective image of `[a, b]`, `a < b`) has its initial point as a limit
point. -/
theorem accPt_arc {z : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hz : ContinuousOn z (Icc a b))
    (hinj : InjOn z (Icc a b)) : AccPt (z a) (𝓟 (z '' Icc a b)) := by
  rw [accPt_iff_frequently]
  have ht : Tendsto (fun s : ℝ => z s) (𝓝[Ioc a b] a) (𝓝 (z a)) :=
    ((hz a (left_mem_Icc.mpr hab.le)).mono Ioc_subset_Icc_self).tendsto
  have hne : (𝓝[Ioc a b] a).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc hab.ne]
    exact left_mem_Icc.mpr hab.le
  have := hne
  have h2 : ∃ᶠ s in 𝓝[Ioc a b] a, z s ≠ z a ∧ z s ∈ z '' Icc a b := by
    refine Eventually.frequently ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    refine ⟨fun h0 => ?_, ⟨s, Ioc_subset_Icc_self hs, rfl⟩⟩
    exact absurd (hinj (Ioc_subset_Icc_self hs) (left_mem_Icc.mpr hab.le) h0) (ne_of_gt hs.1)
  exact ht.frequently h2

/-- DLMF §1.10(ii): analytic functions agreeing on an arc in `D` agree throughout `D`. -/
theorem dlmf_1_10_ii_identity_arc {f₁ f₂ : ℂ → ℂ} {D₁ D₂ : Set ℂ} (hD₁ : IsOpen D₁)
    (hD₂ : IsOpen D₂) (hf₁ : DifferentiableOn ℂ f₁ D₁) (hf₂ : DifferentiableOn ℂ f₂ D₂)
    (hD : IsPreconnected (D₁ ∩ D₂)) {z : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hz : ContinuousOn z (Icc a b)) (hinj : InjOn z (Icc a b)) (hzD : z '' Icc a b ⊆ D₁ ∩ D₂)
    (heq : ∀ t ∈ Icc a b, f₁ (z t) = f₂ (z t)) : EqOn f₁ f₂ (D₁ ∩ D₂) :=
  dlmf_1_10_ii_identity hD₁ hD₂ hf₁ hf₂ hD (hzD ⟨a, left_mem_Icc.mpr hab.le, rfl⟩)
    (accPt_arc hab hz hinj) (by rintro _ ⟨t, ht, rfl⟩; exact heq t ht)

/-- `(f₂, D₂)` is an analytic continuation of `(f₁, D₁)`: both analytic on open sets that
overlap, and equal on the overlap. -/
def IsAnalyticContinuation (f₁ : ℂ → ℂ) (D₁ : Set ℂ) (f₂ : ℂ → ℂ) (D₂ : Set ℂ) : Prop :=
  IsOpen D₁ ∧ IsOpen D₂ ∧ DifferentiableOn ℂ f₁ D₁ ∧ DifferentiableOn ℂ f₂ D₂ ∧
    (D₁ ∩ D₂).Nonempty ∧ EqOn f₁ f₂ (D₁ ∩ D₂)

/-- `f₁` on `D₁` is analytically continued along the path `z(t)`, `a ≤ t ≤ b`, by the chain
`(f₀, D₀), …, (f_{n−1}, D_{n−1})` over the subdivision `a = t₀ < ⋯ < tₙ = b`. -/
def IsContinuationAlong (z : ℝ → ℂ) (a b : ℝ) (n : ℕ) (t : ℕ → ℝ) (f : ℕ → ℂ → ℂ)
    (D : ℕ → Set ℂ) : Prop :=
  t 0 = a ∧ t n = b ∧ (∀ j < n, t j < t (j + 1)) ∧
    (∀ j < n, z '' Icc (t j) (t (j + 1)) ⊆ D j) ∧
    ∀ j, j + 1 < n → IsAnalyticContinuation (f j) (D j) (f (j + 1)) (D (j + 1))

/-- The analytic continuation of `(f₁, D₁)` to `D₂` is unique when `D₁ ∩ D₂` is connected. -/
theorem IsAnalyticContinuation.unique {f₁ f₂ g₂ : ℂ → ℂ} {D₁ D₂ : Set ℂ}
    (hf : IsAnalyticContinuation f₁ D₁ f₂ D₂) (hg : IsAnalyticContinuation f₁ D₁ g₂ D₂)
    (hD₂ : IsPreconnected D₂) : EqOn f₂ g₂ D₂ := by
  obtain ⟨hD₁, hD₂o, -, hf₂, ⟨z₀, hz₀⟩, hfeq⟩ := hf
  obtain ⟨-, -, -, hg₂, -, hgeq⟩ := hg
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (hf₂.analyticOnNhd hD₂o)
    (hg₂.analyticOnNhd hD₂o) hD₂ hz₀.2 ?_
  have hmem : D₁ ∩ D₂ ∈ 𝓝 z₀ := (hD₁.inter hD₂o).mem_nhds hz₀
  refine (Eventually.frequently ?_)
  filter_upwards [nhdsWithin_le_nhds hmem] with w hw
  exact (hfeq hw).symm.trans (hgeq hw)

/-! ### Functional equations -/

/-- DLMF §1.10(ii): continuation reduces a transformation or functional equation to (a) proving it
for real variables and (b) finding a (connected) domain where both sides are analytic.  If `g`,
`h` are analytic on a connected open `D` containing the real segment `[a, b]`, `a < b`, and
`g = h` there, then `g = h` throughout `D`. -/
theorem dlmf_1_10_ii_functional {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {g h : ℂ → ℂ} (hg : DifferentiableOn ℂ g D) (hh : DifferentiableOn ℂ h D) {a b : ℝ}
    (hab : a < b) (hsub : ∀ x ∈ Icc a b, (x : ℂ) ∈ D) (heq : ∀ x ∈ Icc a b, g x = h x) :
    EqOn g h D := by
  have := dlmf_1_10_ii_identity_arc hD hD hg hh (by rwa [inter_self]) (z := fun t : ℝ => (t : ℂ))
    hab continuous_ofReal.continuousOn ofReal_injective.injOn
    (by rintro _ ⟨t, ht, rfl⟩; exact ⟨hsub t ht, hsub t ht⟩) heq
  rwa [inter_self] at this

/-- DLMF §1.10(ii), functional equations in two variables (addition theorems): if `F(z, w)` and
`G(z, w)` are entire in each variable and agree for real `z`, `w`, they agree for all complex
`z`, `w` (continue first in `z`, then in `w`). -/
theorem dlmf_1_10_ii_functional₂ {F G : ℂ → ℂ → ℂ} (hF₁ : ∀ w, Differentiable ℂ fun z => F z w)
    (hF₂ : ∀ z, Differentiable ℂ (F z)) (hG₁ : ∀ w, Differentiable ℂ fun z => G z w)
    (hG₂ : ∀ z, Differentiable ℂ (G z)) (heq : ∀ x y : ℝ, F x y = G x y) (z w : ℂ) :
    F z w = G z w := by
  have step1 : ∀ y : ℝ, ∀ z, F z y = G z y := fun y z =>
    dlmf_1_10_ii_functional (D := univ) isOpen_univ isPreconnected_univ
      (hF₁ y).differentiableOn (hG₁ y).differentiableOn zero_lt_one (fun _ _ => mem_univ _)
      (fun x _ => heq x y) (mem_univ z)
  exact dlmf_1_10_ii_functional (D := univ) isOpen_univ isPreconnected_univ
    (hF₂ z).differentiableOn (hG₂ z).differentiableOn zero_lt_one (fun _ _ => mem_univ _)
    (fun y _ => step1 y z) (mem_univ w)

/-- Example: the addition theorem `e^{z + w} = e^z e^w` follows from the real one. -/
theorem exp_add_of_real (z w : ℂ) : cexp (z + w) = cexp z * cexp w :=
  dlmf_1_10_ii_functional₂ (F := fun z w => cexp (z + w)) (G := fun z w => cexp z * cexp w)
    (fun _ => by fun_prop) (fun _ => by fun_prop) (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun x y => by
      rw [← ofReal_add, ← ofReal_exp, ← ofReal_exp, ← ofReal_exp, Real.exp_add, ofReal_mul]) z w

/-! ### Schwarz reflection principle -/

/-- The reflection of `f` across the real axis: `f(z)` for `Im z ≥ 0`, `conj f(conj z)` below. -/
noncomputable def schwarzReflection (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else conj (f (conj z))

/-- The integral of `f` around the boundary of the rectangle with opposite corners `p`, `q`. -/
noncomputable def rectBoundary (f : ℂ → ℂ) (p q : ℂ) : ℂ :=
  (∫ x : ℝ in p.re..q.re, f (x + p.im * I)) - (∫ x : ℝ in p.re..q.re, f (x + q.im * I)) +
    I • (∫ y : ℝ in p.im..q.im, f (q.re + y * I)) - I • (∫ y : ℝ in p.im..q.im, f (p.re + y * I))

theorem continuousOn_vertical {f : ℂ → ℂ} {p q : ℂ} (hc : ContinuousOn f (Rectangle p q))
    {x : ℝ} (hx : x ∈ [[p.re, q.re]]) : ContinuousOn (fun t : ℝ => f (x + t * I)) [[p.im, q.im]] :=
  hc.comp (by fun_prop) fun t ht => by
    show (x : ℂ) + t * I ∈ [[p.re, q.re]] ×ℂ [[p.im, q.im]]
    rw [mem_reProdIm]
    simpa using ⟨hx, ht⟩

/-- Cutting a rectangle along the horizontal line `Im z = y`. -/
theorem rectBoundary_split {f : ℂ → ℂ} {p q : ℂ} (hc : ContinuousOn f (Rectangle p q)) {y : ℝ}
    (hy : y ∈ [[p.im, q.im]]) :
    rectBoundary f p q = rectBoundary f p ⟨q.re, y⟩ + rectBoundary f ⟨p.re, y⟩ q := by
  have hq := continuousOn_vertical hc (right_mem_uIcc (a := p.re) (b := q.re))
  have hp := continuousOn_vertical hc (left_mem_uIcc (a := p.re) (b := q.re))
  have i1 := (hq.mono (uIcc_subset_uIcc_left hy)).intervalIntegrable (μ := MeasureTheory.volume)
  have i2 := (hq.mono (uIcc_subset_uIcc_right hy)).intervalIntegrable (μ := MeasureTheory.volume)
  have i3 := (hp.mono (uIcc_subset_uIcc_left hy)).intervalIntegrable (μ := MeasureTheory.volume)
  have i4 := (hp.mono (uIcc_subset_uIcc_right hy)).intervalIntegrable (μ := MeasureTheory.volume)
  simp only [rectBoundary]
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    ← intervalIntegral.integral_add_adjacent_intervals i3 i4]
  simp only [smul_add]
  abel

section Reflection

variable {f : ℂ → ℂ} {Ω : Set ℂ} {L : Set ℝ}

/-- **DLMF 1.10.5** (Schwarz reflection principle): let `f` be analytic on an open set `Ω` in the
upper half-plane, continuous on `Ω ∪ L` for a set `L` of real points, and real on `L`. If
`U = Ω ∪ L ∪ conj Ω` is open, `f` continues analytically across `L` by reflection,
`f(z̄) = conj f(z)`: `schwarzReflection f` is analytic on `U`, equals `f` on `Ω ∪ L`, and
satisfies the reflection identity on `U`. -/
theorem dlmf_1_10_5 (hΩo : IsOpen Ω) (hΩ : ∀ z ∈ Ω, 0 < z.im)
    (hU : IsOpen (Ω ∪ (fun x : ℝ => (x : ℂ)) '' L ∪ conj '' Ω))
    (hfc : ContinuousOn f (Ω ∪ (fun x : ℝ => (x : ℂ)) '' L)) (hfd : DifferentiableOn ℂ f Ω)
    (hreal : ∀ x ∈ L, conj (f x) = f x) :
    DifferentiableOn ℂ (schwarzReflection f) (Ω ∪ (fun x : ℝ => (x : ℂ)) '' L ∪ conj '' Ω) ∧
      EqOn (schwarzReflection f) f (Ω ∪ (fun x : ℝ => (x : ℂ)) '' L) ∧
      ∀ z ∈ Ω ∪ (fun x : ℝ => (x : ℂ)) '' L ∪ conj '' Ω,
        schwarzReflection f (conj z) = conj (schwarzReflection f z) := by
  set U := Ω ∪ (fun x : ℝ => (x : ℂ)) '' L ∪ conj '' Ω with hUdef
  set F := schwarzReflection f with hF
  have hpos : ∀ z ∈ U, 0 < z.im → z ∈ Ω := by
    rintro z ((hz | ⟨x, -, rfl⟩) | ⟨w, hw, rfl⟩) h
    · exact hz
    · simp at h
    · have := hΩ w hw
      simp at h
      linarith
  have hneg : ∀ z ∈ U, z.im < 0 → conj z ∈ Ω := by
    rintro z ((hz | ⟨x, -, rfl⟩) | ⟨w, hw, rfl⟩) h
    · linarith [hΩ z hz]
    · simp at h
    · rwa [conj_conj]
  have hzero : ∀ z ∈ U, z.im = 0 → ∃ x ∈ L, (x : ℂ) = z := by
    rintro z ((hz | hz) | ⟨w, hw, rfl⟩) h
    · linarith [hΩ z hz]
    · exact hz
    · have := hΩ w hw
      simp at h
      linarith
  have hFpos : ∀ z, 0 ≤ z.im → F z = f z := fun z h => by
    simp only [hF, schwarzReflection, h, ↓reduceIte]
  have hFneg : ∀ z, z.im < 0 → F z = conj (f (conj z)) := fun z h => by
    simp only [hF, schwarzReflection, not_le.mpr h, ↓reduceIte]
  have hdpos : ∀ z ∈ U, 0 < z.im → DifferentiableAt ℂ F z := fun z hz h => by
    have hev : F =ᶠ[𝓝 z] f := by
      filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds h] with w hw
      exact hFpos w (le_of_lt hw)
    exact (hfd.differentiableAt (hΩo.mem_nhds (hpos z hz h))).congr_of_eventuallyEq hev
  have hdneg : ∀ z ∈ U, z.im < 0 → DifferentiableAt ℂ F z := fun z hz h => by
    have hev : F =ᶠ[𝓝 z] (conj ∘ f ∘ conj) := by
      filter_upwards [isOpen_lt continuous_im continuous_const |>.mem_nhds h] with w hw
      exact hFneg w hw
    have hd := (hfd.differentiableAt (hΩo.mem_nhds (hneg z hz h))).hasDerivAt.conj_conj
    rw [conj_conj] at hd
    exact hd.differentiableAt.congr_of_eventuallyEq hev
  -- continuity of `F` on `U`
  have hcont : ContinuousOn F U := by
    intro z hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact (hdneg z hz h).continuousAt.continuousWithinAt
    · obtain ⟨x, hx, rfl⟩ := hzero z hz h
      have hxU : (x : ℂ) ∈ Ω ∪ (fun x : ℝ => (x : ℂ)) '' L := Or.inr ⟨x, hx, rfl⟩
      have h1 : ContinuousWithinAt F (U ∩ {w | 0 ≤ w.im}) x := by
        have hsub : U ∩ {w | 0 ≤ w.im} ⊆ Ω ∪ (fun x : ℝ => (x : ℂ)) '' L := by
          rintro w ⟨hw, hw0⟩
          rcases (show (0 : ℝ) ≤ w.im from hw0).lt_or_eq with h' | h'
          · exact Or.inl (hpos w hw h')
          · obtain ⟨y, hy, rfl⟩ := hzero w hw h'.symm
            exact Or.inr ⟨y, hy, rfl⟩
        refine ((hfc x hxU).mono hsub).congr (fun w hw => hFpos w hw.2) (hFpos _ (by simp))
      have h2 : ContinuousWithinAt F (U ∩ {w | w.im ≤ 0}) x := by
        have hsub : MapsTo conj (U ∩ {w | w.im ≤ 0}) (Ω ∪ (fun x : ℝ => (x : ℂ)) '' L) := by
          rintro w ⟨hw, hw0⟩
          rcases (show w.im ≤ 0 from hw0).lt_or_eq with h' | h'
          · exact Or.inl (hneg w hw h')
          · obtain ⟨y, hy, rfl⟩ := hzero w hw h'
            exact Or.inr ⟨y, hy, by simp⟩
        have hG : ContinuousWithinAt (conj ∘ f ∘ conj) (U ∩ {w | w.im ≤ 0}) x := by
          have := (hfc (conj (x : ℂ)) (by simpa using hxU)).comp
            continuous_conj.continuousWithinAt hsub
          exact continuous_conj.continuousAt.comp_continuousWithinAt this
        refine hG.congr (fun w hw => ?_) ?_
        · rcases (show w.im ≤ 0 from hw.2).lt_or_eq with h' | h'
          · exact hFneg w h'
          · obtain ⟨y, hy, rfl⟩ := hzero w hw.1 h'
            simp [hFpos _ (by simp : (0 : ℝ) ≤ ((y : ℂ)).im), hreal y hy]
        · simp [hFpos _ (by simp : (0 : ℝ) ≤ ((x : ℂ)).im), hreal x hx]
      have h3 := h1.union h2
      rw [← inter_union_distrib_left] at h3
      have hall : {w : ℂ | 0 ≤ w.im} ∪ {w | w.im ≤ 0} = univ :=
        eq_univ_of_forall fun w => le_total 0 w.im
      rw [hall, inter_univ] at h3
      exact h3
    · exact (hdpos z hz h).continuousAt.continuousWithinAt
  -- boundary integrals of rectangles on one side of the axis vanish
  have hhalf : ∀ p q : ℂ, Rectangle p q ⊆ U →
      (0 ≤ min p.im q.im ∨ max p.im q.im ≤ 0) → rectBoundary F p q = 0 := by
    intro p q hR hcase
    refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F p q
      (hcont.mono hR) fun z hz => ?_
    have hzR : z ∈ U := hR (by
      show z ∈ [[p.re, q.re]] ×ℂ [[p.im, q.im]]
      rw [mem_reProdIm] at hz ⊢
      exact ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)
    rw [mem_reProdIm] at hz
    rcases hcase with h | h
    · exact (hdpos z hzR (lt_of_le_of_lt h hz.2.1)).differentiableWithinAt
    · exact (hdneg z hzR (lt_of_lt_of_le hz.2.2 h)).differentiableWithinAt
  have hrect : ∀ p q : ℂ, Rectangle p q ⊆ U → rectBoundary F p q = 0 := by
    intro p q hR
    by_cases hcase : 0 ≤ min p.im q.im ∨ max p.im q.im ≤ 0
    · exact hhalf p q hR hcase
    push Not at hcase
    have h0 : (0 : ℝ) ∈ [[p.im, q.im]] := ⟨hcase.1.le, hcase.2.le⟩
    have hside : ∀ a : ℝ, 0 ≤ min a 0 ∨ max a 0 ≤ 0 := fun a => by
      rcases le_total 0 a with h | h
      · left; simp [h]
      · right; simp [h]
    have hside' : ∀ a : ℝ, 0 ≤ min 0 a ∨ max 0 a ≤ 0 := fun a => by
      rw [min_comm, max_comm]; exact hside a
    have hR1 : Rectangle p ⟨q.re, 0⟩ ⊆ U := fun z hz => hR (by
      simp only [Rectangle, mem_reProdIm] at hz ⊢
      exact ⟨hz.1, uIcc_subset_uIcc_left h0 hz.2⟩)
    have hR2 : Rectangle ⟨p.re, 0⟩ q ⊆ U := fun z hz => hR (by
      simp only [Rectangle, mem_reProdIm] at hz ⊢
      exact ⟨hz.1, uIcc_subset_uIcc_right h0 hz.2⟩)
    rw [rectBoundary_split (hcont.mono hR) h0, hhalf _ _ hR1 (hside p.im),
      hhalf _ _ hR2 (hside' q.im), add_zero]
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · rcases lt_trichotomy z.im 0 with h | h | h
    · exact (hdneg z hz h).differentiableWithinAt
    · obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU z hz
      have hdiff : DifferentiableOn ℂ F (ball z ρ) :=
        (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_ball).mp
          ⟨fun p q hpq => by
            have := wedgeIntegral_add_wedgeIntegral_eq p q F
            rw [show (∫ x : ℝ in p.re..q.re, F (x + p.im * I)) -
                (∫ x : ℝ in p.re..q.re, F (x + q.im * I)) +
                I • (∫ y : ℝ in p.im..q.im, F (q.re + y * I)) -
                I • (∫ y : ℝ in p.im..q.im, F (p.re + y * I)) = rectBoundary F p q from rfl,
              hrect p q (hpq.trans hball)] at this
            exact eq_neg_of_add_eq_zero_left this, hcont.mono hball⟩
      exact (hdiff.differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hρ))).differentiableWithinAt
    · exact (hdpos z hz h).differentiableWithinAt
  · rcases hz with hz | ⟨x, -, rfl⟩
    · exact hFpos z (hΩ z hz).le
    · exact hFpos _ (by simp)
  · rcases lt_trichotomy z.im 0 with h | h | h
    · rw [hFneg z h, hFpos _ (by simp; linarith), conj_conj]
    · obtain ⟨x, hx, rfl⟩ := hzero z hz h
      simp [hFpos _ (by simp : (0 : ℝ) ≤ ((x : ℂ)).im), hreal x hx]
    · rw [hFpos z h.le, hFneg _ (by simp; linarith), conj_conj]

end Reflection

end Azurite.DLMF
