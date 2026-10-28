/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.JordanCurve.WindingNumber
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Interior and exterior of a closed curve in `ℂ`

For a closed curve `c : [a, b] → ℂ` we define the *interior* as the union of the bounded
connected components of the complement of its image and the *exterior* as the union of the
unbounded ones.  For a Jordan curve (continuous, injective on `[a, b)`, `c a = c b`) the Jordan
curve theorem `Azurite.JordanCurve.jordan_curve` (vendored from `jordan_pick`) says there is
exactly one of each; we transport it from the sphere-parametrized statement to interval
parametrizations via `AddCircle.liftIco`, `AddCircle.homeomorphCircle`, `Arcs.circleHomeoSphere`
and the isometry `Arcs.complexLIE : ℂ ≃ₗᵢ[ℝ] Plane`.

Main results (`h : IsJordanCurve c a b`): `h.exists_mem_jordanInterior`,
`h.jordanInterior_eq` (the interior is the unique bounded component),
`h.isConnected_jordanInterior`, `isOpen_jordanInterior`, and the same for the exterior.  For a
closed piecewise-`C¹` curve the winding number is constant on the interior
(`ClosedPiecewiseC1.windingNumber_eq_of_mem_jordanInterior`); a curve is *positively oriented*
when that constant is `1` (`ClosedPiecewiseC1.IsPositivelyOriented`); that it is always `±1`
for a Jordan curve is proved in `JordanCurve/Orientation`.  Also: the closure of the interior
lies in the interior plus the curve (`closure_jordanInterior_subset`), and the interior lies in
any ball about `0` containing the curve (`jordanInterior_subset_closedBall`).
-/

namespace Azurite.JordanCurve

open Set Filter Topology Bornology Function

/-- A Jordan curve parametrized by `[a, b]`: continuous, injective on `[a, b)`, closed. -/
structure IsJordanCurve (c : ℝ → ℂ) (a b : ℝ) : Prop where
  lt : a < b
  continuousOn : ContinuousOn c (Icc a b)
  injOn : InjOn c (Ico a b)
  closed : c a = c b

/-- The interior of a closed curve: the union of the bounded connected components of the
complement of its image. -/
def jordanInterior (c : ℝ → ℂ) (a b : ℝ) : Set ℂ :=
  {p | p ∉ c '' Icc a b ∧ IsBounded (connectedComponentIn (c '' Icc a b)ᶜ p)}

/-- The exterior of a closed curve: the union of the unbounded connected components of the
complement of its image. -/
def jordanExterior (c : ℝ → ℂ) (a b : ℝ) : Set ℂ :=
  {p | p ∉ c '' Icc a b ∧ ¬ IsBounded (connectedComponentIn (c '' Icc a b)ᶜ p)}

variable {c : ℝ → ℂ} {a b : ℝ}

theorem jordanInterior_subset : jordanInterior c a b ⊆ (c '' Icc a b)ᶜ := fun _ hp => hp.1

theorem jordanExterior_subset : jordanExterior c a b ⊆ (c '' Icc a b)ᶜ := fun _ hp => hp.1

theorem jordanInterior_disjoint_jordanExterior :
    Disjoint (jordanInterior c a b) (jordanExterior c a b) :=
  disjoint_left.mpr fun _ hp hq => hq.2 hp.2

/-- The complement of the curve is the disjoint union of interior and exterior. -/
theorem compl_image_eq_union :
    (c '' Icc a b)ᶜ = jordanInterior c a b ∪ jordanExterior c a b := by
  ext p
  constructor
  · intro hp
    by_cases hb : IsBounded (connectedComponentIn (c '' Icc a b)ᶜ p)
    · exact Or.inl ⟨hp, hb⟩
    · exact Or.inr ⟨hp, hb⟩
  · rintro (h | h) <;> exact h.1

theorem connectedComponentIn_subset_jordanInterior {p : ℂ} (hp : p ∈ jordanInterior c a b) :
    connectedComponentIn (c '' Icc a b)ᶜ p ⊆ jordanInterior c a b := fun q hq =>
  ⟨connectedComponentIn_subset _ _ hq, by rw [← connectedComponentIn_eq hq]; exact hp.2⟩

theorem connectedComponentIn_subset_jordanExterior {p : ℂ} (hp : p ∈ jordanExterior c a b) :
    connectedComponentIn (c '' Icc a b)ᶜ p ⊆ jordanExterior c a b := fun q hq =>
  ⟨connectedComponentIn_subset _ _ hq, by rw [← connectedComponentIn_eq hq]; exact hp.2⟩

theorem isOpen_compl_image (hc : ContinuousOn c (Icc a b)) : IsOpen (c '' Icc a b)ᶜ :=
  (isCompact_Icc.image_of_continuousOn hc).isClosed.isOpen_compl

theorem isOpen_jordanInterior (hc : ContinuousOn c (Icc a b)) : IsOpen (jordanInterior c a b) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  exact ⟨connectedComponentIn (c '' Icc a b)ᶜ p, connectedComponentIn_subset_jordanInterior hp,
    (isOpen_compl_image hc).connectedComponentIn, mem_connectedComponentIn hp.1⟩

theorem isOpen_jordanExterior (hc : ContinuousOn c (Icc a b)) : IsOpen (jordanExterior c a b) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  exact ⟨connectedComponentIn (c '' Icc a b)ᶜ p, connectedComponentIn_subset_jordanExterior hp,
    (isOpen_compl_image hc).connectedComponentIn, mem_connectedComponentIn hp.1⟩

/-- Points of the closure of the interior that are off the curve lie in the interior. -/
theorem closure_jordanInterior_subset (hc : ContinuousOn c (Icc a b)) :
    closure (jordanInterior c a b) ⊆ jordanInterior c a b ∪ c '' Icc a b := by
  intro p hp
  by_cases hpc : p ∈ c '' Icc a b
  · exact Or.inr hpc
  refine Or.inl ⟨hpc, ?_⟩
  have hopen : IsOpen (connectedComponentIn (c '' Icc a b)ᶜ p) :=
    (isOpen_compl_image hc).connectedComponentIn
  obtain ⟨q, hq, hqS⟩ := mem_closure_iff.mp hp _ hopen (mem_connectedComponentIn hpc)
  rw [connectedComponentIn_eq hq]
  exact hqS.2

/-- The interior of a closed curve lies in any closed ball centred at `0` containing the curve. -/
theorem jordanInterior_subset_closedBall {R : ℝ} (hR : 0 ≤ R)
    (hsub : c '' Icc a b ⊆ Metric.closedBall 0 R) :
    jordanInterior c a b ⊆ Metric.closedBall 0 R := by
  intro p hp
  rw [mem_closedBall_zero_iff]
  by_contra hpR
  push Not at hpR
  set E : Set ℂ := {z : ℂ | R < ‖z‖} with hE
  have hEconn : IsConnected E := ClosedPiecewiseC1.isConnected_compl_closedBall_complex hR
  have hEsub : E ⊆ (c '' Icc a b)ᶜ := fun z hz hzc => by
    have := hsub hzc
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.mpr hz)
  have hsubE : E ⊆ connectedComponentIn (c '' Icc a b)ᶜ p :=
    hEconn.isPreconnected.subset_connectedComponentIn hpR hEsub
  obtain ⟨M, hM⟩ := (hp.2.subset hsubE).subset_closedBall 0
  set r : ℝ := max M R + 1 with hr
  have hr0 : 0 ≤ r := by positivity
  have hzE : ((r : ℝ) : ℂ) ∈ E := by
    show R < ‖((r : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg hr0]
    linarith [le_max_right M R]
  have := hM hzE
  rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr0] at this
  linarith [le_max_left M R]

/-! ### Transport through the isometry `ℂ ≃ₗᵢ[ℝ] Plane` -/

theorem isBounded_image_complexLIE_iff (S : Set ℂ) :
    IsBounded (Arcs.complexLIE '' S) ↔ IsBounded S := by
  constructor
  · intro hS
    have := Arcs.complexLIE.symm.isometry.lipschitzWith.isBounded_image hS
    rwa [image_image, show (fun z => Arcs.complexLIE.symm (Arcs.complexLIE z)) = id from
      funext fun z => Arcs.complexLIE.symm_apply_apply z, image_id] at this
  · exact fun hS => Arcs.complexLIE.isometry.lipschitzWith.isBounded_image hS

theorem image_connectedComponentIn_compl {p : ℂ} (hp : p ∉ c '' Icc a b) :
    Arcs.complexLIE '' connectedComponentIn (c '' Icc a b)ᶜ p =
      connectedComponentIn (Arcs.complexLIE '' (c '' Icc a b))ᶜ (Arcs.complexLIE p) := by
  have := Arcs.complexLIE.toHomeomorph.image_connectedComponentIn (s := (c '' Icc a b)ᶜ) hp
  rwa [LinearIsometryEquiv.coe_toHomeomorph, image_compl_eq Arcs.complexLIE.bijective] at this

theorem mem_image_complexLIE_iff {p : ℂ} (S : Set ℂ) :
    Arcs.complexLIE p ∈ Arcs.complexLIE '' S ↔ p ∈ S :=
  Arcs.complexLIE.injective.mem_set_image

namespace IsJordanCurve

variable (h : IsJordanCurve c a b)
include h

theorem image_Ico_eq : c '' Ico a b = c '' Icc a b := by
  rw [← Ico_insert_right h.lt.le, image_insert_eq, insert_eq_of_mem]
  exact ⟨a, left_mem_Ico.mpr h.lt, h.closed⟩

/-- A Jordan curve on `[a, b]` is the image of an injective continuous map from the unit
sphere of the plane, as required by `jordan_curve`. -/
theorem exists_sphere_param :
    ∃ r : Metric.sphere (0 : Plane) 1 → Plane, Continuous r ∧ Injective r ∧
      range r = Arcs.complexLIE '' (c '' Icc a b) := by
  have hab : 0 < b - a := sub_pos.mpr h.lt
  have : Fact (0 < b - a) := ⟨hab⟩
  have hb : a + (b - a) = b := add_sub_cancel a b
  set L : AddCircle (b - a) → ℂ := AddCircle.liftIco (b - a) a c with hL
  have hLc : Continuous L :=
    AddCircle.liftIco_continuous (by rw [hb]; exact h.closed) (by rw [hb]; exact h.continuousOn)
  have hLapply : ∀ x, L x = c (AddCircle.equivIco (b - a) a x) := fun x => rfl
  have hmem : ∀ x, ((AddCircle.equivIco (b - a) a x : ℝ)) ∈ Ico a b := fun x => by
    have := (AddCircle.equivIco (b - a) a x).2
    exact ⟨this.1, lt_of_lt_of_eq this.2 hb⟩
  have hLinj : Injective L := by
    intro x y hxy
    rw [hLapply, hLapply] at hxy
    exact (AddCircle.equivIco (b - a) a).injective
      (Subtype.ext (h.injOn (hmem x) (hmem y) hxy))
  have hLrange : range L = c '' Icc a b := by
    rw [← h.image_Ico_eq]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, hmem x, (hLapply x).symm⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(t : AddCircle (b - a)), ?_⟩
      rw [hL, AddCircle.liftIco_coe_apply]
      rwa [hb]
  let e₁ := Arcs.circleHomeoSphere.symm
  let e₂ := (AddCircle.homeomorphCircle hab.ne').symm
  refine ⟨fun w => Arcs.complexLIE (L (e₂ (e₁ w))), ?_, ?_, ?_⟩
  · exact Arcs.complexLIE.continuous.comp (hLc.comp (e₂.continuous.comp e₁.continuous))
  · exact Arcs.complexLIE.injective.comp (hLinj.comp (e₂.injective.comp e₁.injective))
  · rw [← hLrange]
    show range (Arcs.complexLIE ∘ (L ∘ (e₂ ∘ e₁))) = _
    rw [range_comp, (e₂.surjective.comp e₁.surjective).range_comp]

theorem exists_mem_jordanInterior : ∃ p, p ∈ jordanInterior c a b := by
  obtain ⟨r, hrc, hri, hrr⟩ := h.exists_sphere_param
  obtain ⟨x, hx, hxb⟩ := step_A_exists_bounded Brouwer.brouwerFPT hrc hri
  have hp : Arcs.complexLIE.symm x ∉ c '' Icc a b := by
    intro hmem
    apply hx
    rw [hrr]
    exact ⟨_, hmem, Arcs.complexLIE.apply_symm_apply x⟩
  refine ⟨Arcs.complexLIE.symm x, hp, ?_⟩
  rw [← isBounded_image_complexLIE_iff, image_connectedComponentIn_compl hp,
    Arcs.complexLIE.apply_symm_apply, ← hrr]
  exact hxb

theorem exists_mem_jordanExterior : ∃ p, p ∈ jordanExterior c a b := by
  obtain ⟨r, hrc, -, hrr⟩ := h.exists_sphere_param
  obtain ⟨x, hx, hxb⟩ := exists_unbounded_component r hrc
  have hp : Arcs.complexLIE.symm x ∉ c '' Icc a b := by
    intro hmem
    apply hx
    rw [hrr]
    exact ⟨_, hmem, Arcs.complexLIE.apply_symm_apply x⟩
  refine ⟨Arcs.complexLIE.symm x, hp, ?_⟩
  rw [← isBounded_image_complexLIE_iff, image_connectedComponentIn_compl hp,
    Arcs.complexLIE.apply_symm_apply, ← hrr]
  exact hxb

/-- **Jordan curve theorem**: all bounded components of the complement coincide. -/
theorem connectedComponentIn_eq_of_mem_jordanInterior {p q : ℂ} (hp : p ∈ jordanInterior c a b)
    (hq : q ∈ jordanInterior c a b) :
    connectedComponentIn (c '' Icc a b)ᶜ p = connectedComponentIn (c '' Icc a b)ᶜ q := by
  obtain ⟨r, hrc, hri, hrr⟩ := h.exists_sphere_param
  have hmem : ∀ {z : ℂ}, z ∉ c '' Icc a b → Arcs.complexLIE z ∈ (range r)ᶜ := fun hz hm => by
    rw [hrr, mem_image_complexLIE_iff] at hm
    exact hz hm
  have hbdd : ∀ {z : ℂ}, z ∈ jordanInterior c a b →
      IsBounded (connectedComponentIn (range r)ᶜ (Arcs.complexLIE z)) := fun hz => by
    rw [hrr, ← image_connectedComponentIn_compl hz.1, isBounded_image_complexLIE_iff]
    exact hz.2
  have := step_B_bounded_unique Brouwer.brouwerFPT hrc hri _ (hmem hp.1) _ (hmem hq.1)
    (hbdd hp) (hbdd hq)
  rw [hrr, ← image_connectedComponentIn_compl hp.1, ← image_connectedComponentIn_compl hq.1]
    at this
  exact (image_injective.mpr Arcs.complexLIE.injective) this

/-- All unbounded components of the complement coincide. -/
theorem connectedComponentIn_eq_of_mem_jordanExterior {p q : ℂ} (hp : p ∈ jordanExterior c a b)
    (hq : q ∈ jordanExterior c a b) :
    connectedComponentIn (c '' Icc a b)ᶜ p = connectedComponentIn (c '' Icc a b)ᶜ q := by
  obtain ⟨r, hrc, -, hrr⟩ := h.exists_sphere_param
  have hbdd : ∀ {z : ℂ}, z ∈ jordanExterior c a b →
      ¬ IsBounded (connectedComponentIn (range r)ᶜ (Arcs.complexLIE z)) := fun hz => by
    rw [hrr, ← image_connectedComponentIn_compl hz.1, isBounded_image_complexLIE_iff]
    exact hz.2
  have := unbounded_component_unique r hrc (hbdd hp) (hbdd hq)
  rw [hrr, ← image_connectedComponentIn_compl hp.1, ← image_connectedComponentIn_compl hq.1]
    at this
  exact (image_injective.mpr Arcs.complexLIE.injective) this

/-- The interior of a Jordan curve is the (unique) bounded component of the complement. -/
theorem jordanInterior_eq {p : ℂ} (hp : p ∈ jordanInterior c a b) :
    jordanInterior c a b = connectedComponentIn (c '' Icc a b)ᶜ p :=
  subset_antisymm (fun q hq => by
      rw [h.connectedComponentIn_eq_of_mem_jordanInterior hp hq]
      exact mem_connectedComponentIn hq.1)
    (connectedComponentIn_subset_jordanInterior hp)

/-- The exterior of a Jordan curve is the (unique) unbounded component of the complement. -/
theorem jordanExterior_eq {p : ℂ} (hp : p ∈ jordanExterior c a b) :
    jordanExterior c a b = connectedComponentIn (c '' Icc a b)ᶜ p :=
  subset_antisymm (fun q hq => by
      rw [h.connectedComponentIn_eq_of_mem_jordanExterior hp hq]
      exact mem_connectedComponentIn hq.1)
    (connectedComponentIn_subset_jordanExterior hp)

theorem isConnected_jordanInterior : IsConnected (jordanInterior c a b) := by
  obtain ⟨p, hp⟩ := h.exists_mem_jordanInterior
  rw [h.jordanInterior_eq hp]
  exact isConnected_connectedComponentIn_iff.mpr hp.1

theorem isConnected_jordanExterior : IsConnected (jordanExterior c a b) := by
  obtain ⟨p, hp⟩ := h.exists_mem_jordanExterior
  rw [h.jordanExterior_eq hp]
  exact isConnected_connectedComponentIn_iff.mpr hp.1

end IsJordanCurve

namespace ClosedPiecewiseC1

variable (P : ClosedPiecewiseC1 c a b)

include P in
theorem isJordanCurve (hab : a < b) (hinj : InjOn c (Ico a b)) : IsJordanCurve c a b :=
  ⟨hab, P.continuousOn, hinj, P.closed⟩

/-- The winding number of a Jordan curve is constant on its interior. -/
theorem windingNumber_eq_of_mem_jordanInterior (h : IsJordanCurve c a b) {p q : ℂ}
    (hp : p ∈ jordanInterior c a b) (hq : q ∈ jordanInterior c a b) :
    P.windingNumber p = P.windingNumber q :=
  P.windingNumber_eq_of_isPreconnected h.isConnected_jordanInterior.isPreconnected
    jordanInterior_subset hp hq

/-- The winding number vanishes on the exterior. -/
theorem windingNumber_eq_zero_of_mem_jordanExterior {p : ℂ} (hp : p ∈ jordanExterior c a b) :
    P.windingNumber p = 0 :=
  P.windingNumber_eq_zero_of_not_isBounded hp.1 hp.2

/-- A closed curve is *positively oriented* when its winding number is `1` on its interior
(anticlockwise traversal). -/
def IsPositivelyOriented : Prop := ∀ p ∈ jordanInterior c a b, P.windingNumber p = 1

/-- For a Jordan curve, positive orientation can be checked at a single interior point. -/
theorem isPositivelyOriented_of_eq_one (h : IsJordanCurve c a b) {p : ℂ}
    (hp : p ∈ jordanInterior c a b) (h1 : P.windingNumber p = 1) : P.IsPositivelyOriented :=
  fun _ hq => (P.windingNumber_eq_of_mem_jordanInterior h hq hp).trans h1

end ClosedPiecewiseC1

end Azurite.JordanCurve
