/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The Jordan–Brouwer separation theorem

The topological half of the Jordan–Brouwer separation theorem, following E. L. Lima, "The
Jordan–Brouwer separation theorem for smooth hypersurfaces", Amer. Math. Monthly 95 (1988): a
connected set that locally separates into at most two sides has a complement with at most two
components.  The other half (at least two components) for closed surfaces in `ℝ³` is in
`Section6GaussSeparation.lean`, via the solid angle.

* **Abstract.**  `LocallyTwoSided K p`: some open `U ∋ p` has `U \ K` covered by two preconnected
  sets whose closures contain `K ∩ U`.  For `K` closed, connected and locally two-sided in a
  connected, locally connected space: `subset_closure_connectedComponentIn` (every component of
  `Kᶜ` has all of `K` in its closure, Lima's lemma), `connectedComponentIn_two` (among three
  points of `Kᶜ` two share a component), `frontier_connectedComponentIn` (the frontier of every
  component is `K`), `isPreconnected_of_compl_eq_union` (a splitting of `Kᶜ` into two disjoint
  nonempty open sets has both parts connected).
* **Graphs.**  `IsLocallyGraphAt F K p`: in a chart `E → F × ℝ` around `p`, `K` is the graph
  `t = h(x)` of a continuous `h` over a connected `Ω` inside a box; `IsLocallyGraph K` (some chart
  at every point).  `IsLocallyGraphAt.locallyTwoSided` (the regions above and below the graph,
  `between`, `isPreconnected_between`).
* **Normed spaces** of dimension `≥ 2`: `isPreconnected_compl_closedBall`;
  `jordanBrouwer_le_two` (`K` nonempty, compact, connected, locally a graph: `Kᶜ` has a unique
  unbounded component, the others are bounded, at most two components, each with frontier `K`).
* **Smooth hypersurfaces.**  `isLocallyGraphAt_of_hasStrictFDerivAt` (implicit function theorem:
  a regular zero set is locally a graph over the tangent hyperplane), `isLocallyGraph_of_regular`.
-/

open Set Filter Topology

universe u

namespace Azurite.DLMF

/-! ### At most two components (Lima's argument) -/

section Abstract

variable {X : Type*} [TopologicalSpace X]

/-- `K` has at most two local sides at `p`: some open `U ∋ p` has `U \ K` covered by two
preconnected sets `A`, `B` (off `K`) whose closures both contain `K ∩ U`. -/
def LocallyTwoSided (K : Set X) (p : X) : Prop :=
  ∃ U A B : Set X, IsOpen U ∧ p ∈ U ∧ A ⊆ U \ K ∧ B ⊆ U \ K ∧ IsPreconnected A ∧
    IsPreconnected B ∧ U \ K ⊆ A ∪ B ∧ K ∩ U ⊆ closure A ∩ closure B

theorem subset_connectedComponentIn_of_inter {K A : Set X} {x : X} (hA : IsPreconnected A)
    (hAK : A ⊆ Kᶜ) (h : (A ∩ connectedComponentIn Kᶜ x).Nonempty) :
    A ⊆ connectedComponentIn Kᶜ x := by
  obtain ⟨c, hcA, hcC⟩ := h
  rw [connectedComponentIn_eq hcC]
  exact hA.subset_connectedComponentIn hcA hAK

theorem connectedComponentIn_eq_of_inter {K A : Set X} {x y : X} (hA : IsPreconnected A)
    (hAK : A ⊆ Kᶜ) (hx : (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    (hy : (A ∩ connectedComponentIn Kᶜ y).Nonempty) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y := by
  obtain ⟨a, haA, hay⟩ := hy
  rw [connectedComponentIn_eq (subset_connectedComponentIn_of_inter hA hAK hx haA),
    connectedComponentIn_eq hay]

variable [ConnectedSpace X] [LocallyConnectedSpace X] {K : Set X}

/-- The closure of every component of `Kᶜ` meets `K`. -/
theorem closure_connectedComponentIn_inter_nonempty (hK : IsClosed K) (hKne : K.Nonempty)
    {x : X} (hx : x ∉ K) : (K ∩ closure (connectedComponentIn Kᶜ x)).Nonempty := by
  set C := connectedComponentIn Kᶜ x
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hcl : closure C ⊆ Kᶜ := fun z hz hzK => (eq_empty_iff_forall_notMem.mp h) z ⟨hzK, hz⟩
  have hsub : closure C ⊆ C :=
    isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx)) hcl
  have hclopen : IsClopen C :=
    ⟨closure_subset_iff_isClosed.mp hsub, hK.isOpen_compl.connectedComponentIn⟩
  rcases isClopen_iff.mp hclopen with h0 | h1
  · exact (h0 ▸ mem_connectedComponentIn (F := Kᶜ) hx : x ∈ (∅ : Set X))
  · obtain ⟨k, hk⟩ := hKne
    exact connectedComponentIn_subset Kᶜ x (h1 ▸ mem_univ k : k ∈ C) hk

/-- **Lima's lemma**: if `K` is closed, connected and locally two-sided, the closure of every
component of `Kᶜ` contains all of `K`. -/
theorem subset_closure_connectedComponentIn (hK : IsClosed K) (hKc : IsPreconnected K)
    (hKne : K.Nonempty) (hloc : ∀ p ∈ K, LocallyTwoSided K p) {x : X} (hx : x ∉ K) :
    K ⊆ closure (connectedComponentIn Kᶜ x) := by
  set C := connectedComponentIn Kᶜ x with hC
  have hCK : C ⊆ Kᶜ := connectedComponentIn_subset _ _
  choose U A B hU hpU hA hB hAc hBc hcov hcl using hloc
  have key : ∀ p (hp : p ∈ K), p ∈ closure C → K ∩ U p hp ⊆ closure C := by
    intro p hp hpC
    obtain ⟨c, hcU, hcC⟩ := mem_closure_iff.mp hpC (U p hp) (hU p hp) (hpU p hp)
    have hcAB := hcov p hp ⟨hcU, hCK hcC⟩
    rcases hcAB with hcA | hcB
    · have := subset_connectedComponentIn_of_inter (hAc p hp)
        (fun a ha => (hA p hp ha).2) ⟨c, hcA, hcC⟩
      exact fun q hq => closure_mono this (hcl p hp hq).1
    · have := subset_connectedComponentIn_of_inter (hBc p hp)
        (fun a ha => (hB p hp ha).2) ⟨c, hcB, hcC⟩
      exact fun q hq => closure_mono this (hcl p hp hq).2
  set u := ⋃ (p) (hp : p ∈ K) (_ : p ∈ closure C), U p hp
  have hu : IsOpen u := isOpen_iUnion fun p => isOpen_iUnion fun hp => isOpen_iUnion fun _ =>
    hU p hp
  have hcover : K ⊆ u ∪ (closure C)ᶜ := by
    intro q hq
    by_cases hqC : q ∈ closure C
    · exact Or.inl (mem_iUnion₂.mpr ⟨q, hq, mem_iUnion.mpr ⟨hqC, hpU q hq⟩⟩)
    · exact Or.inr hqC
  have hdisj : K ∩ (u ∩ (closure C)ᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun q ⟨hq, hqu, hqv⟩ => hqv ?_
    obtain ⟨p, hp, hq'⟩ := mem_iUnion₂.mp hqu
    obtain ⟨hpC, hqU⟩ := mem_iUnion.mp hq'
    exact key p hp hpC ⟨hq, hqU⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp hKc u (closure C)ᶜ hu
    isClosed_closure.isOpen_compl hcover hdisj with h | h
  · intro q hq
    obtain ⟨p, hp, hq'⟩ := mem_iUnion₂.mp (h hq)
    obtain ⟨hpC, hqU⟩ := mem_iUnion.mp hq'
    exact key p hp hpC ⟨hq, hqU⟩
  · obtain ⟨q, hqK, hqC⟩ := closure_connectedComponentIn_inter_nonempty hK hKne hx
    exact absurd hqC (h hqK)

/-- **At most two components**: among any three points off `K`, two lie in the same component of
`Kᶜ`. -/
theorem connectedComponentIn_two (hK : IsClosed K) (hKc : IsPreconnected K) (hKne : K.Nonempty)
    (hloc : ∀ p ∈ K, LocallyTwoSided K p) {x y z : X} (hx : x ∉ K) (hy : y ∉ K) (hz : z ∉ K) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y ∨
      connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ z ∨
      connectedComponentIn Kᶜ y = connectedComponentIn Kᶜ z := by
  obtain ⟨p, hp⟩ := hKne
  obtain ⟨U, A, B, hU, hpU, hA, hB, hAc, hBc, hcov, -⟩ := hloc p hp
  have side : ∀ w, w ∉ K → (A ∩ connectedComponentIn Kᶜ w).Nonempty ∨
      (B ∩ connectedComponentIn Kᶜ w).Nonempty := by
    intro w hw
    obtain ⟨c, hcU, hcC⟩ := mem_closure_iff.mp
      (subset_closure_connectedComponentIn hK hKc ⟨p, hp⟩ hloc hw hp) U hU hpU
    rcases hcov ⟨hcU, connectedComponentIn_subset _ _ hcC⟩ with h | h
    · exact Or.inl ⟨c, h, hcC⟩
    · exact Or.inr ⟨c, h, hcC⟩
  have hA' : A ⊆ Kᶜ := fun a ha => (hA ha).2
  have hB' : B ⊆ Kᶜ := fun a ha => (hB ha).2
  rcases side x hx with h1 | h1 <;> rcases side y hy with h2 | h2 <;>
    rcases side z hz with h3 | h3
  · exact Or.inl (connectedComponentIn_eq_of_inter hAc hA' h1 h2)
  · exact Or.inl (connectedComponentIn_eq_of_inter hAc hA' h1 h2)
  · exact Or.inr (Or.inl (connectedComponentIn_eq_of_inter hAc hA' h1 h3))
  · exact Or.inr (Or.inr (connectedComponentIn_eq_of_inter hBc hB' h2 h3))
  · exact Or.inr (Or.inr (connectedComponentIn_eq_of_inter hAc hA' h2 h3))
  · exact Or.inr (Or.inl (connectedComponentIn_eq_of_inter hBc hB' h1 h3))
  · exact Or.inl (connectedComponentIn_eq_of_inter hBc hB' h1 h2)
  · exact Or.inl (connectedComponentIn_eq_of_inter hBc hB' h1 h2)

/-- The frontier of every component of `Kᶜ` is `K`. -/
theorem frontier_connectedComponentIn (hK : IsClosed K) (hKc : IsPreconnected K)
    (hKne : K.Nonempty) (hloc : ∀ p ∈ K, LocallyTwoSided K p) {x : X} (hx : x ∉ K) :
    frontier (connectedComponentIn Kᶜ x) = K := by
  set C := connectedComponentIn Kᶜ x
  have hCo : IsOpen C := hK.isOpen_compl.connectedComponentIn
  rw [hCo.frontier_eq]
  refine Subset.antisymm (fun z ⟨hzc, hzC⟩ => ?_) fun z hz =>
    ⟨subset_closure_connectedComponentIn hK hKc hKne hloc hx hz,
      fun h => connectedComponentIn_subset _ _ h hz⟩
  by_contra hzK
  have hzo : IsOpen (connectedComponentIn Kᶜ z) := hK.isOpen_compl.connectedComponentIn
  obtain ⟨c, hcz, hcC⟩ := mem_closure_iff.mp hzc _ hzo (mem_connectedComponentIn hzK)
  apply hzC
  have h1 : C = connectedComponentIn Kᶜ c := connectedComponentIn_eq hcC
  have h2 : connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ c := connectedComponentIn_eq hcz
  rw [h1, ← h2]
  exact mem_connectedComponentIn hzK

/-- If `Kᶜ` is split into two disjoint nonempty open sets, both are connected (each is a single
component of `Kᶜ`). -/
theorem isPreconnected_of_compl_eq_union (hK : IsClosed K) (hKc : IsPreconnected K)
    (hKne : K.Nonempty) (hloc : ∀ p ∈ K, LocallyTwoSided K p) {P Q : Set X} (hP : IsOpen P)
    (hQ : IsOpen Q) (hPQ : Disjoint P Q) (hcompl : Kᶜ = P ∪ Q) (hPne : P.Nonempty)
    (hQne : Q.Nonempty) : IsPreconnected P := by
  obtain ⟨x₀, hx₀⟩ := hPne
  obtain ⟨z₀, hz₀⟩ := hQne
  have hPK : P ⊆ Kᶜ := hcompl ▸ subset_union_left
  have hQK : Q ⊆ Kᶜ := hcompl ▸ subset_union_right
  have inP : ∀ x ∈ P, connectedComponentIn Kᶜ x ⊆ P := fun x hx =>
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hP hQ hPQ
      (hcompl ▸ connectedComponentIn_subset _ _) ⟨x, mem_connectedComponentIn (hPK hx), hx⟩
  have inQ : ∀ z ∈ Q, connectedComponentIn Kᶜ z ⊆ Q := fun z hz =>
    isPreconnected_connectedComponentIn.subset_right_of_subset_union hP hQ hPQ
      (hcompl ▸ connectedComponentIn_subset _ _) ⟨z, mem_connectedComponentIn (hQK hz), hz⟩
  have hne : ∀ x ∈ P, connectedComponentIn Kᶜ x ≠ connectedComponentIn Kᶜ z₀ := fun x hx h =>
    Set.disjoint_left.mp hPQ (inP x hx (mem_connectedComponentIn (hPK hx)))
      (inQ z₀ hz₀ (h ▸ mem_connectedComponentIn (hPK hx)))
  have heq : P = connectedComponentIn Kᶜ x₀ := by
    refine Subset.antisymm (fun y hy => ?_) (inP x₀ hx₀)
    rcases connectedComponentIn_two hK hKc hKne hloc (hPK hx₀) (hPK hy) (hQK hz₀) with h | h | h
    · rw [h]; exact mem_connectedComponentIn (hPK hy)
    · exact absurd h (hne x₀ hx₀)
    · exact absurd h (hne y hy)
  rw [heq]
  exact isPreconnected_connectedComponentIn

end Abstract

/-! ### Graphs are two-sided -/

section Graph

variable {F : Type*} [TopologicalSpace F]

/-- The region `{(x, t) : x ∈ Ω, lo(x) < t < hi(x)}` between two graphs. -/
def between (Ω : Set F) (lo hi : F → ℝ) : Set (F × ℝ) :=
  {q | q.1 ∈ Ω ∧ lo q.1 < q.2 ∧ q.2 < hi q.1}

theorem isPreconnected_between {Ω : Set F} {lo hi : F → ℝ} (hΩ : IsPreconnected Ω)
    (hlo : ContinuousOn lo Ω) (hhi : ContinuousOn hi Ω) (hlt : ∀ x ∈ Ω, lo x < hi x) :
    IsPreconnected (between Ω lo hi) := by
  have heq : between Ω lo hi =
      (fun q : F × ℝ => (q.1, lo q.1 + q.2 * (hi q.1 - lo q.1))) '' (Ω ×ˢ Ioo 0 1) := by
    ext ⟨x, t⟩
    constructor
    · rintro ⟨hx, h1, h2⟩
      have hd : 0 < hi x - lo x := sub_pos.mpr (hlt x hx)
      refine ⟨(x, (t - lo x) / (hi x - lo x)), ⟨hx, ?_, ?_⟩, ?_⟩
      · exact div_pos (by linarith) hd
      · rw [div_lt_one hd]; linarith
      · simp only [Prod.mk.injEq, true_and]; field_simp; ring
    · rintro ⟨⟨y, s⟩, ⟨hy, hs0, hs1⟩, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hd : 0 < hi y - lo y := sub_pos.mpr (hlt y hy)
      refine ⟨hy, ?_, ?_⟩ <;> simp only <;> nlinarith
  rw [heq]
  refine (hΩ.prod isPreconnected_Ioo).image _ ?_
  intro q hq
  have h1 : ContinuousWithinAt (fun q : F × ℝ => lo q.1) (Ω ×ˢ Ioo 0 1) q :=
    (hlo q.1 hq.1).comp continuousWithinAt_fst fun r hr => hr.1
  have h2 : ContinuousWithinAt (fun q : F × ℝ => hi q.1) (Ω ×ˢ Ioo 0 1) q :=
    (hhi q.1 hq.1).comp continuousWithinAt_fst fun r hr => hr.1
  exact continuousWithinAt_fst.prodMk (h1.add (continuousWithinAt_snd.mul (h2.sub h1)))

theorem mem_closure_between_lo {Ω : Set F} {lo hi : F → ℝ} {x : F} (hx : x ∈ Ω)
    (hlt : lo x < hi x) : (x, lo x) ∈ closure (between Ω lo hi) := by
  have ht : Tendsto (fun s : ℝ => (x, lo x + s * (hi x - lo x))) (𝓝[>] 0) (𝓝 (x, lo x)) := by
    have : Continuous fun s : ℝ => (x, lo x + s * (hi x - lo x)) := by fun_prop
    simpa using (this.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
  have hd : 0 < hi x - lo x := sub_pos.mpr hlt
  exact ⟨hx, by simp only; nlinarith [hs.1], by simp only; nlinarith [hs.2]⟩

theorem mem_closure_between_hi {Ω : Set F} {lo hi : F → ℝ} {x : F} (hx : x ∈ Ω)
    (hlt : lo x < hi x) : (x, hi x) ∈ closure (between Ω lo hi) := by
  have ht : Tendsto (fun s : ℝ => (x, hi x - s * (hi x - lo x))) (𝓝[>] 0) (𝓝 (x, hi x)) := by
    have : Continuous fun s : ℝ => (x, hi x - s * (hi x - lo x)) := by fun_prop
    simpa using (this.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
  have hd : 0 < hi x - lo x := sub_pos.mpr hlt
  exact ⟨hx, by simp only; nlinarith [hs.2], by simp only; nlinarith [hs.1]⟩

variable {E : Type*} [TopologicalSpace E]

/-- `K` is, near `p`, the graph of a continuous function in a chart: a partial homeomorphism
`φ : E → F × ℝ` around `p` maps `K` near `p` onto the graph `t = h(x)` over the box
`Ω × (a, b)`, with `Ω` connected and `a < h < b`. -/
def IsLocallyGraphAt (F : Type*) [TopologicalSpace F] (K : Set E) (p : E) : Prop :=
  ∃ (φ : OpenPartialHomeomorph E (F × ℝ)) (Ω : Set F) (h : F → ℝ) (a b : ℝ),
    p ∈ φ.source ∧ IsOpen Ω ∧ IsPreconnected Ω ∧ ContinuousOn h Ω ∧ MapsTo h Ω (Ioo a b) ∧
    φ p ∈ Ω ×ˢ Ioo a b ∧ Ω ×ˢ Ioo a b ⊆ φ.target ∧
    ∀ y ∈ φ.source, φ y ∈ Ω ×ˢ Ioo a b → (y ∈ K ↔ (φ y).2 = h (φ y).1)

/-- A set that is locally a graph is locally two-sided. -/
theorem IsLocallyGraphAt.locallyTwoSided {K : Set E} {p : E} (hK : IsLocallyGraphAt F K p) :
    LocallyTwoSided K p := by
  obtain ⟨φ, Ω, h, a, b, hp, hΩo, hΩc, hh, hmaps, hφp, hbox, hgraph⟩ := hK
  set A' := between Ω h (fun _ => b)
  set B' := between Ω (fun _ => a) h
  have hA'box : A' ⊆ Ω ×ˢ Ioo a b := fun q hq =>
    ⟨hq.1, (hmaps hq.1).1.trans hq.2.1, hq.2.2⟩
  have hB'box : B' ⊆ Ω ×ˢ Ioo a b := fun q hq =>
    ⟨hq.1, hq.2.1, hq.2.2.trans (hmaps hq.1).2⟩
  have hside : ∀ {S' : Set (F × ℝ)}, S' ⊆ Ω ×ˢ Ioo a b → (∀ q ∈ S', q.2 ≠ h q.1) →
      φ.symm '' S' ⊆ (φ.source ∩ φ ⁻¹' (Ω ×ˢ Ioo a b)) \ K := by
    rintro S' hS' hne _ ⟨q, hq, rfl⟩
    have hqt := hbox (hS' hq)
    have hsrc := φ.map_target hqt
    have hφ : φ (φ.symm q) = q := φ.right_inv hqt
    refine ⟨⟨hsrc, by rw [mem_preimage, hφ]; exact hS' hq⟩, fun hK => hne q hq ?_⟩
    have := (hgraph _ hsrc (by rw [hφ]; exact hS' hq)).mp hK
    rwa [hφ] at this
  have hconn : ∀ {S' : Set (F × ℝ)}, S' ⊆ Ω ×ˢ Ioo a b → IsPreconnected S' →
      IsPreconnected (φ.symm '' S') := fun hS' hc =>
    hc.image _ (φ.continuousOn_symm.mono (hS'.trans hbox))
  refine ⟨φ.source ∩ φ ⁻¹' (Ω ×ˢ Ioo a b), φ.symm '' A', φ.symm '' B',
    φ.isOpen_inter_preimage (hΩo.prod isOpen_Ioo), ⟨hp, hφp⟩,
    hside hA'box fun q hq => (ne_of_lt hq.2.1).symm,
    hside hB'box fun q hq => ne_of_lt hq.2.2,
    hconn hA'box (isPreconnected_between hΩc hh continuousOn_const fun x hx => (hmaps hx).2),
    hconn hB'box (isPreconnected_between hΩc continuousOn_const hh fun x hx => (hmaps hx).1),
    ?_, ?_⟩
  · rintro y ⟨⟨hy, hyb⟩, hyK⟩
    have hne : (φ y).2 ≠ h (φ y).1 := fun he => hyK ((hgraph y hy hyb).mpr he)
    have hy' : y = φ.symm (φ y) := (φ.left_inv hy).symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inr ⟨φ y, ⟨hyb.1, hyb.2.1, hlt⟩, hy'.symm⟩
    · exact Or.inl ⟨φ y, ⟨hyb.1, hgt, hyb.2.2⟩, hy'.symm⟩
  · rintro y ⟨hyK, hy, hyb⟩
    have he : (φ y).2 = h (φ y).1 := (hgraph y hy hyb).mp hyK
    have hq : φ y = ((φ y).1, h (φ y).1) := Prod.ext rfl he
    have hcont : ContinuousAt φ.symm (φ y) := φ.continuousAt_symm (φ.map_source hy)
    have hy' : φ.symm (φ y) = y := φ.left_inv hy
    constructor
    · have hm : φ y ∈ closure A' := by
        rw [hq]; exact mem_closure_between_lo hyb.1 (hmaps hyb.1).2
      have := mem_closure_image hcont hm
      rwa [hy'] at this
    · have hm : φ y ∈ closure B' := by
        rw [hq]; exact mem_closure_between_hi hyb.1 (hmaps hyb.1).1
      have := mem_closure_image hcont hm
      rwa [hy'] at this

/-- `K` is locally a graph at each of its points (the chart space `F` may depend on the point). -/
def IsLocallyGraph {E : Type u} [TopologicalSpace E] (K : Set E) : Prop :=
  ∀ p ∈ K, ∃ (F : Type u) (_ : TopologicalSpace F), IsLocallyGraphAt F K p

theorem IsLocallyGraph.locallyTwoSided {E : Type u} [TopologicalSpace E] {K : Set E}
    (h : IsLocallyGraph K) : ∀ p ∈ K, LocallyTwoSided K p := fun p hp => by
  obtain ⟨F, _, hF⟩ := h p hp
  exact hF.locallyTwoSided

end Graph

/-! ### Normed spaces: at most two components, exactly one unbounded -/

section Normed

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real normed space of dimension at least `2`, the complement of a closed ball is
connected (the image of `{0}ᶜ` under `v ↦ (1 + R/‖v‖) v`). -/
theorem isPreconnected_compl_closedBall (h : 1 < Module.rank ℝ E) (R : ℝ) (hR : 0 ≤ R) :
    IsPreconnected (Metric.closedBall (0 : E) R)ᶜ := by
  have heq : (Metric.closedBall (0 : E) R)ᶜ = (fun v : E => (1 + R / ‖v‖) • v) '' {0}ᶜ := by
    ext w
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le, mem_image,
      mem_singleton_iff]
    constructor
    · intro hw
      have hw0 : 0 < ‖w‖ := hR.trans_lt hw
      refine ⟨(1 - R / ‖w‖) • w, ?_, ?_⟩
      · intro h0
        rcases smul_eq_zero.mp h0 with h | h
        · have : R / ‖w‖ < 1 := (div_lt_one hw0).mpr hw
          linarith
        · exact (norm_pos_iff.mp hw0) h
      · have hc : 0 < 1 - R / ‖w‖ := by rw [sub_pos, div_lt_one hw0]; exact hw
        rw [norm_smul, Real.norm_of_nonneg hc.le, smul_smul]
        convert one_smul ℝ w using 2
        field_simp
        ring
    · rintro ⟨v, hv, rfl⟩
      have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
      rw [norm_smul, Real.norm_of_nonneg (by positivity), add_mul, one_mul,
        div_mul_cancel₀ _ hv0.ne']
      linarith
  rw [heq]
  refine (isConnected_compl_singleton_of_one_lt_rank h 0).isPreconnected.image _ ?_
  intro v hv
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  exact ((continuousAt_const.add (continuousAt_const.div continuous_norm.continuousAt hv0)).smul
    continuousAt_id).continuousWithinAt

variable [Nontrivial E] {K : Set E}

/-- **Jordan–Brouwer separation, the topological half.**  Let `K` be a nonempty compact connected
subset of a real normed space of dimension at least `2`, locally (at each of its points) a graph
in some chart.  Then `Kᶜ` has a unique unbounded component `C_∞`, and every other component is
bounded and equal to any other non-`C_∞` component: `Kᶜ` has at most two components.  The frontier
of every component is `K`. -/
theorem jordanBrouwer_le_two (h : 1 < Module.rank ℝ E) (hK : IsCompact K)
    (hKc : IsPreconnected K) (hKne : K.Nonempty) (hloc : IsLocallyGraph K) :
    ∃ xInf, xInf ∉ K ∧ ¬ Bornology.IsBounded (connectedComponentIn Kᶜ xInf) ∧
      (∀ x ∉ K, connectedComponentIn Kᶜ x ≠ connectedComponentIn Kᶜ xInf →
        Bornology.IsBounded (connectedComponentIn Kᶜ x)) ∧
      (∀ x ∉ K, ∀ y ∉ K, connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ xInf ∨
        connectedComponentIn Kᶜ y = connectedComponentIn Kᶜ xInf ∨
        connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y) ∧
      ∀ x ∉ K, frontier (connectedComponentIn Kᶜ x) = K := by
  have hloc' : ∀ p ∈ K, LocallyTwoSided K p := hloc.locallyTwoSided
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set R' := max R 0
  have hKR : K ⊆ Metric.closedBall 0 R' := hR.trans (Metric.closedBall_subset_closedBall
    (le_max_left _ _))
  have hO : (Metric.closedBall (0 : E) R')ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hKR
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  set xInf : E := ((R' + 1) / ‖u‖) • u
  have hxInf : xInf ∈ (Metric.closedBall (0 : E) R')ᶜ := by
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    simp only [xInf, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (R' + 1) / ‖u‖), div_mul_cancel₀ _ hu0.ne']
    linarith
  have hOC : (Metric.closedBall (0 : E) R')ᶜ ⊆ connectedComponentIn Kᶜ xInf :=
    (isPreconnected_compl_closedBall h R' (le_max_right _ _)).subset_connectedComponentIn hxInf hO
  have hunb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ xInf) := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    set M' := max M R' + 1
    have hmem : (M' / ‖u‖) • u ∈ (Metric.closedBall (0 : E) R')ᶜ := by
      simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ M' / ‖u‖), div_mul_cancel₀ _ hu0.ne']
      have := le_max_right M R'; linarith
    have := hM (hOC hmem)
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ M' / ‖u‖), div_mul_cancel₀ _ hu0.ne'] at this
    have := le_max_left M R'; linarith
  have hbdd : ∀ x ∉ K, connectedComponentIn Kᶜ x ≠ connectedComponentIn Kᶜ xInf →
      Bornology.IsBounded (connectedComponentIn Kᶜ x) := by
    intro x hx hne
    refine (Metric.isBounded_closedBall (x := (0 : E)) (r := R')).subset fun y hy => ?_
    by_contra hyO
    apply hne
    rw [connectedComponentIn_eq hy, ← connectedComponentIn_eq (hOC hyO)]
  refine ⟨xInf, hO hxInf, hunb, hbdd, fun x hx y hy => ?_, fun x hx =>
    frontier_connectedComponentIn hK.isClosed hKc hKne hloc' hx⟩
  rcases connectedComponentIn_two hK.isClosed hKc hKne hloc' hx hy (hO hxInf) with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end Normed

/-! ### Regular level sets are locally graphs -/

section Level

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Regular level sets are locally graphs** (implicit function theorem): if near `p ∈ K` the set
`K` is the zero set of `g`, strictly differentiable at `p` with `g′(p) ≠ 0`, then `K` is near
`p` a graph over the tangent hyperplane `ker g′(p)`. -/
theorem isLocallyGraphAt_of_hasStrictFDerivAt {K : Set E} {g : E → ℝ} {g' : E →L[ℝ] ℝ} {p : E}
    (hg : HasStrictFDerivAt g g' p) (hg' : g' ≠ 0) {U : Set E} (hU : U ∈ 𝓝 p)
    (hKU : ∀ y ∈ U, y ∈ K ↔ g y = 0) (hp : p ∈ K) : IsLocallyGraphAt g'.ker K p := by
  have hsurj : g'.range = ⊤ := by
    obtain ⟨v, hv⟩ : ∃ v, g' v ≠ 0 := by
      by_contra h
      push Not at h
      exact hg' (ContinuousLinearMap.ext h)
    refine LinearMap.range_eq_top.mpr fun t => ⟨(t / g' v) • v, ?_⟩
    simp [hv]
  obtain ⟨U', hU'U, hU'o, hpU'⟩ := mem_nhds_iff.mp hU
  set φ := hg.implicitToOpenPartialHomeomorph g g' hsurj
  set ψ := OpenPartialHomeomorph.trans φ (Homeomorph.prodComm ℝ g'.ker).toOpenPartialHomeomorph
  have hψ : ∀ y, ψ y = ((φ y).2, g y) := fun y => rfl
  have hψsrc : ψ.source = φ.source := by
    simp [ψ]
  have hpsrc : p ∈ ψ.source := hψsrc ▸ hg.mem_implicitToOpenPartialHomeomorph_source hsurj
  have hgp : g p = 0 := (hKU p (hU'U hpU')).mp hp
  set T := ψ.target ∩ ψ.symm ⁻¹' U'
  have hTo : IsOpen T := ψ.isOpen_inter_preimage_symm hU'o
  have hpT : ψ p ∈ T := ⟨ψ.map_source hpsrc, by rw [mem_preimage, ψ.left_inv hpsrc]; exact hpU'⟩
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.mp hTo _ hpT
  set x₀ := (ψ p).1
  have hψp : ψ p = (x₀, 0) := Prod.ext rfl (by rw [hψ]; exact hgp)
  have hbox : Metric.ball x₀ ε ×ˢ Ioo (-ε) ε ⊆ T := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine hεT ?_
    rw [hψp, Metric.mem_ball, Prod.dist_eq]
    refine max_lt hx ?_
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ht
  refine ⟨ψ, Metric.ball x₀ ε, fun _ => 0, -ε, ε, hpsrc, Metric.isOpen_ball,
    (convex_ball x₀ ε).isPreconnected, continuousOn_const, fun _ _ => ⟨by linarith, hε⟩,
    ?_, hbox.trans inter_subset_left, fun y hy hyb => ?_⟩
  · rw [hψp]; exact ⟨Metric.mem_ball_self hε, by linarith, hε⟩
  · have hyU : y ∈ U' := by
      have := (hbox hyb).2
      rwa [mem_preimage, ψ.left_inv hy] at this
    rw [hKU y (hU'U hyU), hψ]

/-- A set that is, near each of its points, a regular zero set of a strictly differentiable
function is locally a graph. -/
theorem isLocallyGraph_of_regular {K : Set E}
    (h : ∀ p ∈ K, ∃ g : E → ℝ, ∃ g' : E →L[ℝ] ℝ, HasStrictFDerivAt g g' p ∧ g' ≠ 0 ∧
      ∃ U ∈ 𝓝 p, ∀ y ∈ U, y ∈ K ↔ g y = 0) : IsLocallyGraph K := by
  intro p hp
  obtain ⟨g, g', hg, hg', U, hU, hKU⟩ := h p hp
  exact ⟨g'.ker, inferInstance, isLocallyGraphAt_of_hasStrictFDerivAt hg hg' hU hKU hp⟩

end Level

end Azurite.DLMF
