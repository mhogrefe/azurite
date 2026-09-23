/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.Theorem_2_77

/-! # BPR Corollary 2.79

A subset of `R` defined by a formula in the language of ordered fields with
coefficients in `R` (a real closed field) is a **finite union of points and
intervals**.

By Corollary 2.78 the set is semialgebraic; the content here is the
one-dimensional cell decomposition. We model "finite union of points and
intervals" as `IsFinUnionOfOrdConnected` — a finite union of order-connected
(order-convex) subsets, which over a linear order are exactly the points and
intervals.

The decomposition is purely order-theoretic (an abstract real closed field has
no topology): `IsFinUnionOfOrdConnected` is closed under `∪`, `∩`, and `ᶜ` (the
complement of a convex set is two rays), and the positivity generator
`{x | P(x) > 0}` is handled by intersecting with the order-connected pieces of
`{x | P(x) = 0}ᶜ`, on each of which `P` has constant sign by the intermediate
value property.
-/

open _root_.Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Finite unions of order-connected sets -/

/-- A **finite union of points and intervals**: a finite family of order-connected
(order-convex) subsets of `R`. -/
def IsFinUnionOfOrdConnected (S : Set R) : Prop :=
  ∃ 𝒞 : Set (Set R), 𝒞.Finite ∧ (∀ C ∈ 𝒞, C.OrdConnected) ∧ S = ⋃₀ 𝒞

omit [Field R] [IsStrictOrderedRing R] in
theorem ordConnected_FUOC {C : Set R} (hC : C.OrdConnected) :
    IsFinUnionOfOrdConnected C :=
  ⟨{C}, Set.finite_singleton _, by rintro D rfl; exact hC, by simp⟩

omit [Field R] [IsStrictOrderedRing R] in
theorem IsFinUnionOfOrdConnected.union {S T : Set R}
    (hS : IsFinUnionOfOrdConnected S) (hT : IsFinUnionOfOrdConnected T) :
    IsFinUnionOfOrdConnected (S ∪ T) := by
  obtain ⟨𝒞, hf𝒞, ho𝒞, rfl⟩ := hS
  obtain ⟨𝒟, hf𝒟, ho𝒟, rfl⟩ := hT
  exact ⟨𝒞 ∪ 𝒟, hf𝒞.union hf𝒟,
    by rintro C (h | h); exacts [ho𝒞 C h, ho𝒟 C h], (Set.sUnion_union 𝒞 𝒟).symm⟩

omit [Field R] [IsStrictOrderedRing R] in
theorem IsFinUnionOfOrdConnected.inter {S T : Set R}
    (hS : IsFinUnionOfOrdConnected S) (hT : IsFinUnionOfOrdConnected T) :
    IsFinUnionOfOrdConnected (S ∩ T) := by
  obtain ⟨𝒞, hf𝒞, ho𝒞, rfl⟩ := hS
  obtain ⟨𝒟, hf𝒟, ho𝒟, rfl⟩ := hT
  refine ⟨(fun p : Set R × Set R => p.1 ∩ p.2) '' (𝒞 ×ˢ 𝒟),
    (hf𝒞.prod hf𝒟).image _, ?_, ?_⟩
  · rintro C ⟨⟨A, B⟩, ⟨hA, hB⟩, rfl⟩
    exact (ho𝒞 A hA).inter (ho𝒟 B hB)
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · rintro ⟨⟨A, hA, hxA⟩, ⟨B, hB, hxB⟩⟩
      exact ⟨A ∩ B, ⟨A, B, ⟨hA, hB⟩, rfl⟩, hxA, hxB⟩
    · rintro ⟨C, ⟨A, B, ⟨hA, hB⟩, rfl⟩, hxA, hxB⟩
      exact ⟨⟨A, hA, hxA⟩, ⟨B, hB, hxB⟩⟩

omit [Field R] in
/-- The complement of an order-connected set is the union of two order-connected rays. -/
theorem compl_ordConnected_FUOC {C : Set R} (hC : C.OrdConnected) :
    IsFinUnionOfOrdConnected Cᶜ := by
  have hocA : ({x | ∀ c ∈ C, x < c} : Set R).OrdConnected :=
    ⟨fun x _ y hy z hz c hc => lt_of_le_of_lt hz.2 (hy c hc)⟩
  have hocB : ({x | ∀ c ∈ C, c < x} : Set R).OrdConnected :=
    ⟨fun x hx y _ z hz c hc => lt_of_lt_of_le (hx c hc) hz.1⟩
  have hAB : Cᶜ = {x | ∀ c ∈ C, x < c} ∪ {x | ∀ c ∈ C, c < x} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hxC
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨c₁, hc₁, hxc₁⟩, ⟨c₂, hc₂, hxc₂⟩⟩ := hcon
      exact hxC (hC.out hc₁ hc₂ ⟨hxc₁, hxc₂⟩)
    · rintro (h | h) hxC
      · exact lt_irrefl x (h x hxC)
      · exact lt_irrefl x (h x hxC)
  rw [hAB]
  exact (ordConnected_FUOC hocA).union (ordConnected_FUOC hocB)

omit [Field R] [IsStrictOrderedRing R] in
theorem FUOC_sInter {ℱ : Set (Set R)} (hℱ : ℱ.Finite)
    (h : ∀ F ∈ ℱ, IsFinUnionOfOrdConnected F) : IsFinUnionOfOrdConnected (⋂₀ ℱ) := by
  revert h
  induction ℱ, hℱ using Set.Finite.induction_on with
  | empty => intro _; rw [Set.sInter_empty]; exact ordConnected_FUOC Set.ordConnected_univ
  | @insert F 𝒟 _ _ ih =>
    intro h
    rw [Set.sInter_insert]
    exact (h F (Set.mem_insert _ _)).inter (ih (fun G hG => h G (Set.mem_insert_of_mem _ hG)))

omit [Field R] in
theorem IsFinUnionOfOrdConnected.compl {S : Set R}
    (hS : IsFinUnionOfOrdConnected S) : IsFinUnionOfOrdConnected Sᶜ := by
  obtain ⟨𝒞, hf𝒞, ho𝒞, rfl⟩ := hS
  rw [Set.compl_sUnion]
  refine FUOC_sInter (hf𝒞.image _) ?_
  rintro F ⟨C, hC, rfl⟩
  exact compl_ordConnected_FUOC (ho𝒞 C hC)

omit [Field R] [IsStrictOrderedRing R] in
/-- A finite set is a finite union of points. -/
theorem FUOC_finite {S : Set R} (hS : S.Finite) : IsFinUnionOfOrdConnected S := by
  refine ⟨(fun a => {a}) '' S, hS.image _, ?_, ?_⟩
  · rintro C ⟨a, _, rfl⟩; exact Set.ordConnected_singleton
  · ext x; simp

/-! ### Constant sign on order-connected sets, and the generators -/

variable [IsRealClosed R]

/-- A nonvanishing polynomial has constant sign on an order-connected set: opposite
signs would force a root in between by the intermediate value property. -/
theorem const_sign_ordConnected {C : Set R} (hC : C.OrdConnected) (P : R[X])
    (hrf : ∀ x ∈ C, P.eval x ≠ 0) :
    (∀ x ∈ C, 0 < P.eval x) ∨ (∀ x ∈ C, P.eval x < 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hx, hPx⟩, ⟨y, hy, hPy⟩⟩ := hcon
  have hPx' : P.eval x < 0 := lt_of_le_of_ne hPx (hrf x hx)
  have hPy' : 0 < P.eval y := lt_of_le_of_ne hPy (Ne.symm (hrf y hy))
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · obtain ⟨r, hr1, hr2, hr3⟩ := hasIVP_of_isRealClosed P x y hxy (by nlinarith)
    exact hrf r (hC.out hx hy ⟨le_of_lt hr1, le_of_lt hr2⟩) hr3
  · subst hxy; linarith
  · obtain ⟨r, hr1, hr2, hr3⟩ := hasIVP_of_isRealClosed P y x hxy (by nlinarith)
    exact hrf r (hC.out hy hx ⟨le_of_lt hr1, le_of_lt hr2⟩) hr3

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- A zero locus is a finite union of points (or all of `R` if the polynomial is `0`). -/
theorem FUOC_zero_locus (P : R[X]) :
    IsFinUnionOfOrdConnected {x : R | P.eval x = 0} := by
  by_cases hP : P = 0
  · subst hP
    have : {x : R | (0 : R[X]).eval x = 0} = Set.univ := by ext x; simp
    rw [this]; exact ordConnected_FUOC Set.ordConnected_univ
  · exact FUOC_finite (P.finite_setOfPred_isRoot hP)

/-- A positivity locus is a finite union of intervals: it is the union, over the
order-connected pieces of `{P = 0}ᶜ`, of those pieces on which `P` is positive
(constant sign by `const_sign_ordConnected`). -/
theorem FUOC_pos_locus (P : R[X]) :
    IsFinUnionOfOrdConnected {x : R | 0 < P.eval x} := by
  by_cases hP : P = 0
  · subst hP
    refine ⟨∅, Set.finite_empty, by simp, ?_⟩
    ext x; simp
  · obtain ⟨𝒢, hf𝒢, ho𝒢, h𝒢⟩ := (FUOC_zero_locus P).compl
    refine ⟨(fun G => G ∩ {x : R | 0 < P.eval x}) '' 𝒢, hf𝒢.image _, ?_, ?_⟩
    · rintro D ⟨G, hG, rfl⟩
      show (G ∩ {x : R | 0 < P.eval x}).OrdConnected
      have hGsub : G ⊆ {x : R | P.eval x = 0}ᶜ := h𝒢 ▸ Set.subset_sUnion_of_mem hG
      have hrf : ∀ x ∈ G, P.eval x ≠ 0 := fun x hx => hGsub hx
      rcases const_sign_ordConnected (ho𝒢 G hG) P hrf with hpos | hneg
      · have heq : G ∩ {x : R | 0 < P.eval x} = G := by
          ext z; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
          exact ⟨fun h => h.1, fun h => ⟨h, hpos z h⟩⟩
        rw [heq]; exact ho𝒢 G hG
      · have heq : G ∩ {x : R | 0 < P.eval x} = ∅ := by
          ext z
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hz, hpz⟩; exact absurd (hneg z hz) (by linarith)
        rw [heq]; exact Set.ordConnected_empty
    · ext x
      simp only [Set.mem_ofPred_eq, Set.mem_sUnion, Set.mem_image]
      constructor
      · intro hpx
        have hxc : x ∈ {y : R | P.eval y = 0}ᶜ := by
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]; linarith
        rw [h𝒢, Set.mem_sUnion] at hxc
        obtain ⟨G, hG, hxG⟩ := hxc
        exact ⟨G ∩ {x : R | 0 < P.eval x}, ⟨G, hG, rfl⟩, hxG, hpx⟩
      · rintro ⟨D, ⟨G, _, rfl⟩, _, hpx⟩; exact hpx

/-! ### From semialgebraic to a finite union of points and intervals -/

/-- The map embedding `R` as the single coordinate, `t ↦ (fun _ ↦ t)`. -/
def constPt (t : R) : Fin 1 → R := fun _ => t

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Specialising a one-variable `MvPolynomial` at the constant tuple `constPt t` is
`R[X]`-evaluation at `t`. -/
theorem eval_constPt_eq_eval_toPoly (t : R) (P : MvPolynomial (Fin 1) R) :
    MvPolynomial.eval (constPt t) P
      = Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) P) := by
  show MvPolynomial.aeval (constPt t) P = _
  have h : (MvPolynomial.aeval (constPt t) : MvPolynomial (Fin 1) R →ₐ[R] R)
      = (Polynomial.aeval t).comp (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X)) := by
    apply MvPolynomial.algHom_ext
    intro i; fin_cases i; simp [constPt]
  rw [show MvPolynomial.aeval (constPt t) P = _ from congrFun (congrArg _ h) P]; simp

/-- The "section" `constPt ⁻¹' S = {t | (fun _ ↦ t) ∈ S}` of a semialgebraic
`S ⊆ R¹` is a finite union of points and intervals. -/
theorem semialgebraic_sect_FUOC {S : Set (Fin 1 → R)} (hS : IsSemialgebraicSet S) :
    IsFinUnionOfOrdConnected (constPt ⁻¹' S) := by
  induction hS with
  | algebraic h =>
    obtain ⟨pset, rfl⟩ := h
    have hset : (constPt ⁻¹' Zer pset)
        = ⋂₀ ((fun P => {t : R |
            Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) P) = 0})
            '' (↑pset : Set (MvPolynomial (Fin 1) R))) := by
      ext t
      simp only [Set.mem_preimage, Zer, Set.mem_ofPred_eq, Set.mem_sInter, Set.mem_image,
        Finset.mem_coe]
      constructor
      · rintro ht F ⟨P, hP, rfl⟩
        show Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) P) = 0
        rw [← eval_constPt_eq_eval_toPoly]; exact ht P hP
      · intro ht P hP; rw [eval_constPt_eq_eval_toPoly]; exact ht _ ⟨P, hP, rfl⟩
    rw [hset]
    exact FUOC_sInter (pset.finite_toSet.image _) (by rintro F ⟨P, _, rfl⟩; exact FUOC_zero_locus _)
  | pos_locus P =>
    have hset : (constPt ⁻¹' {x : Fin 1 → R | MvPolynomial.eval x P > 0})
        = {t : R | 0 < Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) P)} := by
      ext t; simp only [Set.mem_preimage, Set.mem_ofPred_eq, gt_iff_lt]
      rw [eval_constPt_eq_eval_toPoly]
    rw [hset]; exact FUOC_pos_locus _
  | compl _ ih => rw [Set.preimage_compl]; exact ih.compl
  | inter _ _ ihV ihW => rw [Set.preimage_inter]; exact ihV.inter ihW

/-- **BPR Corollary 2.79.** A subset of `R` defined by a formula in the language of
ordered fields with coefficients in `R` is a finite union of points and intervals. -/
theorem corollary_2_79 (Φ : Formula (Fin 1) (OrderedFieldAtom (Fin 1) R)) :
    IsFinUnionOfOrdConnected {t : R | (fun _ : Fin 1 => t) ∈ Φ.realization (C := R)} :=
  semialgebraic_sect_FUOC (corollary_2_78 (algebraMap R R).injective Φ)

end Azurite.BPR
