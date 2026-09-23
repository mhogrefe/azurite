/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleSets
import Azurite.BasuPollackRoy.Chapter2.Section2_3.SemialgebraicSets
import Azurite.BasuPollackRoy.Chapter2.Section2_3.SumOfSquaresZer

/-!
# BPR Section 2.3 — Basic Semialgebraic Sets

A *basic semialgebraic subset* of `R^k` is a set of the form
`{x | P(x) = 0 ∧ ⋀ q ∈ 𝒬, q(x) > 0}` for a polynomial `P` and a finset
`𝒬` of polynomials. BPR states (without proof) that every semialgebraic
set is a finite union of basic ones -- a disjunctive normal form theorem.

The proof goes through an inductive predicate `IsFinUnionOfBasic` (the
finite-union closure of basic semialgebraic sets) with three
constructors. Closure under intersection uses the sum-of-squares trick
(`zer_eq_zer_singleton_sumSq`) to combine two equality witnesses into
one; closure under complement is a Finset induction on the positivity
finset that case-splits each constraint into a finite disjunction.
-/

namespace Azurite.BPR

open MvPolynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A basic semialgebraic subset of `R^k`: an equality at one polynomial
together with strict positivity at each polynomial of a finset. -/
def IsBasicSemialgebraicSet (V : Set (Fin k → R)) : Prop :=
  ∃ (P : MvPolynomial (Fin k) R) (Q : Finset (MvPolynomial (Fin k) R)),
    V = {x | eval x P = 0 ∧ ∀ q ∈ Q, eval x q > 0}

/-- Inductive closure: finite unions of basic semialgebraic subsets. -/
inductive IsFinUnionOfBasic : Set (Fin k → R) → Prop where
  | empty : IsFinUnionOfBasic ∅
  | basic {B} : IsBasicSemialgebraicSet B → IsFinUnionOfBasic B
  | union {V W} :
      IsFinUnionOfBasic V →
      IsFinUnionOfBasic W →
      IsFinUnionOfBasic (V ∪ W)

/-! ### Small library of basic sets. -/

omit [IsStrictOrderedRing R] in
/-- `R^k` is a basic semialgebraic set: `{x | 0 = 0}`. -/
theorem IsBasicSemialgebraicSet.univ :
    IsBasicSemialgebraicSet (Set.univ : Set (Fin k → R)) :=
  ⟨0, ∅, by ext x; simp⟩

omit [IsStrictOrderedRing R] in
/-- `{x | P(x) = 0}` is basic. -/
theorem IsBasicSemialgebraicSet.eqZero (P : MvPolynomial (Fin k) R) :
    IsBasicSemialgebraicSet ({x : Fin k → R | eval x P = 0}) :=
  ⟨P, ∅, by ext x; simp⟩

omit [IsStrictOrderedRing R] in
/-- `{x | P(x) > 0}` is basic. -/
theorem IsBasicSemialgebraicSet.gtZero (P : MvPolynomial (Fin k) R) :
    IsBasicSemialgebraicSet ({x : Fin k → R | eval x P > 0}) :=
  ⟨0, {P}, by ext x; simp⟩

/-- `{x | P(x) < 0}` is basic (witness `-P > 0`). -/
theorem IsBasicSemialgebraicSet.ltZero (P : MvPolynomial (Fin k) R) :
    IsBasicSemialgebraicSet ({x : Fin k → R | eval x P < 0}) := by
  refine ⟨0, {-P}, ?_⟩
  ext x
  simp [map_neg]

/-! ### Easy direction: every basic / FUB set is semialgebraic. -/

omit [IsStrictOrderedRing R] in
/-- The empty set is semialgebraic: it is the complement of `R^k`. -/
theorem IsSemialgebraicSet.empty :
    IsSemialgebraicSet (∅ : Set (Fin k → R)) := by
  have h := (IsSemialgebraicSet.algebraic
    (isAlgebraicSet_univ : IsAlgebraicSet (Set.univ : Set (Fin k → R)))).compl
  rwa [Set.compl_univ] at h

omit [IsStrictOrderedRing R] in
theorem IsBasicSemialgebraicSet.isSemialgebraicSet
    {V : Set (Fin k → R)} (h : IsBasicSemialgebraicSet V) :
    IsSemialgebraicSet V := by
  obtain ⟨P, Q, rfl⟩ := h
  classical
  induction Q using Finset.induction with
  | empty =>
    have h_eq := IsSemialgebraicSet.eqZero P
    convert h_eq using 1
    ext x; simp
  | @insert q' Q' _ ih =>
    have h_inter := ih.inter (IsSemialgebraicSet.pos_locus q')
    convert h_inter using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
      Finset.forall_mem_insert]
    tauto

omit [IsStrictOrderedRing R] in
theorem IsFinUnionOfBasic.isSemialgebraicSet
    {V : Set (Fin k → R)} (h : IsFinUnionOfBasic V) :
    IsSemialgebraicSet V := by
  induction h with
  | empty => exact IsSemialgebraicSet.empty
  | basic hB => exact hB.isSemialgebraicSet
  | union _ _ ihV ihW => exact ihV.union ihW

/-! ### Closure under intersection.

The intersection of two basic semialgebraic sets is basic: combine
the equality witnesses into one via `P₁² + P₂²` (sum of squares is
zero iff each summand is, over a linearly ordered field) and union
the positivity finsets. -/

theorem IsBasicSemialgebraicSet.inter
    {V W : Set (Fin k → R)}
    (hV : IsBasicSemialgebraicSet V)
    (hW : IsBasicSemialgebraicSet W) :
    IsBasicSemialgebraicSet (V ∩ W) := by
  obtain ⟨P₁, Q₁, rfl⟩ := hV
  obtain ⟨P₂, Q₂, rfl⟩ := hW
  refine ⟨P₁ ^ 2 + P₂ ^ 2, Q₁ ∪ Q₂, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union,
    map_add, map_pow]
  constructor
  · rintro ⟨⟨hp₁, hQ₁⟩, hp₂, hQ₂⟩
    refine ⟨by rw [hp₁, hp₂]; ring, ?_⟩
    rintro q (hq | hq)
    · exact hQ₁ q hq
    · exact hQ₂ q hq
  · rintro ⟨hsum, hQ⟩
    have ha : 0 ≤ (eval x P₁) ^ 2 := sq_nonneg _
    have hb : 0 ≤ (eval x P₂) ^ 2 := sq_nonneg _
    have hP₁ : (eval x P₁) ^ 2 = 0 := by linarith
    have hP₂ : (eval x P₂) ^ 2 = 0 := by linarith
    refine ⟨⟨sq_eq_zero_iff.mp hP₁, fun q hq => hQ q (Or.inl hq)⟩,
            sq_eq_zero_iff.mp hP₂, fun q hq => hQ q (Or.inr hq)⟩

private theorem IsFinUnionOfBasic.basicInter
    {B W : Set (Fin k → R)}
    (hB : IsBasicSemialgebraicSet B)
    (hW : IsFinUnionOfBasic W) :
    IsFinUnionOfBasic (B ∩ W) := by
  induction hW with
  | empty =>
    rw [Set.inter_empty]; exact .empty
  | basic hB' =>
    exact .basic (hB.inter hB')
  | union _ _ ihW₁ ihW₂ =>
    rw [Set.inter_union_distrib_left]
    exact ihW₁.union ihW₂

theorem IsFinUnionOfBasic.inter
    {V W : Set (Fin k → R)}
    (hV : IsFinUnionOfBasic V)
    (hW : IsFinUnionOfBasic W) :
    IsFinUnionOfBasic (V ∩ W) := by
  induction hV with
  | empty =>
    rw [Set.empty_inter]; exact .empty
  | basic hB =>
    exact basicInter hB hW
  | union _ _ ihV₁ ihV₂ =>
    rw [Set.union_inter_distrib_right]
    exact ihV₁.union ihV₂

/-! ### Closure under complement.

The hard step is: the complement of a single basic semialgebraic set
`{P = 0 ∧ ⋀ q ∈ 𝒬, q > 0}` is a finite union of basic semialgebraic
sets. Proof by induction on the finset `𝒬`, using the decompositions
`{x | P ≠ 0} = {P > 0} ∪ {P < 0}` and
`{x | q ≤ 0} = {q < 0} ∪ {q = 0}`. -/

omit [IsStrictOrderedRing R] in
theorem IsFinUnionOfBasic.univ :
    IsFinUnionOfBasic (Set.univ : Set (Fin k → R)) :=
  .basic IsBasicSemialgebraicSet.univ

private theorem isFinUnionOfBasic_le_zero (P : MvPolynomial (Fin k) R) :
    IsFinUnionOfBasic ({x : Fin k → R | eval x P ≤ 0}) := by
  have h_lt : IsFinUnionOfBasic ({x : Fin k → R | eval x P < 0}) :=
    .basic (.ltZero P)
  have h_eq : IsFinUnionOfBasic ({x : Fin k → R | eval x P = 0}) :=
    .basic (.eqZero P)
  have h := h_lt.union h_eq
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  exact le_iff_lt_or_eq

private theorem isFinUnionOfBasic_ne_zero (P : MvPolynomial (Fin k) R) :
    IsFinUnionOfBasic ({x : Fin k → R | eval x P ≠ 0}) := by
  have h_pos : IsFinUnionOfBasic ({x : Fin k → R | eval x P > 0}) :=
    .basic (.gtZero P)
  have h_neg : IsFinUnionOfBasic ({x : Fin k → R | eval x P < 0}) :=
    .basic (.ltZero P)
  have h := h_pos.union h_neg
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  exact ⟨fun h => (lt_or_gt_of_ne h).symm,
         fun h => h.elim ne_of_gt ne_of_lt⟩

private theorem complementOfBasic_isFUB
    (P : MvPolynomial (Fin k) R)
    (Q : Finset (MvPolynomial (Fin k) R)) :
    IsFinUnionOfBasic
      ({x : Fin k → R | eval x P = 0 ∧ ∀ q ∈ Q, eval x q > 0}ᶜ) := by
  classical
  induction Q using Finset.induction with
  | empty =>
    have h := isFinUnionOfBasic_ne_zero P
    convert h using 1
    ext x
    simp
  | @insert q' Q' _ ih =>
    have h_le := isFinUnionOfBasic_le_zero q'
    have h := ih.union h_le
    convert h using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union,
      Finset.forall_mem_insert]
    constructor
    · intro hn
      by_cases hq' : eval x q' > 0
      · left; rintro ⟨hP, hQ'⟩; exact hn ⟨hP, hq', hQ'⟩
      · right; exact not_lt.mp hq'
    · rintro (hn | hq')
      · rintro ⟨hP, _, hQ'⟩; exact hn ⟨hP, hQ'⟩
      · rintro ⟨_, hq, _⟩; linarith

theorem IsFinUnionOfBasic.compl
    {V : Set (Fin k → R)} (h : IsFinUnionOfBasic V) :
    IsFinUnionOfBasic Vᶜ := by
  induction h with
  | empty =>
    rw [Set.compl_empty]; exact IsFinUnionOfBasic.univ
  | basic hB =>
    obtain ⟨P, Q, rfl⟩ := hB
    exact complementOfBasic_isFUB P Q
  | union _ _ ihV ihW =>
    rw [Set.compl_union]
    exact ihV.inter ihW

/-! ### Main theorem.

Every semialgebraic set is a finite union of basic semialgebraic sets.
Proof by induction on `IsSemialgebraicSet`:
* an algebraic set `Zer 𝒫` is basic with witness `∑ P ∈ 𝒫, P²`
  (sum-of-squares: `Zer 𝒫 = Zer {∑ P²}`);
* a positivity locus `{P > 0}` is basic by definition;
* complement and intersection are inherited from the closure results.
-/

theorem IsFinUnionOfBasic.of_isSemialgebraicSet
    {V : Set (Fin k → R)} (h : IsSemialgebraicSet V) :
    IsFinUnionOfBasic V := by
  induction h with
  | algebraic hAlg =>
    obtain ⟨S, rfl⟩ := hAlg
    refine .basic ⟨∑ P ∈ S, P ^ 2, ∅, ?_⟩
    rw [zer_eq_zer_singleton_sumSq S]
    ext x; simp [Zer]
  | pos_locus P =>
    exact .basic (.gtZero P)
  | compl _ ih =>
    exact ih.compl
  | inter _ _ ihV ihW =>
    exact ihV.inter ihW

/-- A semialgebraic subset of `R^k` is the same as a finite union of
basic semialgebraic subsets -- BPR's normal-form statement. -/
theorem IsSemialgebraicSet.iff_isFinUnionOfBasic
    {V : Set (Fin k → R)} :
    IsSemialgebraicSet V ↔ IsFinUnionOfBasic V :=
  ⟨IsFinUnionOfBasic.of_isSemialgebraicSet,
   IsFinUnionOfBasic.isSemialgebraicSet⟩

/-! ### Constructible vs semialgebraic.

BPR observes that constructible sets (Chapter 1) are semialgebraic
(Chapter 2 Section 2.3): in particular, every basic constructible set
`{x | P(x) = 0 ∧ ⋀ Q ∈ 𝒬, Q(x) ≠ 0}` is the basic semialgebraic set
`{x | P(x) = 0 ∧ ⋀ Q ∈ 𝒬, Q²(x) > 0}`, using `Q ≠ 0 ↔ Q² > 0` over a
linearly ordered field. Sum-of-squares collapses any Zer-witness into a
single equality, and squaring lifts non-vanishing into strict
positivity, so the Chapter 1 `IsBasicConstructibleSet` inductive
embeds into `IsBasicSemialgebraicSet`. The wider `IsConstructibleSet`
embeds into `IsSemialgebraicSet` for free -- same closure operations. -/

private lemma sq_pos_iff_ne_zero (a : R) : 0 < a ^ 2 ↔ a ≠ 0 := by
  refine ⟨fun h ha => by simp [ha] at h, fun h => ?_⟩
  exact (sq_nonneg a).lt_of_ne (Ne.symm (pow_ne_zero _ h))

/-- The explicit BPR shape `{P = 0 ∧ ⋀ Q ≠ 0}` is basic semialgebraic
(positivity finset `{Q² | Q ∈ 𝒬}`, since `Q ≠ 0 ↔ Q² > 0`). -/
theorem IsBasicSemialgebraicSet.of_eqZero_neZeroes
    (P : MvPolynomial (Fin k) R)
    (Q : Finset (MvPolynomial (Fin k) R)) :
    IsBasicSemialgebraicSet
      ({x : Fin k → R | eval x P = 0 ∧ ∀ q ∈ Q, eval x q ≠ 0}) := by
  classical
  refine ⟨P, Q.image (· ^ 2), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨hP, hQ⟩
    refine ⟨hP, ?_⟩
    rintro q' ⟨q, hq, rfl⟩
    rw [map_pow]
    exact (sq_pos_iff_ne_zero _).mpr (hQ q hq)
  · rintro ⟨hP, hQ⟩
    refine ⟨hP, fun q hq => ?_⟩
    have h := hQ (q ^ 2) ⟨q, hq, rfl⟩
    rw [map_pow] at h
    exact (sq_pos_iff_ne_zero _).mp h

/-- Every basic constructible subset of `R^k` is basic semialgebraic.
Sum-of-squares collapses an algebraic-set's Zer-witness into one
equality polynomial, and `Q² > 0 ↔ Q ≠ 0` turns the complement of an
algebraic set into a single positivity constraint. -/
theorem IsBasicSemialgebraicSet.of_isBasicConstructibleSet
    {V : Set (Fin k → R)} (h : IsBasicConstructibleSet V) :
    IsBasicSemialgebraicSet V := by
  induction h with
  | algebraic hAlg =>
    obtain ⟨S, rfl⟩ := hAlg
    refine ⟨∑ P ∈ S, P ^ 2, ∅, ?_⟩
    rw [zer_eq_zer_singleton_sumSq S]
    ext x; simp [Zer]
  | compl_algebraic hAlg =>
    obtain ⟨S, rfl⟩ := hAlg
    refine ⟨0, {(∑ P ∈ S, P ^ 2) ^ 2}, ?_⟩
    rw [zer_eq_zer_singleton_sumSq S]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Zer,
      Finset.mem_singleton, forall_eq, map_zero,
      true_and, map_pow]
    exact (sq_pos_iff_ne_zero _).symm
  | inter _ _ ihV ihW => exact ihV.inter ihW

omit [IsStrictOrderedRing R] in
/-- Constructible subsets of `R^k` are semialgebraic: same closure
operations (algebraic ∪ complement ∪ intersection), so the
`IsConstructibleSet` inductive maps onto `IsSemialgebraicSet`
constructor-for-constructor. -/
theorem IsSemialgebraicSet.of_isConstructibleSet
    {V : Set (Fin k → R)} (h : IsConstructibleSet V) :
    IsSemialgebraicSet V := by
  induction h with
  | algebraic hAlg => exact .algebraic hAlg
  | compl _ ih => exact ih.compl
  | inter _ _ ihV ihW => exact ihV.inter ihW

end Azurite.BPR
