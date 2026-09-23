/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_1.Notation1_1

/-!
# BPR Section 2.3 — Semialgebraic Sets

A **semialgebraic subset** of `R^k` is a member of the smallest family of
subsets of `R^k` that contains the algebraic subsets and the *positivity
loci* `{x | P(x) > 0}` for `P ∈ R[X_1, …, X_k]`, and is closed under
complementation, finite unions, and finite intersections.

If the coefficients of the defining polynomials lie in a subring
`D ⊆ R`, BPR says the semialgebraic set is *defined over* `D`. We model
this as a separate predicate `IsSemialgebraicSetOver D` whose
constructors require the polynomial witnesses to live in
`D[X_1, …, X_k]` (evaluated in `R` via `aeval`).

As with `IsConstructibleSet`, closure under union follows from
complementation and intersection by De Morgan, so the inductive only
needs the three constructors.

A corollary (`IsSemialgebraicSet.atom`) records that *all six* of the
`OrderedFieldAtom` comparison relations -- `= 0`, `≠ 0`, `< 0`, `> 0`,
`≤ 0`, `≥ 0` -- yield semialgebraic sets; thus the realisation of any
ordered-field atomic formula is semialgebraic.
-/

namespace Azurite.BPR

open MvPolynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A semialgebraic subset of `R^k`. -/
inductive IsSemialgebraicSet :
    Set (Fin k → R) → Prop where
  | algebraic {V} :
      IsAlgebraicSet V → IsSemialgebraicSet V
  | pos_locus (P : MvPolynomial (Fin k) R) :
      IsSemialgebraicSet {x | eval x P > 0}
  | compl {V} :
      IsSemialgebraicSet V → IsSemialgebraicSet Vᶜ
  | inter {V W} :
      IsSemialgebraicSet V →
      IsSemialgebraicSet W →
      IsSemialgebraicSet (V ∩ W)

omit [IsStrictOrderedRing R] in
/-- Semialgebraic sets are closed under finite union (by De Morgan). -/
theorem IsSemialgebraicSet.union {V W : Set (Fin k → R)}
    (hV : IsSemialgebraicSet V)
    (hW : IsSemialgebraicSet W) :
    IsSemialgebraicSet (V ∪ W) := by
  rw [Set.union_eq_compl_compl_inter_compl]
  exact .compl (.inter (.compl hV) (.compl hW))

/-! ### All six order-relation atoms yield semialgebraic sets. -/

omit [IsStrictOrderedRing R] in
/-- `{x | P(x) = 0}` is semialgebraic (it is algebraic). -/
theorem IsSemialgebraicSet.eqZero (P : MvPolynomial (Fin k) R) :
    IsSemialgebraicSet {x : Fin k → R | eval x P = 0} :=
  .algebraic ⟨{P}, by ext x; simp [Zer]⟩

omit [IsStrictOrderedRing R] in
/-- `{x | P(x) ≠ 0}` is semialgebraic (complement of an algebraic set). -/
theorem IsSemialgebraicSet.neZero (P : MvPolynomial (Fin k) R) :
    IsSemialgebraicSet {x : Fin k → R | eval x P ≠ 0} :=
  (eqZero P).compl

omit [IsStrictOrderedRing R] in
/-- `{x | P(x) > 0}` is semialgebraic (the constructor). -/
theorem IsSemialgebraicSet.gtZero (P : MvPolynomial (Fin k) R) :
    IsSemialgebraicSet {x : Fin k → R | eval x P > 0} :=
  .pos_locus P

/-- `{x | P(x) < 0}` is semialgebraic (rewrite as `(-P)(x) > 0`). -/
theorem IsSemialgebraicSet.ltZero (P : MvPolynomial (Fin k) R) :
    IsSemialgebraicSet {x : Fin k → R | eval x P < 0} := by
  have h := IsSemialgebraicSet.pos_locus (-P)
  convert h using 1
  ext x; simp

/-- `{x | P(x) ≥ 0}` is semialgebraic (complement of `{P < 0}`). -/
theorem IsSemialgebraicSet.geZero (P : MvPolynomial (Fin k) R) :
    IsSemialgebraicSet {x : Fin k → R | eval x P ≥ 0} := by
  have h := (IsSemialgebraicSet.ltZero P).compl
  convert h using 1
  ext x; simp [not_lt]

omit [IsStrictOrderedRing R] in
/-- `{x | P(x) ≤ 0}` is semialgebraic (complement of `{P > 0}`). -/
theorem IsSemialgebraicSet.leZero (P : MvPolynomial (Fin k) R) :
    IsSemialgebraicSet {x : Fin k → R | eval x P ≤ 0} := by
  have h := (IsSemialgebraicSet.pos_locus P).compl
  convert h using 1
  ext x; simp [not_lt]

/-! ### Semialgebraic sets defined over a subring `D ⊆ R`. -/

/-- A semialgebraic subset of `R^k` **defined over** `D`: the polynomial
witnesses are required to lie in `D[X_1, …, X_k]`, evaluated into `R`
via `aeval`. The four constructors mirror `IsSemialgebraicSet`. -/
inductive IsSemialgebraicSetOver (D : Type*) [CommRing D] [Algebra D R] :
    Set (Fin k → R) → Prop where
  | algebraic {V} :
      (∃ poly_set : Finset (MvPolynomial (Fin k) D),
        V = {x | ∀ P ∈ poly_set, aeval x P = 0}) →
      IsSemialgebraicSetOver D V
  | pos_locus (P : MvPolynomial (Fin k) D) :
      IsSemialgebraicSetOver D {x : Fin k → R | aeval x P > 0}
  | compl {V} :
      IsSemialgebraicSetOver D V → IsSemialgebraicSetOver D Vᶜ
  | inter {V W} :
      IsSemialgebraicSetOver D V →
      IsSemialgebraicSetOver D W →
      IsSemialgebraicSetOver D (V ∩ W)

omit [IsStrictOrderedRing R] in
/-- Sets defined over `D` are closed under finite union. -/
theorem IsSemialgebraicSetOver.union {D : Type*} [CommRing D] [Algebra D R]
    {V W : Set (Fin k → R)}
    (hV : IsSemialgebraicSetOver D V)
    (hW : IsSemialgebraicSetOver D W) :
    IsSemialgebraicSetOver D (V ∪ W) := by
  rw [Set.union_eq_compl_compl_inter_compl]
  exact .compl (.inter (.compl hV) (.compl hW))

omit [IsStrictOrderedRing R] in
/-- Every set defined over a subring `D ⊆ R` is semialgebraic: push each
witness polynomial along `algebraMap D R` and use that
`aeval x P = eval x (map (algebraMap D R) P)`. -/
theorem IsSemialgebraicSet.of_definedOver
    {D : Type*} [CommRing D] [Algebra D R] {V : Set (Fin k → R)}
    (h : IsSemialgebraicSetOver D V) : IsSemialgebraicSet V := by
  have heval : ∀ (P : MvPolynomial (Fin k) D) (x : Fin k → R),
      eval x (map (algebraMap D R) P) = aeval x P := fun P x => by
    rw [eval_map, ← aeval_def]
  induction h with
  | algebraic h =>
    obtain ⟨poly_set, hV⟩ := h
    refine .algebraic
      ⟨poly_set.image (map (algebraMap D R)), ?_⟩
    rw [hV]; ext x
    simp only [Zer, Set.mem_ofPred_eq, Finset.mem_image]
    refine ⟨fun hx Q hQ => ?_, fun hx P hP => ?_⟩
    · obtain ⟨P, hP, rfl⟩ := hQ
      rw [heval]; exact hx P hP
    · have := hx (map (algebraMap D R) P) ⟨P, hP, rfl⟩
      rwa [heval] at this
  | pos_locus P =>
    have hpos := IsSemialgebraicSet.pos_locus (map (algebraMap D R) P)
    convert hpos using 1
    ext x; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, heval]
  | compl _ ih => exact ih.compl
  | inter _ _ ihV ihW => exact ihV.inter ihW

/-! ### Atomic semialgebraic-over-`D` sets.

The six ordered-field atomic comparisons are semialgebraic over `D`
provided the polynomial is in `D[X_1, …, X_k]`. -/

omit [IsStrictOrderedRing R] in
theorem IsSemialgebraicSetOver.eqZero {D : Type*} [CommRing D] [Algebra D R]
    (P : MvPolynomial (Fin k) D) :
    IsSemialgebraicSetOver D ({x : Fin k → R | aeval x P = 0}) :=
  .algebraic ⟨{P}, by ext x; simp⟩

omit [IsStrictOrderedRing R] in
theorem IsSemialgebraicSetOver.neZero {D : Type*} [CommRing D] [Algebra D R]
    (P : MvPolynomial (Fin k) D) :
    IsSemialgebraicSetOver D ({x : Fin k → R | aeval x P ≠ 0}) :=
  (IsSemialgebraicSetOver.eqZero (R := R) (D := D) P).compl

omit [IsStrictOrderedRing R] in
theorem IsSemialgebraicSetOver.gtZero {D : Type*} [CommRing D] [Algebra D R]
    (P : MvPolynomial (Fin k) D) :
    IsSemialgebraicSetOver D ({x : Fin k → R | aeval x P > 0}) :=
  .pos_locus P

theorem IsSemialgebraicSetOver.ltZero {D : Type*} [CommRing D] [Algebra D R]
    (P : MvPolynomial (Fin k) D) :
    IsSemialgebraicSetOver D ({x : Fin k → R | aeval x P < 0}) := by
  have h := IsSemialgebraicSetOver.pos_locus (R := R) (D := D) (-P)
  convert h using 1
  ext x; simp

theorem IsSemialgebraicSetOver.geZero {D : Type*} [CommRing D] [Algebra D R]
    (P : MvPolynomial (Fin k) D) :
    IsSemialgebraicSetOver D ({x : Fin k → R | aeval x P ≥ 0}) := by
  have h := (IsSemialgebraicSetOver.ltZero (R := R) (D := D) P).compl
  convert h using 1
  ext x; simp [not_lt]

omit [IsStrictOrderedRing R] in
theorem IsSemialgebraicSetOver.leZero {D : Type*} [CommRing D] [Algebra D R]
    (P : MvPolynomial (Fin k) D) :
    IsSemialgebraicSetOver D ({x : Fin k → R | aeval x P ≤ 0}) := by
  have h := (IsSemialgebraicSetOver.pos_locus (R := R) (D := D) P).compl
  convert h using 1
  ext x; simp [not_lt]

/-! ### Single-generator characterization via `≥ 0`.

BPR's definition lists two polynomial generators (`{P = 0}` and `{P > 0}`),
but the family is in fact generated by the single nonnegativity-locus
generator `{P ≥ 0}` together with the boolean operations. The
equivalence is `IsSemialgebraicSet.iff_ge`. This is a small simplification
of the inductive shape that we do *not* push into the BPR-faithful
definition; it is exposed only as an alternative characterization.
-/

/-- Single-generator variant of semialgebraic subsets: generated from the
nonnegativity loci `{x | P(x) ≥ 0}` for `P ∈ R[X_1, …, X_k]`, closed
under complementation and finite intersection. -/
inductive IsSemialgebraicSetGe : Set (Fin k → R) → Prop where
  | nonneg_locus (P : MvPolynomial (Fin k) R) :
      IsSemialgebraicSetGe {x | eval x P ≥ 0}
  | compl {V} :
      IsSemialgebraicSetGe V → IsSemialgebraicSetGe Vᶜ
  | inter {V W} :
      IsSemialgebraicSetGe V →
      IsSemialgebraicSetGe W →
      IsSemialgebraicSetGe (V ∩ W)

/-- `{x | P(x) = 0}` is `IsSemialgebraicSetGe`: it is
`{P ≥ 0} ∩ {-P ≥ 0}`. -/
theorem IsSemialgebraicSetGe.eqZero (P : MvPolynomial (Fin k) R) :
    IsSemialgebraicSetGe {x : Fin k → R | eval x P = 0} := by
  have h := (nonneg_locus P).inter (nonneg_locus (-P))
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, map_neg, ge_iff_le,
    neg_nonneg, le_antisymm_iff]
  tauto

/-- Every algebraic set is `IsSemialgebraicSetGe`. Proof: induction on
the witness finset, with the empty case `Zer ∅ = R^k = {x | eval x 0 ≥ 0}`
and the insert step `Zer (insert P S) = {P = 0} ∩ Zer S`. -/
theorem IsSemialgebraicSetGe.zer
    (poly_set : Finset (MvPolynomial (Fin k) R)) :
    IsSemialgebraicSetGe (Zer poly_set) := by
  classical
  induction poly_set using Finset.induction with
  | empty =>
    have h := nonneg_locus (0 : MvPolynomial (Fin k) R)
    convert h using 1
    ext x; simp [Zer]
  | @insert P S _ ih =>
    have h := (eqZero P).inter ih
    convert h using 1
    ext x
    simp only [Zer, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Finset.forall_mem_insert]

/-- Every `IsSemialgebraicSetGe` set is semialgebraic. -/
theorem IsSemialgebraicSet.of_isSemialgebraicSetGe
    {V : Set (Fin k → R)} (h : IsSemialgebraicSetGe V) :
    IsSemialgebraicSet V := by
  induction h with
  | nonneg_locus P => exact IsSemialgebraicSet.geZero P
  | compl _ ih => exact ih.compl
  | inter _ _ ihV ihW => exact ihV.inter ihW

/-- Every semialgebraic set is `IsSemialgebraicSetGe`. -/
theorem IsSemialgebraicSetGe.of_isSemialgebraicSet
    {V : Set (Fin k → R)} (h : IsSemialgebraicSet V) :
    IsSemialgebraicSetGe V := by
  induction h with
  | algebraic hAlg =>
    obtain ⟨S, rfl⟩ := hAlg
    exact zer S
  | pos_locus P =>
    have h := (nonneg_locus (-P)).compl
    convert h using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, map_neg, ge_iff_le,
      not_le, neg_lt_zero, gt_iff_lt]
  | compl _ ih => exact ih.compl
  | inter _ _ ihV ihW => exact ihV.inter ihW

/-- The two formulations of semialgebraic-set membership agree:
`IsSemialgebraicSet` (algebraic ∪ positivity loci -- BPR's definition)
and `IsSemialgebraicSetGe` (nonnegativity loci only) describe the same
family. -/
theorem IsSemialgebraicSet.iff_ge {V : Set (Fin k → R)} :
    IsSemialgebraicSet V ↔ IsSemialgebraicSetGe V :=
  ⟨IsSemialgebraicSetGe.of_isSemialgebraicSet,
   IsSemialgebraicSet.of_isSemialgebraicSetGe⟩

end Azurite.BPR
