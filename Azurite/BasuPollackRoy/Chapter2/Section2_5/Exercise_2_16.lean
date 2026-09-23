/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_87

/-! # BPR Exercise 2.16: the extension of a finite semialgebraic set adds no points

**Exercise 2.16.** If `S ⊆ Rᵏ` is a *finite* semialgebraic set, then `Ext(S, R')` equals `S`
(more precisely, the image of `S` under the coordinatewise embedding `Rᵏ ↪ R'ᵏ`).

A finite set `S = {a₁, …, aₘ}` is defined by the quantifier-free formula
`⋁_{a ∈ S} ⋀_{j} (X_j = a_j)` — a disjunction of "point" conjunctions. Its realization over
*any* extension field `C` is exactly `{embed_C a | a ∈ S}` (each conjunct pins one point).
Over `R` this is `S`; over `R'` it is the embedded image. Well-definedness of the extension
(`ext_eq`) then gives `Ext(S, R') = embed_{R'} '' S`.
-/

open MvPolynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `⋀_{j ∈ M} (X_j = a_j)` — the conjunction, over a list `M` of coordinates, of the atoms
pinning each coordinate of the point `a`. The empty conjunction is `0 = 0` (always true). -/
noncomputable def pointFormOn {k : ℕ} (M : List (Fin k)) (a : Fin k → R) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) R) :=
  M.foldr (fun j φ => (Formula.atom ⟨X j - C (a j), OrderRel.eq⟩).and φ)
    (Formula.atom ⟨0, OrderRel.eq⟩)

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem mem_pointFormOn_realization {k : ℕ} {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Algebra R K] (M : List (Fin k)) (a : Fin k → R) (y : Fin k → K) :
    y ∈ (pointFormOn M a).realization (C := K) ↔ ∀ j ∈ M, y j = algebraMap R K (a j) := by
  induction M with
  | nil =>
    have hunfold : pointFormOn ([] : List (Fin k)) a
        = Formula.atom (⟨0, OrderRel.eq⟩ : OrderedFieldAtom (Fin k) R) := rfl
    rw [hunfold]
    simp only [Formula.realization, AtomRealization.interpret, Set.mem_ofPred_eq, map_zero,
      List.not_mem_nil, false_implies, implies_true]
  | cons j M' ih =>
    have hunfold : pointFormOn (j :: M') a
        = (Formula.atom (⟨X j - C (a j), OrderRel.eq⟩ : OrderedFieldAtom (Fin k) R)).and
            (pointFormOn M' a) := rfl
    rw [hunfold]
    simp only [Formula.realization, Set.mem_inter_iff, AtomRealization.interpret,
      Set.mem_ofPred_eq, map_sub, aeval_X, aeval_C, sub_eq_zero, ih, List.forall_mem_cons]

/-- `⋁_{a ∈ L} ⋀_{j} (X_j = a_j)` — the disjunction, over a list `L` of points, of the point
conjunctions. The empty disjunction is `1 = 0` (always false). -/
noncomputable def setForm {k : ℕ} (L : List (Fin k → R)) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) R) :=
  L.foldr (fun a φ => (pointFormOn (List.finRange k) a).or φ) (Formula.atom ⟨1, OrderRel.eq⟩)

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem mem_setForm_realization {k : ℕ} {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Algebra R K] (L : List (Fin k → R)) (y : Fin k → K) :
    y ∈ (setForm L).realization (C := K) ↔ ∃ a ∈ L, ∀ j, y j = algebraMap R K (a j) := by
  induction L with
  | nil =>
    have hunfold : setForm ([] : List (Fin k → R))
        = Formula.atom (⟨1, OrderRel.eq⟩ : OrderedFieldAtom (Fin k) R) := rfl
    rw [hunfold]
    simp only [Formula.realization, AtomRealization.interpret, Set.mem_ofPred_eq, map_one,
      List.not_mem_nil, false_and, exists_false, iff_false]
    exact one_ne_zero
  | cons a L' ih =>
    have hunfold : setForm (a :: L')
        = (pointFormOn (List.finRange k) a).or (setForm L') := rfl
    rw [hunfold]
    simp only [Formula.realization, Set.mem_union, mem_pointFormOn_realization,
      List.mem_finRange, forall_const, ih, List.exists_mem_cons_iff]

section Extension

variable [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

/-- **BPR Exercise 2.16.** The extension of a *finite* semialgebraic set `S ⊆ Rᵏ` adds no
points: `Ext(S, R')` is the image of `S` under the coordinatewise embedding `Rᵏ ↪ R'ᵏ`. -/
theorem exercise_2_16 {k : ℕ} {S : Set (Fin k → R)} (hSfin : S.Finite)
    (hS : IsSemialgebraicSet S) :
    extension (R' := R') S hS = (fun y : Fin k → R => algebraMap R R' ∘ y) '' S := by
  classical
  set L := hSfin.toFinset.toList with hL
  have hmemL : ∀ a, a ∈ L ↔ a ∈ S := fun a => by
    rw [hL, Finset.mem_toList, Set.Finite.mem_toFinset]
  have hself : ∀ x : R, algebraMap R R x = x := fun x => by simp
  -- `S` is the realization of `setForm L` over `R`.
  have hSR : S = (setForm L).realization (C := R) := by
    ext y
    rw [mem_setForm_realization]
    constructor
    · intro hy; exact ⟨y, (hmemL y).mpr hy, fun j => (hself (y j)).symm⟩
    · rintro ⟨a, haL, hya⟩
      have : y = a := funext fun j => by rw [hya j, hself]
      rw [this]; exact (hmemL a).mp haL
  -- transport along well-definedness, then read off the realization over `R'`.
  rw [ext_eq hS hSR]
  ext z
  rw [mem_setForm_realization, Set.mem_image]
  constructor
  · rintro ⟨a, haL, hza⟩
    exact ⟨a, (hmemL a).mp haL, funext fun j => (hza j).symm⟩
  · rintro ⟨a, haS, hza⟩
    exact ⟨a, (hmemL a).mpr haS, fun j => by rw [← hza]; rfl⟩

end Extension

end Azurite.BPR
