/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleSets
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization

/-!
# Constructible ↔ QF-Realizable

A set is constructible if and only if it is the realization of
a quantifier-free formula.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

namespace Formula

variable {D : Type*} [CommRing D] {σ : Type*}
variable {C : Type*} [Field C] [Algebra D C]

/-- Conjunction of `eq_zero` atoms from a list. -/
noncomputable def conjEqZero : List (MvPolynomial σ D) → Formula σ (FieldAtom σ D)
  | [] => eq_zero 0
  | [P] => eq_zero P
  | P :: Ps => .and (eq_zero P) (conjEqZero Ps)

theorem conjEqZero_isQF :
    ∀ (L : List (MvPolynomial σ D)),
    (conjEqZero L).IsQuantifierFree
  | [] => trivial
  | [_] => trivial
  | _ :: _ :: Ps =>
    ⟨trivial, conjEqZero_isQF (_ :: Ps)⟩

theorem conjEqZero_realization [DecidableEq σ]
    {C : Type*} [Field C] [Algebra D C] :
    ∀ (L : List (MvPolynomial σ D)),
    (conjEqZero L).realization (C := C) =
      { y | ∀ P ∈ L, MvPolynomial.aeval y P = 0}
  | [] => by
    ext y; simp [conjEqZero, map_zero]
  | [P] => by
    ext y; simp [conjEqZero]
  | P :: Q :: Ps => by
    ext y
    simp only [conjEqZero, realization, Set.mem_inter_iff,
      Set.mem_ofPred_eq, List.mem_cons]
    rw [show (conjEqZero (Q :: Ps)).realization (C := C) =
      { y | ∀ P ∈ (Q :: Ps), MvPolynomial.aeval y P = 0}
      from conjEqZero_realization (Q :: Ps)]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hP, hrest⟩ R hR
      rcases hR with rfl | hR
      · exact hP
      · exact hrest R (List.mem_cons.mpr hR)
    · intro h
      exact ⟨h P (Or.inl rfl),
        fun R hR => h R (Or.inr (List.mem_cons.mp hR))⟩

end Formula

variable {k : ℕ} {C : Type*} [Field C]

open Formula in
/-- Backward: QF-realizable → constructible. -/
theorem qf_realizable_isConstructible
    {Φ : Formula (Fin k) (FieldAtom (Fin k) C)} (hqf : Φ.IsQuantifierFree) :
    IsConstructibleSet (Φ.realization (C := C)) := by
  induction Φ with
  | atom a =>
    by_cases h : a.isEq = true
    · -- P = 0 case: algebraic set
      exact .algebraic ⟨{a.poly}, by
        ext y; simp [Zer, realization, h, MvPolynomial.aeval_def]⟩
    · -- P ≠ 0 case: complement of algebraic set
      have : (atom a).realization (C := C) =
          ({y | MvPolynomial.eval y a.poly = 0} : Set (Fin k → C))ᶜ := by
        ext y; simp [realization, h, Set.mem_compl_iff, Set.mem_ofPred_eq]
      rw [this]
      exact .compl (.algebraic ⟨{a.poly}, by
        ext y; simp [Zer]⟩)
  | not Φ ih => exact .compl (ih hqf)
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    exact .inter (ih₁ hqf.1) (ih₂ hqf.2)
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    exact (ih₁ hqf.1).union (ih₂ hqf.2)
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    exact (IsConstructibleSet.compl (ih₁ hqf.1)).union (ih₂ hqf.2)
  | exists_ x Φ _ => exact absurd hqf id
  | forall_ x Φ _ => exact absurd hqf id

open Formula in
/-- Forward: constructible → QF-realizable. -/
theorem constructible_isQFRealizable
    (V : Set (Fin k → C)) (hV : IsConstructibleSet V) :
    ∃ Φ : Formula (Fin k) (FieldAtom (Fin k) C), Φ.IsQuantifierFree ∧
      V = Φ.realization (C := C) := by
  induction hV with
  | algebraic hA =>
    obtain ⟨poly_set, rfl⟩ := hA
    exact ⟨conjEqZero poly_set.toList, conjEqZero_isQF _,
      by rw [conjEqZero_realization]
         ext y; simp [Zer, MvPolynomial.aeval_def]⟩
  | compl _ ih =>
    obtain ⟨Φ, hqf, rfl⟩ := ih
    exact ⟨.not Φ, hqf, by simp [realization]⟩
  | inter _ _ ih₁ ih₂ =>
    obtain ⟨Φ₁, hqf₁, rfl⟩ := ih₁
    obtain ⟨Φ₂, hqf₂, rfl⟩ := ih₂
    exact ⟨.and Φ₁ Φ₂, ⟨hqf₁, hqf₂⟩,
      by simp [realization]⟩

/-- A set is constructible iff it is the realization of a
    quantifier-free formula. -/
theorem constructible_iff_qfRealizable
    (V : Set (Fin k → C)) :
    IsConstructibleSet V ↔
    ∃ Φ : Formula (Fin k) (FieldAtom (Fin k) C), Φ.IsQuantifierFree ∧
      V = Φ.realization (C := C) :=
  ⟨constructible_isQFRealizable V,
   fun ⟨_, hqf, hV⟩ => hV ▸ qf_realizable_isConstructible hqf⟩

end Azurite.BPR
