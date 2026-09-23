/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleSets
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_1

/-!
# Exercise 1.2

A constructible subset of `C` is either finite or the complement of a finite set.

Proof outline: induct on the structure of `IsConstructibleSet`. The algebraic
case is Exercise 1.1. Complement and intersection branches recover the
finite-or-cofinite dichotomy via De Morgan and the constructible-set
union lemma.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {C : Type*} [Field C] [IsAlgClosed C]

omit [IsAlgClosed C] in
/-- Exercise 1.2: A constructible subset of C is either finite
    or cofinite. -/
theorem exercise_1_2 (V : Set (Fin 1 → C))
    (hV : IsConstructibleSet V) :
    V.Finite ∨ Vᶜ.Finite := by
  induction hV with
  | algebraic hA =>
    rcases exercise_1_1 _ hA with hfin | huniv
    · exact Or.inl hfin
    · right; rw [huniv]; simp
  | compl _ ih =>
    rcases ih with h | h
    · exact Or.inr (by rwa [compl_compl])
    · exact Or.inl h
  | inter _ _ ihV ihW =>
    rcases ihV, ihW with ⟨hV | hV, hW | hW⟩
    · exact Or.inl (hV.subset Set.inter_subset_left)
    · exact Or.inl (hV.subset Set.inter_subset_left)
    · exact Or.inl (hW.subset Set.inter_subset_right)
    · right; rw [Set.compl_inter]; exact hV.union hW

end Azurite.BPR
