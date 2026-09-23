/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_35

/-!
# BPR Exercise 2.12

Immediate corollaries of the Budan-Fourier theorem:

- If `Var(Der(P); a, b] = 0`, then `P` has no root in `(a, b]`.
- If `Var(Der(P); a, b] = 1`, then `P` has exactly one root in `(a, b]`,
  and that root is simple (multiplicity `1`).

Both follow from the fact that `num(P; (a, b]) ≤ Var(Der(P); a, b]` with
the difference even and non-negative.
-/

namespace Azurite.BPR.Theorem2_35

open Polynomial Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Exercise 2.12 (first part, root-count form).** If
    `Var(Der(P); a, b] = 0`, then `num(P; (a, b]) = 0`. -/
theorem numRoots_eq_zero_of_var_eq_zero
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) {a b : R}
    (hab : a < b) (hV : varBetween (der P) (.finite a) (.finite b) = 0) :
    numRoots P (.finite a) (.finite b) = 0 := by
  have hBF := budan_fourier_finite hIVP hP hab
  rw [hV] at hBF
  have hle : (numRoots P (.finite a) (.finite b) : ℤ) ≤ 0 := hBF.1
  exact_mod_cast le_antisymm hle (Int.natCast_nonneg _)

/-- **BPR Exercise 2.12 (second part, root-count form).** If
    `Var(Der(P); a, b] = 1`, then `num(P; (a, b]) = 1`. -/
theorem numRoots_eq_one_of_var_eq_one
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) {a b : R}
    (hab : a < b) (hV : varBetween (der P) (.finite a) (.finite b) = 1) :
    numRoots P (.finite a) (.finite b) = 1 := by
  have hBF := budan_fourier_finite hIVP hP hab
  rw [hV] at hBF
  obtain ⟨hle, heven⟩ := hBF
  set n : ℕ := numRoots P (.finite a) (.finite b)
  have hle_n : n ≤ 1 := by exact_mod_cast hle
  interval_cases n
  · exact absurd heven (by decide)
  · rfl

/-- **BPR Exercise 2.12 (first part).** If `Var(Der(P); a, b] = 0`, then
    `P` has no root in `(a, b]`. -/
theorem no_root_of_var_eq_zero
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) {a b : R}
    (hab : a < b) (hV : varBetween (der P) (.finite a) (.finite b) = 0) :
    ∀ r ∈ Set.Ioc a b, ¬ P.IsRoot r := by
  classical
  intro r hr hr_root
  have hn := numRoots_eq_zero_of_var_eq_zero hIVP hP hab hV
  rw [numRoots_finite_finite] at hn
  have hfilter_zero : P.roots.filter (fun r => a < r ∧ r ≤ b) = 0 :=
    Multiset.card_eq_zero.mp hn
  have hmem : r ∈ P.roots.filter (fun r => a < r ∧ r ≤ b) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP).mpr hr_root, hr⟩
  rw [hfilter_zero] at hmem
  exact Multiset.notMem_zero r hmem

/-- **BPR Exercise 2.12 (second part).** If `Var(Der(P); a, b] = 1`, then
    `P` has exactly one root in `(a, b]`, and that root is simple
    (i.e. has multiplicity `1`). -/
theorem unique_simple_root_of_var_eq_one
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) {a b : R}
    (hab : a < b) (hV : varBetween (der P) (.finite a) (.finite b) = 1) :
    ∃ r ∈ Set.Ioc a b, P.IsRoot r ∧ P.rootMultiplicity r = 1 ∧
      ∀ r' ∈ Set.Ioc a b, P.IsRoot r' → r' = r := by
  classical
  have hn := numRoots_eq_one_of_var_eq_one hIVP hP hab hV
  rw [numRoots_finite_finite] at hn
  obtain ⟨r, hr_eq⟩ := Multiset.card_eq_one.mp hn
  have hr_mem : r ∈ P.roots.filter (fun r => a < r ∧ r ≤ b) := by
    rw [hr_eq]; exact Multiset.mem_singleton_self r
  rw [Multiset.mem_filter] at hr_mem
  obtain ⟨hr_roots, hr_ioc⟩ := hr_mem
  refine ⟨r, hr_ioc, (Polynomial.mem_roots hP).mp hr_roots, ?_, ?_⟩
  · -- rootMultiplicity r = 1
    have hcnt : Multiset.count r (P.roots.filter (fun r => a < r ∧ r ≤ b)) = 1 := by
      rw [hr_eq]; exact Multiset.count_singleton_self r
    rw [Multiset.count_filter, ite_eq_left hr_ioc] at hcnt
    rw [← Polynomial.count_roots]; exact hcnt
  · intro r' hr' hr'_root
    have hr'_mem : r' ∈ P.roots.filter (fun r => a < r ∧ r ≤ b) :=
      Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP).mpr hr'_root, hr'⟩
    rw [hr_eq, Multiset.mem_singleton] at hr'_mem
    exact hr'_mem

end Azurite.BPR.Theorem2_35
