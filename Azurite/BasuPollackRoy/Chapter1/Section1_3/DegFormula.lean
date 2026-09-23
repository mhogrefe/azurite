/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Polynomial
import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization

/-! # BPR Section 1.3 — Notation 1.18: Degree as a formula

For `Q ∈ D[Y₁, …, Y_k][X]`, the **degree formula** `degFormula Q i`
is a quantifier-free formula in the variables `Y₁, …, Y_k` whose
`C`-realization is the set of `y ∈ C^k` such that the specialized
polynomial `Q_y(X)` has degree `i` (where `i ∈ WithBot ℕ`, with
`⊥` representing degree `−∞`, i.e. `Q_y = 0`).

Concretely:
- `degFormula Q ⊥` is the conjunction `⋀_{j=0}^{natDeg Q} (coeff Q j = 0)`.
- `degFormula Q (some n)` is `coeff Q n ≠ 0 ∧ ⋀_{j=n+1}^{natDeg Q} (coeff Q j = 0)`.
- `degEqFormula Q₁ Q₂` is `⋁_i (degFormula Q₁ i ∧ degFormula Q₂ i)`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ}

section DegFormula

variable {D : Type*} [CommRing D]

/-- BPR Notation 1.18: `deg_X(Q) = i` as a formula in `Fin k` variables.

For `Q ∈ D[Y₁,…,Yₖ][X]`:
- `i = ⊥` means all coefficients vanish (degree = −∞, i.e., `Q_y = 0`)
- `i = some n` means `coeff Q n ≠ 0` and all higher coefficients vanish -/
noncomputable def degFormula
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i : WithBot ℕ) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  match i with
  | ⊥ => Formula.conjList ((List.range (Q.natDegree + 1)).map fun j =>
      Formula.eq_zero (Q.coeff j))
  | some n => .and
      (Formula.ne_zero (Q.coeff n))
      (Formula.conjList ((List.range (Q.natDegree - n)).map fun j =>
        Formula.eq_zero (Q.coeff (n + 1 + j))))

/-- BPR Notation 1.18: `deg_X(Q₁) = deg_X(Q₂)` as a formula.

This is the finite disjunction over all possible degree values
`i ∈ {⊥, 0, 1, …, max(natDeg Q₁, natDeg Q₂)}` of
`degFormula Q₁ i ∧ degFormula Q₂ i`. -/
noncomputable def degEqFormula
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  let m := max Q₁.natDegree Q₂.natDegree
  Formula.disjList (
    ((degFormula Q₁ ⊥).and (degFormula Q₂ ⊥)) ::
    (List.range (m + 1)).map fun i =>
      (degFormula Q₁ (some i)).and (degFormula Q₂ (some i)))

/-- The negation of `degEqFormula`: `deg_X(Q₁_y) ≠ deg_X(Q₂_y)`. -/
noncomputable def degNeqFormula
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  .not (degEqFormula Q₁ Q₂)

/-! #### Degree characterization lemma -/

private theorem degree_eq_coe_iff
    {R : Type*} [Semiring R] (p : Polynomial R) (n : ℕ) :
    p.degree = ↑n ↔ p.coeff n ≠ 0 ∧ ∀ m, n < m → p.coeff m = 0 := by
  constructor
  · intro h
    exact ⟨by rw [← Polynomial.natDegree_eq_of_degree_eq_some h]
              exact Polynomial.leadingCoeff_ne_zero.mpr (by intro h0; simp [h0] at h),
           fun m hm => (Polynomial.degree_le_iff_coeff_zero p n).mp (le_of_eq h) m
              (by exact_mod_cast hm)⟩
  · intro ⟨hne, hhi⟩
    exact le_antisymm
      ((Polynomial.degree_le_iff_coeff_zero p n).mpr
        fun m hm => hhi m (by exact_mod_cast hm))
      (Polynomial.le_degree_of_ne_zero hne)

/-- Coefficients above `natDegree` vanish: a convenient shorthand. -/
private theorem coeff_eq_zero_of_natDegree_lt
    {R : Type*} [Semiring R] (Q : Polynomial R) {n : ℕ}
    (h : Q.natDegree < n) : Q.coeff n = 0 := by
  have := Polynomial.degree_le_natDegree (p := Q)
  exact (Polynomial.degree_le_iff_coeff_zero Q Q.natDegree).mp this n
    (by exact_mod_cast h)

/-! #### Helper: coefficient vanishing above `natDegree` under ring homs -/

private theorem map_eq_zero_iff
    {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (Q : Polynomial R) :
    Q.map f = 0 ↔ ∀ n ≤ Q.natDegree, f (Q.coeff n) = 0 := by
  constructor
  · intro h n _
    have := congr_arg (fun p => Polynomial.coeff p n) h
    simp [Polynomial.coeff_map] at this
    exact this
  · intro h
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hn : n ≤ Q.natDegree
    · exact h n hn
    · have : Q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt Q (by omega)
      simp [this]

theorem map_degree_eq_coe_iff
    {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (Q : Polynomial R) (n : ℕ) :
    (Q.map f).degree = ↑n ↔
      f (Q.coeff n) ≠ 0 ∧ ∀ m, n < m → m ≤ Q.natDegree → f (Q.coeff m) = 0 := by
  rw [degree_eq_coe_iff]
  simp only [Polynomial.coeff_map]
  constructor
  · exact fun ⟨hne, hhi⟩ => ⟨hne, fun m hm _ => hhi m hm⟩
  · intro ⟨hne, hhi⟩
    exact ⟨hne, fun m hm => by
      by_cases hm' : m ≤ Q.natDegree
      · exact hhi m hm hm'
      · have : Q.coeff m = 0 := coeff_eq_zero_of_natDegree_lt Q (by omega)
        simp [this]⟩

/-! #### Realization of `degFormula` -/

/-- The realization of `degFormula Q i` is the set of `y ∈ C^k` where
the specialized polynomial `Q.map (aeval y)` has degree `i`.

This is the formal counterpart of BPR's claim that `Reali(deg_X(Q) = i)`
partitions `C^k` according to the degree of `Q_y`. -/
theorem realization_degFormula
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i : WithBot ℕ) :
    (degFormula Q i).realization (C := C) =
      { y | (Q.map (MvPolynomial.aeval y).toRingHom).degree = i } := by
  match i with
  | ⊥ =>
    ext y
    simp only [degFormula, Formula.realization_conjList, Set.mem_ofPred_eq,
      List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Formula.realization_eq_zero]
    rw [Polynomial.degree_eq_bot, map_eq_zero_iff]
    constructor
    · exact fun h n hn => h n (by omega)
    · exact fun h n hn => h n (by omega)
  | some n =>
    ext y
    simp only [degFormula, Formula.realization_and, Formula.realization_ne_zero,
      Formula.realization_conjList, Set.mem_inter_iff, Set.mem_ofPred_eq,
      List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Formula.realization_eq_zero]
    rw [show (some n : WithBot ℕ) = (↑n : WithBot ℕ) from rfl,
        map_degree_eq_coe_iff]
    constructor
    · intro ⟨hne, hhi⟩
      exact ⟨hne, fun m hm hm' => by
        have hlt : m - (n + 1) < Q.natDegree - n := by omega
        have := hhi (m - (n + 1)) hlt
        rwa [show n + 1 + (m - (n + 1)) = m by omega] at this⟩
    · intro ⟨hne, hhi⟩
      exact ⟨hne, fun j hj => hhi (n + 1 + j) (by omega) (by omega)⟩

/-- The realization of `degEqFormula Q₁ Q₂` is the set of `y ∈ C^k`
where `Q₁_y` and `Q₂_y` have the same degree. -/
theorem realization_degEqFormula
    {C : Type*} [Field C] [Algebra D C]
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    (degEqFormula Q₁ Q₂).realization (C := C) =
      { y | (Q₁.map (MvPolynomial.aeval y).toRingHom).degree =
            (Q₂.map (MvPolynomial.aeval y).toRingHom).degree } := by
  ext y
  simp only [degEqFormula, Formula.realization_disjList, Set.mem_ofPred_eq,
    List.mem_cons, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, rfl | ⟨i, _, rfl⟩, hmem⟩ <;>
    rw [Formula.realization_and, Set.mem_inter_iff] at hmem <;>
    exact ((Set.ext_iff.mp (realization_degFormula _ _) y).mp hmem.1).trans
      ((Set.ext_iff.mp (realization_degFormula _ _) y).mp hmem.2).symm
  · intro h
    match hd : (Q₁.map (MvPolynomial.aeval y).toRingHom).degree with
    | ⊥ =>
      refine ⟨_, Or.inl rfl, ?_⟩
      rw [Formula.realization_and, Set.mem_inter_iff]
      exact ⟨(Set.ext_iff.mp (realization_degFormula _ _) y).mpr hd,
        (Set.ext_iff.mp (realization_degFormula _ _) y).mpr (h.symm.trans hd)⟩
    | some n =>
      refine ⟨_, Or.inr ⟨n, ?_, rfl⟩, ?_⟩
      · simp only [Nat.lt_succ_iff]
        have hnd := Polynomial.natDegree_eq_of_degree_eq_some hd
        have hle : (Q₁.map (MvPolynomial.aeval y).toRingHom).natDegree ≤ Q₁.natDegree :=
          Polynomial.natDegree_map_le
        exact le_trans (by omega : n ≤ Q₁.natDegree) (le_max_left _ _)
      · rw [Formula.realization_and, Set.mem_inter_iff]
        exact ⟨(Set.ext_iff.mp (realization_degFormula _ _) y).mpr hd,
          (Set.ext_iff.mp (realization_degFormula _ _) y).mpr (h.symm.trans hd)⟩

/-- The realization of `degNeqFormula Q₁ Q₂` is the set of `y ∈ C^k`
where `Q₁_y` and `Q₂_y` have distinct degrees. -/
theorem realization_degNeqFormula
    {C : Type*} [Field C] [Algebra D C]
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    (degNeqFormula Q₁ Q₂).realization (C := C) =
      { y | (Q₁.map (MvPolynomial.aeval y).toRingHom).degree ≠
            (Q₂.map (MvPolynomial.aeval y).toRingHom).degree } := by
  simp only [degNeqFormula, Formula.realization, realization_degEqFormula]
  ext y; simp [Set.mem_compl_iff, Set.mem_ofPred_eq]

/-! #### Partition property -/

/-- The `degFormula` family partitions `C^k`: every `y` satisfies
exactly one `degFormula Q i`. (Covering part.) -/
theorem degFormula_covering
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (y : Fin k → C) :
    ∃ i : WithBot ℕ, y ∈ (degFormula Q i).realization (C := C) := by
  simp only [realization_degFormula, Set.mem_ofPred_eq]
  exact ⟨_, rfl⟩

/-- The `degFormula` family partitions `C^k`: distinct degree values
give disjoint realizations. (Disjointness part.) -/
theorem degFormula_disjoint
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i j : WithBot ℕ) (hij : i ≠ j) :
    (degFormula Q i).realization (C := C) ∩
      (degFormula Q j).realization (C := C) = ∅ := by
  simp only [realization_degFormula]
  ext y; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro h; rw [h]; exact hij

end DegFormula

end Azurite.BPR
