/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14

/-!
# Two corollaries of Lemma 1.14

Corollary 1: a finite family $\mathcal{P}$ has a common root in $C$
iff $\lcode{listGcd}\,\mathcal{P}$ has positive degree (i.e.\ is not
a nonzero constant).

Corollary 2: a finite family $\mathcal{Q}$ has a common non-root in
$C$ iff every polynomial in the family is nonzero (equivalently,
$\deg(\prod \mathcal{Q}) \ge 0$).
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]
variable {C : Type*} [Field C]

/-- BPR Lemma 1.14 Corollary 1: A finite family of polynomials has a common root in an algebraically closed field if and only if its GCD is not a non-zero constant. -/
lemma lemma_1_14_cor1 [IsAlgClosed C] [Algebra K C] [DecidableEq K] [DecidableEq C]
    (P_fam : List K[X]) :
    (∃ x : C, ∀ P ∈ P_fam, aeval x P = 0) ↔ (listGcd P_fam).degree ≠ 0 := by
  by_cases hP : listGcd P_fam = 0
  · have h_deg : (listGcd P_fam).degree ≠ 0 := by rw [hP, degree_zero]; decide
    have h_exists : ∃ x : C, ∀ P ∈ P_fam, aeval x P = 0 := by
      use (0 : C)
      intro P hP_in
      have H_dvd : listGcd P_fam ∣ P := (listGcd_isListGCD P_fam).1 P hP_in
      rw [hP] at H_dvd
      have H_P : P = 0 := zero_dvd_iff.mp H_dvd
      rw [H_P, map_zero]
    exact iff_of_true h_exists h_deg
  · have h_d : (listGcd P_fam).natDegree < (listGcd P_fam).natDegree + 1 := Nat.lt_succ_self _
    have H := lemma_1_14 (C := C) P_fam ([] : List K[X]) hP (d := (listGcd P_fam).natDegree + 1) h_d
    have h_LHS : (∃ x : C, (∀ P ∈ P_fam, aeval x P = 0) ∧ (∀ Q ∈ ([] : List K[X]), aeval x Q ≠ 0)) ↔
      (∃ x : C, ∀ P ∈ P_fam, aeval x P = 0) := by
      simp
    have h_RHS : (gcd (listGcd P_fam) (([] : List K[X]).prod ^ ((listGcd P_fam).natDegree + 1))).natDegree ≠
      (listGcd P_fam).natDegree ↔ (listGcd P_fam).degree ≠ 0 := by
      have H_Q : ([] : List K[X]).prod = (1 : K[X]) := rfl
      have H_Q_pow : (1 : K[X]) ^ ((listGcd P_fam).natDegree + 1) = 1 := one_pow _
      have H_gcd_deg : (gcd (listGcd P_fam) (1 : K[X])).natDegree = 0 := by
        have H_dvd : gcd (listGcd P_fam) 1 ∣ (1 : K[X]) := gcd_dvd_right _ _
        have H_unit : IsUnit (gcd (listGcd P_fam) 1) := isUnit_of_dvd_one H_dvd
        exact natDegree_eq_of_degree_eq_some (isUnit_iff_degree_eq_zero.mp H_unit)
      rw [H_Q, H_Q_pow, H_gcd_deg, ne_comm]
      constructor
      · intro h_nat h_deg
        have : (listGcd P_fam).natDegree = 0 := by
          have h1 : (listGcd P_fam).degree = (listGcd P_fam).natDegree := degree_eq_natDegree hP
          have h2 : (listGcd P_fam).natDegree = 0 ↔ (listGcd P_fam).degree = 0 := by
            constructor
            · intro h; rw [h1, h, Nat.cast_zero]
            · intro h; rw [h1] at h; exact Nat.cast_eq_zero.mp h
          exact h2.mpr h_deg
        exact h_nat this
      · intro h_deg h_nat
        have : (listGcd P_fam).degree = 0 := by
          have h1 : (listGcd P_fam).degree = (listGcd P_fam).natDegree := degree_eq_natDegree hP
          rw [h1, h_nat, Nat.cast_zero]
        exact h_deg this
    rw [← h_LHS]
    rw [← h_RHS]
    exact H

/-- BPR Lemma 1.14 Corollary 2: There is a common non-root for a finite family of polynomials over an algebraically closed field if and only if no polynomial in the family is zero. -/
lemma lemma_1_14_cor2 [IsAlgClosed C] [Algebra K C] [DecidableEq K] [DecidableEq C]
    (Q_fam : List K[X]) :
    (∃ x : C, ∀ Q ∈ Q_fam, aeval x Q ≠ 0) ↔ 0 ≤ (Q_fam.prod).degree := by
  have h_equiv : (∃ x : C, ∀ Q ∈ Q_fam, aeval x Q ≠ 0) ↔ (∃ x : C, aeval x (Q_fam.prod) ≠ 0) := by
    constructor
    · intro ⟨x, hx⟩
      exact ⟨x, not_isRoot_listProd_iff_forall_not_isRoot.mpr hx⟩
    · intro ⟨x, hx⟩
      exact ⟨x, not_isRoot_listProd_iff_forall_not_isRoot.mp hx⟩
  rw [h_equiv]
  constructor
  · rintro ⟨x, hx⟩
    have h_prod_ne_zero : Q_fam.prod ≠ 0 := by
      rintro h_prod_eq_zero
      rw [h_prod_eq_zero, map_zero] at hx
      exact hx rfl
    have hbot : (Q_fam.prod).degree = (Q_fam.prod).natDegree := degree_eq_natDegree h_prod_ne_zero
    rw [hbot]
    exact Nat.cast_nonneg _
  · rintro h_deg
    have h_prod_ne_zero : Q_fam.prod ≠ 0 := by
      intro contra
      rw [contra, degree_zero] at h_deg
      exact not_le.mpr (WithBot.bot_lt_coe 0) h_deg
    have h_map_ne_zero : (Q_fam.prod.map (algebraMap K C)) ≠ 0 := by
      intro h_map
      have h1 : Q_fam.prod = 0 := Polynomial.map_eq_zero_iff (algebraMap K C).injective |>.mp h_map
      exact h_prod_ne_zero h1
    obtain ⟨x, hx⟩ : ∃ x : C, x ∉ (Q_fam.prod.map (algebraMap K C)).roots.toFinset := Infinite.exists_notMem_finset _
    use x
    have h_not_root : ¬ IsRoot (Q_fam.prod.map (algebraMap K C)) x := by
      intro h_root
      have h_mem : x ∈ (Q_fam.prod.map (algebraMap K C)).roots := mem_roots h_map_ne_zero |>.mpr h_root
      have h_mem_finset : x ∈ (Q_fam.prod.map (algebraMap K C)).roots.toFinset := Multiset.mem_toFinset.mpr h_mem
      exact hx h_mem_finset
    have h_aeval : aeval x Q_fam.prod = eval x (Q_fam.prod.map (algebraMap K C)) := by
      rw [aeval_def, eval_map]
    rw [h_aeval]
    exact h_not_root

end Azurite.BPR
