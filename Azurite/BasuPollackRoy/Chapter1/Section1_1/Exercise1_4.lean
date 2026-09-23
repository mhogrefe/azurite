/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization

/-!
# Exercise 1.4: Field Axioms

The field axioms as formulas. The ring axioms (commutativity, associativity,
distributivity, identities) are tautological polynomial identities. The
remaining non-trivial axioms are additive inverse, multiplicative inverse,
and nontriviality. We also formalize the algebraic-closure axiom schema
$\Phi_d$ asserting that every monic polynomial of degree $d$ has a root.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {C : Type*} [Field C]

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D] [Algebra D C]

/-- ∀X₀ ∃X₁, X₀ + X₁ = 0 (additive inverse). -/
noncomputable def additiveInverse : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  forall_ 0 (.exists_ 1 (eq_zero (X 0 + X 1)))

/-- ∀X₀, X₀ = 0 ∨ ∃X₁, X₀X₁ − 1 = 0
    (multiplicative inverse for nonzero elements). -/
noncomputable def multiplicativeInverse : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  forall_ 0 (.or (eq_zero (X 0))
    (.exists_ 1 (eq_zero (X 0 * X 1 - 1))))

/-- 1 ≠ 0 (nontriviality). -/
noncomputable def fieldNontriviality : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  ne_zero 1

theorem additiveInverse_holds :
    additiveInverse.realization (C := C) =
      Set.univ := by
  ext y; simp [additiveInverse, realization]
  intro c
  exact ⟨-c, by simp⟩

theorem multiplicativeInverse_holds :
    multiplicativeInverse.realization (C := C) =
      Set.univ := by
  ext y; simp [multiplicativeInverse, realization]
  intro c; by_cases hc : c = 0
  · subst hc; simp
  · right; exact ⟨c⁻¹, by field_simp [hc]; ring⟩

theorem fieldNontriviality_holds :
    fieldNontriviality.realization (C := C) =
      Set.univ := by
  ext y; simp [fieldNontriviality, ne_zero, FieldAtom.neZero]

/-!
### Algebraic Closure Axiom Φ_d

Φ_d asserts that every monic polynomial of degree d has a
root: ∀Y₁...∀Y_d ∃X, X^d + Y₁X^(d-1) + ... + Y_d = 0.
-/

/-- The generic monic polynomial of degree d:
    X₀^d + X₁ · X₀^(d-1) + X₂ · X₀^(d-2) + ... + X_d.
    Variable 0 is the root variable, variables 1..d are
    coefficients. -/
noncomputable def monicPoly (d : ℕ) :
    MvPolynomial (Fin (d + 1)) ℤ :=
  X 0 ^ d + ∑ i : Fin d,
    X ⟨i + 1, by omega⟩ * X 0 ^ (d - 1 - i)

/-- Φ_d: ∀Y₁ ∀Y₂ ... ∀Y_d ∃X, monicPoly d = 0.
    Example: Φ₂ = ∀Y₁ ∀Y₂ ∃X, X² + Y₁X + Y₂ = 0. -/
noncomputable def phiD (d : ℕ) : Formula (Fin (d + 1)) (FieldAtom (Fin (d + 1)) ℤ) :=
  (List.finRange d).foldr
    (fun i acc => forall_ ⟨i.val + 1, by omega⟩ acc)
    (.exists_ 0 (eq_zero (monicPoly d)))

private theorem realization_forall_of_univ [DecidableEq σ]
    (x : σ) (Φ : Formula σ (FieldAtom σ D))
    (h : Φ.realization (C := C) = Set.univ) :
    (forall_ x Φ).realization (C := C) = Set.univ := by
  ext y; simp [realization, h]

private theorem realization_foldr_forall_of_univ
    [DecidableEq σ] (xs : List σ) (body : Formula σ (FieldAtom σ D))
    (h : body.realization (C := C) = Set.univ) :
    (xs.foldr (fun x acc => forall_ x acc)
      body).realization (C := C) = Set.univ := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
    simp [List.foldr]
    exact realization_forall_of_univ x _ ih

private theorem realization_finRange_forall_of_univ {n : ℕ}
    (d : ℕ) (g : Fin d → Fin (n + 1)) (body : Formula (Fin (n + 1)) (FieldAtom (Fin (n + 1)) ℤ))
    (h : body.realization (C := C) = Set.univ) :
    ((List.finRange d).foldr (fun i acc => forall_ (g i) acc)
      body).realization (C := C) = Set.univ := by
  induction (List.finRange d) with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldr]
    exact realization_forall_of_univ (g x) _ ih

/-- Φ_d holds in any algebraically closed field. -/
theorem phiD_holds [IsAlgClosed C] (d : ℕ) (hd : 0 < d) :
    (phiD d).realization (C := C) = Set.univ := by
  unfold phiD
  apply realization_finRange_forall_of_univ
  ext y
  simp only [realization, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  let q := ∑ i : Fin d,
    Polynomial.C (y ⟨↑i + 1, by omega⟩) * Polynomial.X ^ (d - 1 - (i : ℕ))
  let p : C[X] := Polynomial.X ^ d + q
  -- natDegree q ≤ d - 1
  have hnd : q.natDegree ≤ d - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by omega)
  -- degree q < d
  have hq : q.degree < (d : WithBot ℕ) := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hq0]; omega
  -- p is monic
  have hp : p.Monic := Polynomial.monic_X_pow_add hq
  -- p.natDegree = d
  have hpnd : p.natDegree = d := by
    show (Polynomial.X ^ d + q).natDegree = d
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · by_cases hq0 : q = 0
      · simp [hq0, hd]
      · simp; exact lt_of_le_of_lt hnd (by omega)
  -- degree p ≠ 0
  have hdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, hpnd]
    exact_mod_cast hd.ne'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root p hdeg
  rw [Polynomial.IsRoot] at hc
  refine ⟨c, ?_⟩
  simp only [monicPoly]
  convert hc using 1
  simp [p, q, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]

private lemma forall_realization_univ_iff
    {D : Type*} [CommRing D] [Algebra D C]
    {σ : Type*} [DecidableEq σ]
    (x : σ) (Φ : Formula σ (FieldAtom σ D)) :
    (forall_ x Φ).realization (C := C) = Set.univ ↔
    Φ.realization (C := C) = Set.univ := by
  constructor
  · intro h; ext z; simp only [Set.mem_univ, iff_true]
    have hz := (Set.eq_univ_iff_forall.mp h) z
    simp only [realization, Set.mem_ofPred_eq] at hz
    convert hz (z x); exact (Function.update_eq_self x z).symm
  · intro h; ext y; simp only [Set.mem_univ, iff_true]
    simp only [realization, Set.mem_ofPred_eq]
    intro c; exact Set.eq_univ_iff_forall.mp h _

private lemma phiD_univ_iff (d : ℕ) :
    (phiD d).realization (C := C) = Set.univ ↔
    (Formula.exists_ (0 : Fin (d + 1))
      (Formula.eq_zero (monicPoly d))).realization (C := C) = Set.univ := by
  unfold phiD
  suffices h : ∀ (xs : List (Fin d)) (body : Formula (Fin (d + 1)) (FieldAtom (Fin (d + 1)) ℤ)),
    (xs.foldr (fun i acc => forall_ ⟨i.val + 1, by omega⟩ acc)
      body).realization (C := C) = Set.univ ↔
    body.realization (C := C) = Set.univ from h _ _
  intro xs body; induction xs with
  | nil => exact Iff.rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact (forall_realization_univ_iff _ _).trans ih

/-- Converse of `phiD_holds`: if Φ_d holds for all d ≥ 1,
    then C is algebraically closed. -/
theorem isAlgClosed_of_phiD_holds
    (h : ∀ d, 0 < d → (phiD d).realization (C := C) = Set.univ) :
    IsAlgClosed C := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  have hd : 0 < p.natDegree := by
    by_contra hle; push Not at hle
    exact not_irreducible_one
      ((Polynomial.eq_one_of_monic_natDegree_zero hp (by omega)) ▸ hirr)
  set d := p.natDegree with d_def
  have hphi := (phiD_univ_iff d).mp (h d hd)
  have hR := Set.eq_univ_iff_forall.mp hphi
  set y : Fin (d + 1) → C := fun j => p.coeff (d - j.val)
  have hy := hR y
  simp only [realization, Set.mem_ofPred_eq] at hy
  obtain ⟨c, hc⟩ := hy
  refine ⟨c, ?_⟩
  simp only [monicPoly] at hc
  have h_upd : ∀ i : Fin d,
    Function.update y (0 : Fin (d + 1)) c ⟨↑i + 1, by omega⟩ =
    p.coeff (d - 1 - (i : ℕ)) := by
    intro i
    rw [Function.update_of_ne (show (⟨↑i + 1, by omega⟩ : Fin (d + 1)) ≠ 0
      from by simp [Fin.ext_iff])]
    simp only [y]; congr 1; omega
  simp only [realization_eq_zero, Set.mem_ofPred_eq] at hc
  simp only [map_add, map_pow, MvPolynomial.aeval_X,
    map_sum, map_mul, Function.update_self] at hc
  simp_rw [h_upd] at hc
  rw [← hc]
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
  simp only [d_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [Finset.sum_range_succ,
    show p.coeff p.natDegree = 1 from hp.coeff_natDegree,
    one_mul, add_comm]
  congr 1
  rw [← Finset.sum_range_reflect (fun j => p.coeff j * c ^ j) d]
  symm
  apply Finset.sum_nbij (fun (i : Fin d) => (i : ℕ))
  · intro i _; exact Finset.mem_range.mpr i.isLt
  · intro i₁ i₂ _ _ h; exact Fin.val_injective h
  · intro j hj
    exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

end Formula

end Azurite.BPR
