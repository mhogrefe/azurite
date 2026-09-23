/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Equiv.Add
import Mathlib.Algebra.Polynomial.Coeff

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-! ### Shared helpers -/

-- Helper: coeff beyond (p.size + q.size - 1) sums to zero
private lemma coeff_beyond_zero (p q : AzPolynomial R) (n : ℕ)
    (h_ge : ¬(n < p.coeffs.size + q.coeffs.size - 1)) :
    ∑ x ∈ Finset.antidiagonal n, (AzPolynomial.toPoly p).coeff x.1 * (AzPolynomial.toPoly q).coeff x.2 = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  have hpz : (AzPolynomial.toPoly p).coeff x.1 = 0 ∨ (AzPolynomial.toPoly q).coeff x.2 = 0 := by
    simp_rw [coeff_toPoly]
    by_contra! hc
    have ht1 : x.1 < p.coeffs.size := by
      by_contra h_ge_p
      push Not at h_ge_p
      exact hc.1 (by dsimp [coeff]; rw [Array.getElem?_eq_none (by omega)]; rfl)
    have ht2 : x.2 < q.coeffs.size := by
      by_contra h_ge_q
      push Not at h_ge_q
      exact hc.2 (by dsimp [coeff]; rw [Array.getElem?_eq_none (by omega)]; rfl)
    omega
  rcases hpz with h1 | h2
  · rw [h1, zero_mul]
  · rw [h2, mul_zero]

-- Helper: empty coeffs → zero poly
omit [DecidableEq R] in
private lemma empty_implies_zero_mul (p : AzPolynomial R) (hp : p.coeffs.size = 0) : p = 0 :=
  AzPolynomial.ext (Array.eq_empty_of_size_eq_zero hp)

/-! ### Proofs for `mulBasecaseList` (old implementation, kept for comparison) -/

omit [DecidableEq R] in
lemma List.sum_map_eq_finset_sum_antidiagonal (n : ℕ) (p q : AzPolynomial R) :
  ((List.range (n + 1)).map (fun i => p.coeff i * q.coeff (n - i))).sum =
  ∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2 := by
  have hl : ∑ i ∈ Finset.range (n + 1), p.coeff i * q.coeff (n - i) = ((List.range (n + 1)).map (fun i => p.coeff i * q.coeff (n - i))).sum := rfl
  rw [← hl]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j) n).symm

@[simp] lemma toPoly_mulBasecaseList (p q : AzPolynomial R) :
  AzPolynomial.toPoly (mulBasecaseList p q) = AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  ext n; rw [Polynomial.coeff_mul]
  dsimp [mulBasecaseList]
  split
  · next h_empty =>
    revert h_empty; simp only [Bool.or_eq_true, beq_iff_eq]; intro h_empty
    rcases h_empty with hp | hq
    · rw [empty_implies_zero_mul p hp]; simp
    · rw [empty_implies_zero_mul q hq]; simp
  · next h_not_empty =>
    rw [toPoly_normalize, coeff_list_toPoly]
    simp only [Array.toList_ofFn]
    rw [List.getCoeff_ofFn_aux]
    split
    · next h_lt =>
      change ((List.range (n + 1)).map (fun idx => p.coeff idx * q.coeff (n - idx))).sum = _
      simp_rw [coeff_toPoly]
      exact List.sum_map_eq_finset_sum_antidiagonal n p q
    · exact (coeff_beyond_zero p q n ‹_›).symm

/-! ### Proofs for `mulBasecase` (Finset.sum-based implementation) -/

@[simp] lemma toPoly_mulBasecase (p q : AzPolynomial R) :
  AzPolynomial.toPoly (mulBasecase p q) = AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  ext n; rw [Polynomial.coeff_mul]
  dsimp [mulBasecase]
  split
  · next h_empty =>
    revert h_empty; simp only [Bool.or_eq_true, beq_iff_eq]; intro h_empty
    rcases h_empty with hp | hq
    · rw [empty_implies_zero_mul p hp]; simp
    · rw [empty_implies_zero_mul q hq]; simp
  · next h_not_empty =>
    rw [toPoly_normalize, coeff_list_toPoly]
    simp only [Array.toList_ofFn]
    rw [List.getCoeff_ofFn_aux]
    split
    · next h_lt =>
      simp_rw [coeff_toPoly]
      exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j) n).symm
    · exact (coeff_beyond_zero p q n ‹_›).symm

/-! ### Proofs for `mulBasecaseFold` (Fin.foldl-based implementation) -/

omit [DecidableEq R] in
/-- `Fin.foldl` of addition equals `Finset.range` sum. -/
lemma fin_foldl_eq_finset_range_sum (n : ℕ) (f : ℕ → R) :
    Fin.foldl n (fun acc i => acc + f i.val) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, Fin.foldl_succ_last]
    congr 1

/-- `mulBasecaseFold` produces the same result as `mulBasecase`. -/
lemma mulBasecaseFold_eq_mulBasecase (p q : AzPolynomial R) :
    mulBasecaseFold p q = mulBasecase p q := by
  simp only [mulBasecaseFold, mulBasecaseCoeffs, mulBasecase]
  split
  · apply AzPolynomial.ext; simp [normalize]
  · apply congrArg; apply congrArg; funext n
    exact fin_foldl_eq_finset_range_sum (↑n + 1)
      (fun j => p.coeff j * q.coeff (↑n - j))

@[simp] lemma toPoly_mulBasecaseFold (p q : AzPolynomial R) :
    AzPolynomial.toPoly (mulBasecaseFold p q) = AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  rw [mulBasecaseFold_eq_mulBasecase]; exact toPoly_mulBasecase p q

/-! ### Lift to `mul` -/

@[simp] lemma toPoly_mul (p q : AzPolynomial R) :
    AzPolynomial.toPoly (p * q) = AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  show AzPolynomial.toPoly (AzPolynomialMulConfig.dmul p q) = _
  simp [AzPolynomialMulConfig.dmul, toPoly_mulBasecaseFold]

@[simp] lemma coeff_mul (p q : AzPolynomial R) (n : ℕ) :
    coeff (p * q) n = ∑ x ∈ Finset.antidiagonal n, coeff p x.1 * coeff q x.2 := by
  have h := toPoly_mul p q
  have hc := congrArg (fun p => Polynomial.coeff p n) h
  rw [Polynomial.coeff_mul] at hc
  simp_rw [coeff_toPoly] at hc
  exact hc

@[simp] lemma ofPoly_mul (p q : Polynomial R) :
    AzPolynomial.ofPoly (p * q) = AzPolynomial.ofPoly p * AzPolynomial.ofPoly q := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_mul, toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

/-! ### Algebraic properties of multiplication -/

theorem add_mul' (a b c : AzPolynomial R) : (a + b) * c = a * c + b * c := by
  apply toPoly_inj.mp
  simp only [toPoly_mul, toPoly_add, _root_.add_mul]

theorem zero_mul' (a : AzPolynomial R) : (0 : AzPolynomial R) * a = 0 := by
  apply toPoly_inj.mp
  simp [toPoly_mul, toPoly_zero]

end Azurite.AzPolynomial
