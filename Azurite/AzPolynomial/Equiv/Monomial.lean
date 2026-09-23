/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Equiv.Basic

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

@[simp] lemma toPoly_C (c : R) : AzPolynomial.toPoly (C c) = Polynomial.C c := by
  unfold C
  split
  · next hc =>
    rw [hc, Polynomial.C_0]
    exact toPoly_zero
  · next hc =>
    dsimp [AzPolynomial.toPoly, List.toPoly]
    simp

@[simp] lemma ofPoly_C (c : R) : AzPolynomial.ofPoly (Polynomial.C c) = C c := by
  rw [← toPoly_inj]
  rw [toPoly_ofPoly]
  exact (toPoly_C c).symm

@[simp] lemma toPoly_X : AzPolynomial.toPoly (X : AzPolynomial R) = Polynomial.X := by
  unfold X
  split
  · next h =>
    ext n
    simp [h, Polynomial.coeff_X]
  · next hc =>
    dsimp [AzPolynomial.toPoly, List.toPoly]
    simp

@[simp] lemma ofPoly_X : AzPolynomial.ofPoly (Polynomial.X : Polynomial R) = X := by
  rw [← toPoly_inj]
  rw [toPoly_ofPoly]
  exact toPoly_X.symm

@[simp] lemma toPoly_monomial (n : ℕ) (a : R) : AzPolynomial.toPoly (monomial n a) = Polynomial.monomial n a := by
  unfold monomial
  split
  · next h =>
    rw [h, Polynomial.monomial_zero_right, toPoly_zero]
  · next hc =>
    ext i
    have hw : ((Array.replicate n 0).push a).toList = List.replicate n 0 ++ [a] := by
      simp
    dsimp [AzPolynomial.toPoly]
    rw [hw, coeff_toPoly]
    by_cases h_i : i = n
    · rw [h_i]
      rw [Polynomial.coeff_monomial]
      simp
      dsimp [List.getCoeff]
      have ht : (List.replicate n (0 : R) ++ [a])[n]? = some a := by
        rw [List.getElem?_append_right (by simp)]
        have h0 : n - (List.replicate n (0 : R)).length = 0 := by simp
        rw [h0]
        simp
      rw [ht]
      rfl
    · rw [Polynomial.coeff_monomial]
      have hn : ¬(n = i) := by intro h; exact h_i h.symm
      simp [hn]
      dsimp [List.getCoeff]
      cases lt_trichotomy i n with
      | inl h_lt =>
        have ht : (List.replicate n (0 : R) ++ [a])[i]? = some 0 := by
          rw [List.getElem?_append]
          simp [h_lt]
        rw [ht]
        rfl
      | inr h_or =>
        cases h_or with
        | inl h_eq =>
          exfalso
          exact h_i h_eq
        | inr h_gt =>
          have h_len : (List.replicate n (0 : R) ++ [a]).length = n + 1 := by simp
          have h_ge : (List.replicate n (0 : R) ++ [a]).length ≤ i := by omega
          have ht : (List.replicate n (0 : R) ++ [a])[i]? = none := List.getElem?_eq_none h_ge
          rw [ht]
          rfl

@[simp] lemma ofPoly_monomial (n : ℕ) (a : R) : AzPolynomial.ofPoly (Polynomial.monomial n a) = monomial n a := by
  rw [← toPoly_inj]
  rw [toPoly_ofPoly]
  exact (toPoly_monomial n a).symm

@[simp] lemma toPoly_erase (n : ℕ) (p : AzPolynomial R) :
  AzPolynomial.toPoly (erase n p) = Polynomial.erase n (AzPolynomial.toPoly p) := by
  ext i
  rw [coeff_toPoly_eq]
  rw [Polynomial.coeff_erase]
  dsimp [erase]
  split
  · next h =>
    by_cases h_eq : i = n
    · rw [ite_eq_left h_eq]
      rw [h_eq]
      dsimp [coeff]
      have ht : p.coeffs[n]? = none := Array.getElem?_eq_none_iff.mpr h
      rw [ht]
      rfl
    · rw [ite_eq_right h_eq]
      rw [coeff_toPoly_eq]
  · next hc =>
    by_cases h_eq : i = n
    · rw [ite_eq_left h_eq]
      rw [h_eq]
      rw [coeff_normalize]
      have h_lt : n < p.coeffs.size := by omega
      have ht : (p.coeffs.setIfInBounds n 0)[n]? = some 0 := by
        exact Array.getElem?_setIfInBounds_self_of_lt h_lt
      rw [ht]
      rfl
    · rw [ite_eq_right h_eq]
      rw [coeff_normalize]
      have h_lt : n < p.coeffs.size := by omega
      have ht : (p.coeffs.setIfInBounds n 0)[i]? = p.coeffs[i]? := by
        exact Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)
      rw [ht]
      rw [← coeff]
      rw [coeff_toPoly_eq]

@[simp] lemma ofPoly_erase (n : ℕ) (p : Polynomial R) :
  AzPolynomial.ofPoly (Polynomial.erase n p) = erase n (AzPolynomial.ofPoly p) := by
  rw [← toPoly_inj]
  have h := toPoly_erase n (AzPolynomial.ofPoly p)
  rw [toPoly_ofPoly p] at h
  rw [toPoly_ofPoly]
  exact h.symm

/-! ### Coefficient of monomial -/

@[simp] lemma coeff_monomial' (n : ℕ) (c : R) (k : ℕ) :
    coeff (monomial n c) k = if k = n then c else 0 := by
  have h := coeff_toPoly_eq (monomial n c) k
  rw [toPoly_monomial, Polynomial.coeff_monomial] at h
  rw [← h]; simp [eq_comm]

end Azurite.AzPolynomial
