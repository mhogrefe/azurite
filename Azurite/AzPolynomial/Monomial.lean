/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Basic

/-!
# Constant Polynomials and Monomials

This module defines constructors for basic polynomials natively within `AzPolynomial`,
such as `C` for constant polynomials.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Constructs a constant polynomial with value `c`. -/
def C (c : R) : AzPolynomial R :=
  if h : c = 0 then
    0
  else
    ⟨#[c], by simp [h]⟩

/-- Constructs the polynomial `X`. -/
def X : AzPolynomial R :=
  if h : (1 : R) = 0 then
    0
  else
    ⟨#[0, 1], by simp [h]⟩

/-- Constructs the monomial `a * X^n`. -/
def monomial (n : ℕ) (a : R) : AzPolynomial R :=
  if h : a = 0 then
    0
  else
    ⟨(Array.replicate n 0).push a, by simp [h]⟩

lemma coeff_normalize (a : Array R) (i : ℕ) :
  (normalize a).coeff i = (a[i]?).getD 0 := by
  have h_pop : (normalize a).coeffs.toList = dropTrailingZeros a.toList := toList_popWhile_eq_dropTrailingZeros a
  have ht_arr : (normalize a).coeffs[i]? = (normalize a).coeffs.toList[i]? := (Array.getElem?_toList).symm
  dsimp [coeff, List.getCoeff]
  rw [ht_arr]
  rw [h_pop]
  have h_get := dropTrailingZeros_get? a.toList i
  rw [h_get]
  split
  · next h_lt =>
    have ht_arr_list : a.toList[i]? = a[i]? := Array.getElem?_toList
    have h_eq : a[i]? = a.toList[i]? := ht_arr_list.symm
    rw [h_eq]
  · next h_ge =>
    by_cases h_bounds : i < a.toList.length
    · have h_drop : (a.toList)[i]? = some 0 := by
        have ht : dropTrailingZeros a.toList ++ (a.toList.reverse.takeWhile (· = 0)).reverse = a.toList := eq_dropTrailingZeros_append_takeWhile a.toList
        have ht_get : (dropTrailingZeros a.toList ++ (a.toList.reverse.takeWhile (· = 0)).reverse)[i]? = a.toList[i]? := by rw [ht]
        rw [List.getElem?_append] at ht_get
        rw [ite_eq_right (by omega)] at ht_get
        have ht2 : ((a.toList.reverse.takeWhile (· = 0)).reverse)[i - (dropTrailingZeros a.toList).length]? = a.toList[i]? := ht_get

        have ht3 : a.toList[i]? = ((a.toList.reverse.takeWhile (· = 0)).reverse)[i - (dropTrailingZeros a.toList).length]? := ht2.symm
        rw [ht3]

        have h_len_sum : (dropTrailingZeros a.toList).length + (a.toList.reverse.takeWhile (· = 0)).reverse.length = a.toList.length := by
          have h_len_eq : (dropTrailingZeros a.toList ++ (a.toList.reverse.takeWhile (· = 0)).reverse).length = a.toList.length := by rw [ht]
          rw [List.length_append] at h_len_eq
          exact h_len_eq

        have h_len_rev : (a.toList.reverse.takeWhile (· = 0)).reverse.length = (a.toList.reverse.takeWhile (·=0)).length := by
          exact List.length_reverse

        have h_idx_lt : i - (dropTrailingZeros a.toList).length < (a.toList.reverse.takeWhile (· = 0)).reverse.length := by
          omega

        have h_idx_lt2 : i - (dropTrailingZeros a.toList).length < (a.toList.reverse.takeWhile (· = 0)).length := by
          omega

        have h_get_rev : ∃ x, ((a.toList.reverse.takeWhile (· = 0)).reverse)[i - (dropTrailingZeros a.toList).length]? = some x := by
          exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨h_idx_lt, rfl⟩⟩

        rcases h_get_rev with ⟨x, hx⟩
        rw [hx]

        have hx_rev : (a.toList.reverse.takeWhile (· = 0))[ (a.toList.reverse.takeWhile (· = 0)).length - 1 - (i - (dropTrailingZeros a.toList).length) ]? = some x := by
          have h_rev_idx : i - (dropTrailingZeros a.toList).length < (a.toList.reverse.takeWhile (· = 0)).length := by omega
          have h_rev_get : ((a.toList.reverse.takeWhile (· = 0)).reverse)[i - (dropTrailingZeros a.toList).length]? = (a.toList.reverse.takeWhile (· = 0))[ (a.toList.reverse.takeWhile (· = 0)).length - 1 - (i - (dropTrailingZeros a.toList).length) ]? := by
            exact List.getElem?_reverse h_rev_idx
          rw [h_rev_get] at hx
          exact hx

        have h_idx_lt_3 : (a.toList.reverse.takeWhile (· = 0)).length - 1 - (i - (dropTrailingZeros a.toList).length) < (a.toList.reverse.takeWhile (· = 0)).length := by
          omega

        have hp : (fun x : R => decide (x = 0)) x = true := takeWhile_getElem?_eq_some (a.toList.reverse) ((a.toList.reverse.takeWhile (· = 0)).length - 1 - (i - (dropTrailingZeros a.toList).length)) h_idx_lt_3 x hx_rev
        have hp2 : x = 0 := by exact of_decide_eq_true hp
        rw [hp2]
      have ht_arr_list : a.toList[i]? = a[i]? := Array.getElem?_toList
      rw [ht_arr_list] at h_drop
      rw [h_drop]
      rfl
    · have ht_arr_list : a.toList[i]? = a[i]? := Array.getElem?_toList
      have h_bounds_le : a.toList.length ≤ i := by omega
      have h_none : a.toList[i]? = none := List.getElem?_eq_none h_bounds_le
      rw [ht_arr_list] at h_none
      rw [h_none]

/-- Erases the `n`-th coefficient of a polynomial. -/
def erase (n : ℕ) (p : AzPolynomial R) : AzPolynomial R :=
  if p.coeffs.size ≤ n then
    p
  else
    normalize (p.coeffs.set! n 0)

end Azurite.AzPolynomial
