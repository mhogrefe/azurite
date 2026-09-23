/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Algebra.Basic

/-!
# Computational Univariate Polynomials

This module defines `AzPolynomial`, a computational representation of univariate
polynomials over an arbitrary Semiring/Ring `R`.

Unlike `Polynomial R` in Mathlib (which represents polynomials as finitely
supported functions `Finsupp`), `AzPolynomial R` focuses on a dense representation
using a list of coefficients.

The representation maintains the invariant that the last element of the
list (the leading coefficient) is always non-zero, unless the polynomial is the
zero polynomial (represented by the empty list).
-/

namespace Azurite

/-- A univariate polynomial represented as a dense array of coefficients
`#[a_0, a_1, ..., a_n]`. The last element `a_n` is guaranteed to be non-zero
(unless the array is empty, representing the zero polynomial). -/
structure AzPolynomial (R : Type _) [Semiring R] where
  coeffs : Array R
  -- If the array is non-empty, the last element is not 0
  last_ne_zero : coeffs.back? ≠ some 0
deriving Repr, DecidableEq

@[ext] lemma AzPolynomial.ext {R : Type _} [Semiring R] {p q : Azurite.AzPolynomial R} (h : p.coeffs = q.coeffs) : p = q := by
  cases p
  cases q
  simp at h
  congr
end Azurite

variable {R : Type _} [Semiring R]

def List.getCoeff (l : List R) (i : ℕ) : R := (l[i]?).getD 0

@[simp] lemma List.getCoeff_nil (i : ℕ) : ([] : List R).getCoeff i = 0 := rfl
@[simp] lemma List.getCoeff_cons_zero (a : R) (as : List R) : (a :: as).getCoeff 0 = a := rfl
@[simp] lemma List.getCoeff_cons_succ (a : R) (as : List R) (i : ℕ) : (a :: as).getCoeff (i + 1) = as.getCoeff i := rfl

namespace Azurite.AzPolynomial

/-- The zero polynomial is represented by the empty array. -/
def zero {R : Type _} [Semiring R] : AzPolynomial R :=
  ⟨#[], by simp⟩

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Removes trailing zeros from a list of coefficients. -/
def dropTrailingZeros (l : List R) : List R :=
  (l.reverse.dropWhile (· = 0)).reverse

lemma head?_dropWhile (l : List R) :
  (l.dropWhile (· = 0)).head? ≠ some 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    by_cases ha : a = 0
    · simp [ha]
      exact ih
    · simp [ha]

lemma dropTrailingZeros_last (l : List R) :
  let dropped := dropTrailingZeros l
  dropped = [] ∨ dropped.getLast? ≠ some 0 := by
  dsimp [dropTrailingZeros]
  by_cases h : (l.reverse.dropWhile (· = 0)).reverse = []
  · left
    exact h
  · right
    have h1 : ((l.reverse.dropWhile (· = 0)).reverse).getLast? = (l.reverse.dropWhile (· = 0)).head? := by
      apply List.getLast?_reverse
    rw [h1]
    exact head?_dropWhile (l.reverse)

lemma dropTrailingZeros_prefix (l : List R) :
  dropTrailingZeros l <+: l := by
  dsimp [dropTrailingZeros]
  have h1 : (l.reverse.dropWhile (· = 0)).reverse ++ (l.reverse.takeWhile (· = 0)).reverse = l := by
    have h2 : l.reverse.takeWhile (· = 0) ++ l.reverse.dropWhile (· = 0) = l.reverse := by
      exact List.takeWhile_append_dropWhile
    have h3 : (l.reverse.takeWhile (· = 0) ++ l.reverse.dropWhile (· = 0)).reverse = l.reverse.reverse := by rw [h2]
    rw [List.reverse_append] at h3
    rw [List.reverse_reverse] at h3
    exact h3
  exact ⟨(l.reverse.takeWhile (· = 0)).reverse, h1⟩

lemma IsPrefix_get? {α : Type _} {l₁ l₂ : List α} (h : l₁ <+: l₂) (i : ℕ) (hi : i < l₁.length) :
  l₂[i]? = l₁[i]? := by
  rcases h with ⟨t, ht⟩
  rw [← ht]
  rw [List.getElem?_append]
  rw [ite_eq_left hi]

lemma dropTrailingZeros_get? (l : List R) (i : ℕ) :
  (dropTrailingZeros l)[i]? = if i < (dropTrailingZeros l).length then l[i]? else none := by
  have h_pref := dropTrailingZeros_prefix l
  split
  · next h_lt =>
    have ht := IsPrefix_get? h_pref i h_lt
    exact ht.symm
  · next h_ge =>
    exact List.getElem?_eq_none (by omega)

lemma takeWhile_getElem?_eq_some {α : Type _} {p : α → Bool} (l : List α) (j : ℕ) (hj : j < (l.takeWhile p).length) (x : α) (hx : (l.takeWhile p)[j]? = some x) :
  p x = true := by
  induction l generalizing j with
  | nil =>
    simp at hj
  | cons a as ih =>
    by_cases hpa : p a = true
    · simp [hpa] at hj hx
      cases j with
      | zero =>
        simp at hx
        rw [← hx]
        exact hpa
      | succ j =>
        exact ih j (by omega) hx
    · simp [hpa] at hj

lemma eq_dropTrailingZeros_append_takeWhile (l : List R) :
  dropTrailingZeros l ++ (l.reverse.takeWhile (· = 0)).reverse = l := by
  have h1 : (l.reverse.dropWhile (· = 0)).reverse ++ (l.reverse.takeWhile (· = 0)).reverse = l := by
    have h2 : l.reverse.takeWhile (· = 0) ++ l.reverse.dropWhile (· = 0) = l.reverse := by
      exact List.takeWhile_append_dropWhile
    have h3 : (l.reverse.takeWhile (· = 0) ++ l.reverse.dropWhile (· = 0)).reverse = l.reverse.reverse := by rw [h2]
    rw [List.reverse_append] at h3
    rw [List.reverse_reverse] at h3
    exact h3
  exact h1

lemma toList_popWhile_eq_dropTrailingZeros (a : Array R) :
  (a.popWhile (· = 0)).toList = dropTrailingZeros a.toList := by
  dsimp [dropTrailingZeros]
  have h := List.popWhile_toArray (· = 0) a.toList
  have ht : a.toList.toArray = a := by simp
  rw [ht] at h
  rw [h]

/-- Normalizes an array of coefficients by dropping trailing zeros and constructs a AzPolynomial. -/
def normalize (a : Array R) : AzPolynomial R :=
  let arr := a.popWhile (· = 0)
  ⟨arr, by
    intro h
    let orig := dropTrailingZeros a.toList
    have h1 : arr.toList = orig := toList_popWhile_eq_dropTrailingZeros a
    have h2 : arr.toList.getLast? = arr.back? := by simp
    rw [← h2] at h
    rw [h1] at h
    have ht := dropTrailingZeros_last a.toList
    change orig = [] ∨ orig.getLast? ≠ some 0 at ht
    rcases ht with h_empty | h_not_zero
    · rw [h_empty] at h
      simp at h
    · exact h_not_zero h
  ⟩

/--
The polynomial 1.

In an arbitrary Semiring, `1` might equal `0` (the trivial ring).
If `1 = 0`, then returning `#[1]` violates our invariant because the last element is `0`.
Therefore, we require `[DecidableEq R]` to return `#[]` (the zero polynomial) if `1 = 0`.
-/
def one {R : Type _} [Semiring R] [DecidableEq R] : AzPolynomial R :=
  if h : (1 : R) = 0 then
    zero
  else
    ⟨#[(1 : R)], by simp [h]⟩

instance {R : Type _} [Semiring R] : Inhabited (AzPolynomial R) := ⟨zero⟩
instance {R : Type _} [Semiring R] : Zero (AzPolynomial R) := ⟨zero⟩
instance {R : Type _} [Semiring R] [DecidableEq R] : One (AzPolynomial R) := ⟨one⟩

@[simp] lemma coeffs_zero {R : Type _} [Semiring R] : (0 : AzPolynomial R).coeffs = #[] := rfl

/-- The natural degree of a `AzPolynomial`. Expected behavior: 0 for the zero polynomial. -/
def natDegree {R : Type _} [Semiring R] (p : AzPolynomial R) : ℕ :=
  p.coeffs.size - 1

/-- The degree of a `AzPolynomial`, returning `WithBot ℕ`. Expected behavior: ⊥ for the zero polynomial. -/
def degree {R : Type _} [Semiring R] (p : AzPolynomial R) : WithBot ℕ :=
  if p.coeffs = #[] then ⊥ else ↑p.natDegree

/-- The `n`-th coefficient of the polynomial `p`. -/
def coeff {R : Type _} [Semiring R] (p : AzPolynomial R) (n : ℕ) : R :=
  (p.coeffs[n]?).getD 0

/-- The leading coefficient of the polynomial `p`. -/
def leadingCoeff {R : Type _} [Semiring R] (p : AzPolynomial R) : R :=
  p.coeff p.natDegree

/-- The second-highest coefficient, or 0 for constants. -/
def nextCoeff {R : Type _} [Semiring R] (p : AzPolynomial R) : R :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)

/-- A polynomial is `Monic` if its leading coefficient is 1. -/
def Monic {R : Type _} [Semiring R] (p : AzPolynomial R) :=
  p.leadingCoeff = (1 : R)

theorem Monic.def {R : Type _} [Semiring R] {p : AzPolynomial R} : p.Monic ↔ p.leadingCoeff = 1 :=
  Iff.rfl

instance Monic.decidable {R : Type _} [Semiring R] [DecidableEq R] {p : AzPolynomial R} : Decidable p.Monic := by unfold Monic; infer_instance

@[simp]
theorem Monic.leadingCoeff_eq_one {R : Type _} [Semiring R] {p : AzPolynomial R} (hp : p.Monic) : p.leadingCoeff = 1 :=
  hp

theorem Monic.coeff_natDegree {R : Type _} [Semiring R] {p : AzPolynomial R} (hp : p.Monic) : p.coeff p.natDegree = 1 :=
  hp

variable {S : Type _} [Semiring S] [DecidableEq S]

/-- `map f p` maps a polynomial `p` across a ring hom `f`. -/
def map {R : Type _} [Semiring R] (f : R →+* S) (p : AzPolynomial R) : AzPolynomial S :=
  normalize (p.coeffs.map f)

lemma Array_back?_map {α β : Type _} (a : Array α) (f : α → β) :
  (a.map f).back? = a.back?.map f := by
  dsimp [Array.back?]
  by_cases h : a.size = 0
  · have h1 : (a.map f).size = 0 := by simp [h]
    simp [h, h1]
  · have h1 : (a.map f).size = a.size := by simp
    have h2 : (a.map f).size - 1 = a.size - 1 := by omega
    rw [h1]
    rw [Array.getElem?_map]

/-- A powerful general-purpose map that skips normalization if the mapping function preserves zeros strictly (i.e., `f r = 0 ↔ r = 0`). -/
def mapZeroInjective {α β : Type _} [Semiring α] [Semiring β] (f : α → β) (hfinj : ∀ r, f r = 0 ↔ r = 0) (p : AzPolynomial α) : AzPolynomial β :=
  let arr := p.coeffs.map f
  ⟨arr, by
    intro h
    have h_back : arr.back? = p.coeffs.back?.map f := by
      exact Array_back?_map p.coeffs f
    rw [h_back] at h
    rcases hp : p.coeffs.back? with _ | r
    · simp [hp] at h
    · simp [hp] at h
      have hr0 : r = 0 := (hfinj r).mp (by rw [h])
      have hp2 : p.coeffs.back? = some 0 := by rw [hp, hr0]
      exact p.last_ne_zero hp2
  ⟩

/-- RingHom map skipping normalization. -/
def mapInjective {R S : Type _} [Semiring R] [Semiring S] (f : R →+* S) (hf : Function.Injective f) (p : AzPolynomial R) : AzPolynomial S :=
  mapZeroInjective f (fun r => ⟨fun hr => hf (by rw [hr, f.map_zero]), fun hr => by rw [hr, f.map_zero]⟩) p

/-- Maps a polynomial across `algebraMap R S`. Skips normalization if the `algebraMap` is injective. -/
def mapAlgebraMap {R S : Type _} [CommSemiring R] [Semiring S] [Algebra R S]
  (hf : Function.Injective (algebraMap R S)) (p : AzPolynomial R) : AzPolynomial S :=
  mapInjective (algebraMap R S) hf p

end Azurite.AzPolynomial
