/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter10.Section10_1.NormLengthMeasure

/-!
# BPR Lemma 10.10: exchanging a root for its inverse conjugate preserves the norm

`lemma_10_10`: `∥(X − α)·P∥ = ∥(ᾱX − 1)·P∥`. BPR's proof computes both
squared norms coefficientwise and finds the same value
`(1 + |α|²)∥P∥² − ∑ⱼ(α aⱼ āⱼ₋₁ + ᾱ āⱼ aⱼ₋₁)`.

The formalization takes an equivalent route that avoids the cross terms
entirely: writing the coefficients of the two products uniformly as
`x − α·y` and `ᾱ·x − y` with `x = (X·P).coeff j`, `y = P.coeff j`
(no `j = 0` case split needed), the pointwise identity

  `|x − αy|² − |ᾱx − y|² = (1 − |α|²)(|x|² − |y|²)`

(`Ri.normSqR_sub_mul_identity`, a `ring` identity after expanding
`normSq z = z·z̄` through the conjugation homomorphism) reduces the
difference of the squared norms to
`(1 − |α|²)·(∑ⱼ |(X·P)ⱼ|² − ∑ⱼ |Pⱼ|²)`, which vanishes because
multiplication by `X` merely shifts the coefficient multiset.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Pointwise identity behind Lemma 10.10:
`|x − αy|² − |ᾱx − y|² = (1 − |α|²)(|x|² − |y|²)`. -/
theorem Ri.normSqR_sub_mul_identity (α x y : Ri R) :
    Ri.normSqR (x - α * y) - Ri.normSqR (Ri.conj R α * x - y)
      = (1 - Ri.normSqR α) * (Ri.normSqR x - Ri.normSqR y) := by
  apply FaithfulSMul.algebraMap_injective R (Ri R)
  rw [map_sub, map_mul, map_sub, map_sub, map_one]
  rw [Ri.normSqR_spec, Ri.normSqR_spec, Ri.normSqR_spec, Ri.normSqR_spec, Ri.normSqR_spec]
  show (x - α * y) * (Ri.conj R) (x - α * y)
      - (Ri.conj R α * x - y) * (Ri.conj R) (Ri.conj R α * x - y)
      = (1 - α * (Ri.conj R) α) * (x * (Ri.conj R) x - y * (Ri.conj R) y)
  rw [map_sub, map_mul, map_sub, map_mul, Ri.conj_conj]
  ring

set_option maxHeartbeats 1000000 in
omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **BPR Lemma 10.10, squared form.**
`∥(X − α)·P∥² = ∥(ᾱX − 1)·P∥²`. -/
theorem lemma_10_10_normSq (α : Ri R) (P : Polynomial (Ri R)) :
    polyNormSq ((X - C α) * P) = polyNormSq ((C (Ri.conj R α) * X - 1) * P) := by
  set p := P.natDegree with hp
  -- both products have degree below p + 2
  have hd1 : ((X - C α) * P).natDegree < p + 2 := by
    have h1 := Polynomial.natDegree_mul_le (p := X - C α) (q := P)
    have h2 : (X - C α : (Ri R)[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C α
    omega
  have hd2 : ((C (Ri.conj R α) * X - 1) * P).natDegree < p + 2 := by
    have h1 := Polynomial.natDegree_mul_le (p := C (Ri.conj R α) * X - 1) (q := P)
    have h2 : (C (Ri.conj R α) * X - 1 : (Ri R)[X]).natDegree ≤ 1 := by
      apply le_trans (Polynomial.natDegree_sub_le _ _)
      have h3 : (C (Ri.conj R α) * X : (Ri R)[X]).natDegree ≤ 1 := by
        apply le_trans (Polynomial.natDegree_C_mul_le _ _)
        rw [Polynomial.natDegree_X]
      simp only [Polynomial.natDegree_one]
      omega
    omega
  -- the coefficients of the two products, uniformly in `j`
  have hco1 : ∀ j, ((X - C α) * P).coeff j = (X * P).coeff j - α * P.coeff j := by
    intro j
    rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  have hco2 : ∀ j, ((C (Ri.conj R α) * X - 1) * P).coeff j
      = Ri.conj R α * (X * P).coeff j - P.coeff j := by
    intro j
    rw [sub_mul, one_mul, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul]
  -- the pointwise identity collapses the difference of the squared norms
  have hstep1 : ∑ j ∈ Finset.range (p + 2), Ri.normSqR (((X - C α) * P).coeff j)
      - ∑ j ∈ Finset.range (p + 2), Ri.normSqR (((C (Ri.conj R α) * X - 1) * P).coeff j)
      = (1 - Ri.normSqR α) * ∑ j ∈ Finset.range (p + 2),
          (Ri.normSqR ((X * P).coeff j) - Ri.normSqR (P.coeff j)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hco1 j, hco2 j, Ri.normSqR_sub_mul_identity]
  -- multiplication by `X` shifts the coefficient multiset
  have hsucc' : ∀ f : ℕ → R, ∑ j ∈ Finset.range (p + 2), f j
      = (∑ i ∈ Finset.range (p + 1), f (i + 1)) + f 0 :=
    fun f => Finset.sum_range_succ' f (p + 1)
  have hsucc : ∀ f : ℕ → R, ∑ j ∈ Finset.range (p + 2), f j
      = (∑ i ∈ Finset.range (p + 1), f i) + f (p + 1) :=
    fun f => Finset.sum_range_succ f (p + 1)
  have hXP0 : ((X * P : (Ri R)[X])).coeff 0 = 0 := by
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
  have hXP : ∑ j ∈ Finset.range (p + 2), Ri.normSqR ((X * P).coeff j)
      = ∑ j ∈ Finset.range (p + 2), Ri.normSqR (P.coeff j) := by
    rw [hsucc', hsucc, hXP0, Ri.normSqR_zero, add_zero,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < p + 1),
      Ri.normSqR_zero, add_zero]
    exact Finset.sum_congr rfl (fun i _ => by rw [Polynomial.coeff_X_mul])
  have hzero : ∑ j ∈ Finset.range (p + 2),
      (Ri.normSqR ((X * P).coeff j) - Ri.normSqR (P.coeff j)) = 0 := by
    rw [Finset.sum_sub_distrib, hXP, sub_self]
  rw [polyNormSq_eq_sum _ hd1, polyNormSq_eq_sum _ hd2, ← sub_eq_zero, hstep1, hzero,
    mul_zero]

/-- **BPR Lemma 10.10.** `∥(X − α)·P∥ = ∥(ᾱX − 1)·P∥`. -/
theorem lemma_10_10 (α : Ri R) (P : Polynomial (Ri R)) :
    polyNorm ((X - C α) * P) = polyNorm ((C (Ri.conj R α) * X - 1) * P) := by
  rw [polyNorm, polyNorm, lemma_10_10_normSq]

end Azurite.BPR
