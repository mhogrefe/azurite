/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for `AzMvPolynomial.mulNaive`.

  Mirrors the old `Equiv/MulNaive.lean`.  Proves `(p.mulNaive q).toMvPoly
  = p.toMvPoly * q.toMvPoly` so that `mul` delegating to `mulNaive` is
  automatically equivalent.
-/
import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Monomial-level multiplication -/

omit [DecidableEq R] in
/-- `toMvPoly` distributes over monomial multiplication. -/
theorem Monomial.toMvPoly_mul (a b : Monomial n R ord) :
    (a * b).toMvPoly = a.toMvPoly * b.toMvPoly := by
  show monomial (a.monic * b.monic).toFinsupp (a.coeff.val * b.coeff.val) =
    monomial a.monic.toFinsupp a.coeff.val * monomial b.monic.toFinsupp b.coeff.val
  rw [MvPolynomial.monomial_mul_monomial, MonicMonomial.toFinsupp_mul]

/-! ### Normalization preserves toMvPoly sum -/

omit [NoZeroDivisors R] in
/-- `combineSorted` preserves the `toMvPoly` sum. -/
theorem toMvPoly_combineSorted (l : List (Monomial n R ord)) :
    ((combineSorted l).map Monomial.toMvPoly).sum =
    (l.map Monomial.toMvPoly).sum := by
  induction l using combineSorted.induct with
  | case1 => simp [combineSorted]
  | case2 _ => simp [combineSorted]
  | case3 m₁ m₂ rest heq hcz ih =>
    simp only [combineSorted, ite_eq_left heq, dite_eq_left hcz, List.map_cons, List.sum_cons]; rw [ih]
    have : m₁.toMvPoly + m₂.toMvPoly = 0 := by
      simp only [Monomial.toMvPoly, heq]
      rw [← map_add (monomial m₂.monic.toFinsupp), hcz, monomial_zero]
    rw [← add_assoc, this, zero_add]
  | case4 m₁ m₂ rest heq hcnz ih =>
    simp only [combineSorted, ite_eq_left heq, dite_eq_right hcnz, List.map_cons, List.sum_cons]
    rw [ih, List.map_cons, List.sum_cons]
    have : (⟨⟨m₁.coeff.val + m₂.coeff.val, hcnz⟩, m₁.monic⟩ : Monomial n R ord).toMvPoly =
        m₁.toMvPoly + m₂.toMvPoly := by
      simp only [Monomial.toMvPoly, heq]
      exact map_add (monomial m₂.monic.toFinsupp) m₁.coeff.val m₂.coeff.val
    rw [this, add_assoc]
  | case5 _ _ _ hneq ih =>
    simp only [combineSorted, ite_eq_right hneq, List.map_cons, List.sum_cons]; congr 1

omit [NoZeroDivisors R] [DecidableEq R] in
/-- `sortDescending` preserves the `toMvPoly` sum (via permutation). -/
theorem toMvPoly_sortDescending (l : List (Monomial n R ord)) :
    ((sortDescending l).map Monomial.toMvPoly).sum =
    (l.map Monomial.toMvPoly).sum :=
  (List.mergeSort_perm l _).map Monomial.toMvPoly |>.sum_eq

omit [NoZeroDivisors R] in
/-- `normalizeMonomials` preserves the `toMvPoly` sum. -/
theorem toMvPoly_normalizeMonomials (l : List (Monomial n R ord)) :
    ((normalizeMonomials l).map Monomial.toMvPoly).sum =
    (l.map Monomial.toMvPoly).sum := by
  unfold normalizeMonomials
  rw [toMvPoly_combineSorted, toMvPoly_sortDescending]

/-! ### Distributive law for mulPairs -/

omit [DecidableEq R] in
/-- The `toMvPoly` sum of all pairwise products equals the product of the
    individual `toMvPoly` sums (distributivity). -/
theorem toMvPoly_mulPairs (ps qs : List (Monomial n R ord)) :
    ((mulPairs ps qs).map Monomial.toMvPoly).sum =
    (ps.map Monomial.toMvPoly).sum * (qs.map Monomial.toMvPoly).sum := by
  simp only [mulPairs, List.map_flatMap, List.map_map]
  induction ps with
  | nil => simp
  | cons p ps' ih =>
    simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, add_mul]
    rw [ih]; congr 1
    conv_lhs => rw [show (Monomial.toMvPoly ∘ fun q => p * q) =
      (fun q : Monomial n R ord => p.toMvPoly * q.toMvPoly) from
      funext (fun q => Monomial.toMvPoly_mul p q)]
    rw [← List.sum_map_mul_left]

/-! ### Full mulNaive equivalence -/

/-- `mulNaive` correctly computes the `MvPolynomial` product. -/
theorem toMvPoly_mulNaive (p q : AzMvPolynomial n R ord) :
    (p.mulNaive q).toMvPoly = p.toMvPoly * q.toMvPoly := by
  rw [AzMvPolynomial.toMvPoly_eq_list_sum (p.mulNaive q)]
  simp only [AzMvPolynomial.mulNaive, List.toList_toArray]
  rw [toMvPoly_normalizeMonomials, toMvPoly_mulPairs,
      ← AzMvPolynomial.toMvPoly_eq_list_sum p,
      ← AzMvPolynomial.toMvPoly_eq_list_sum q]

end Azurite
