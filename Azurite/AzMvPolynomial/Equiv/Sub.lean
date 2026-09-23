/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for `AzMvPolynomial` subtraction.
-/
import Azurite.AzMvPolynomial.Sub
import Azurite.AzMvPolynomial.Equiv.MergeSorted

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [DecidableEq R] in
private theorem neg_preserves : ∀ (x : R), x ≠ 0 → -x ≠ 0 :=
  fun _ h => neg_ne_zero.mpr h

/-- Subtraction commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_sub (p q : AzMvPolynomial n R ord) :
    (p - q).toMvPoly = p.toMvPoly - q.toMvPoly := by
  have h1 : (p - q).toMvPoly =
      ((mergeSorted Neg.neg neg_preserves p.terms.toList q.terms.toList).map
        Monomial.toMvPoly).sum := by
    show (AzMvPolynomial.sub p q).toMvPoly = _
    simp only [AzMvPolynomial.toMvPoly, AzMvPolynomial.sub]
    rw [← Array.foldl_toList, foldl_add_map_eq_sum, List.toList_toArray]
  rw [h1, toMvPoly_mergeSorted,
      AzMvPolynomial.toMvPoly_eq_list_sum p, AzMvPolynomial.toMvPoly_eq_list_sum q]
  rw [sub_eq_add_neg]; congr 1
  -- Show: sum(qs.map (monomial · (-·))) = -(sum(qs.map toMvPoly))
  have hmap : ∀ (l : List (Monomial n R ord)),
      (l.map (fun t => MvPolynomial.monomial t.monic.toFinsupp (Neg.neg t.coeff.val))).sum =
      -(l.map Monomial.toMvPoly).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih, neg_add]
      congr 1
      simp only [Monomial.toMvPoly]
      exact map_neg (MvPolynomial.monomial a.monic.toFinsupp) a.coeff.val
  exact hmap q.terms.toList

/-- Subtraction commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_sub (p q : MvPolynomial (Fin n) R) :
    (AzMvPolynomial.ofMvPoly (p - q) : AzMvPolynomial n R ord) =
      AzMvPolynomial.ofMvPoly p - AzMvPolynomial.ofMvPoly q := by
  set a := AzMvPolynomial.ofMvPoly (ord := ord) p
  set b := AzMvPolynomial.ofMvPoly (ord := ord) q
  have hp : a.toMvPoly = p := toMvPoly_ofMvPoly p
  have hq : b.toMvPoly = q := toMvPoly_ofMvPoly q
  rw [← hp, ← hq, ← toMvPoly_sub a b]
  exact ofMvPoly_toMvPoly (a - b)

end Azurite
