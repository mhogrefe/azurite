/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Generic equivalence proof for `mergeSorted`.

  Shows that `mergeSorted f hf` preserves the MvPolynomial semantics.
-/
import Azurite.AzMvPolynomial.MergeSorted
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- `mergeSorted f hf` preserves the MvPolynomial sum. -/
theorem toMvPoly_mergeSorted
    (f : R → R) (hf : ∀ x, x ≠ 0 → f x ≠ 0)
    (ps qs : List (Monomial n R ord)) :
    ((mergeSorted f hf ps qs).map Monomial.toMvPoly).sum =
    (ps.map Monomial.toMvPoly).sum +
    (qs.map (fun q => MvPolynomial.monomial q.monic.toFinsupp (f q.coeff.val))).sum := by
  match ps, qs with
  | [], [] => simp [mergeSorted]
  | [], q :: qs' =>
    unfold mergeSorted
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
    rw [toMvPoly_mergeSorted f hf [] qs']
    simp only [List.map_nil, List.sum_nil, zero_add, Monomial.toMvPoly]
  | p :: ps', [] =>
    simp only [mergeSorted, List.map_nil, List.sum_nil, add_zero]
  | p :: ps', q :: qs' =>
    unfold mergeSorted
    split_ifs with hpq hqp hc
    · -- p > q: emit p
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_mergeSorted f hf ps' (q :: qs')]
      simp only [List.map_cons, List.sum_cons]; abel
    · -- q > p: emit f(q)
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_mergeSorted f hf (p :: ps') qs']
      simp only [List.map_cons, List.sum_cons, Monomial.toMvPoly]; abel
    · -- equal monics, zero sum: terms cancel
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_mergeSorted f hf ps' qs']
      have heq : p.monic = q.monic :=
        le_antisymm (not_lt.mp hpq) (not_lt.mp hqp)
      have hcancel : p.toMvPoly +
          MvPolynomial.monomial q.monic.toFinsupp (f q.coeff.val) = 0 := by
        simp only [Monomial.toMvPoly, heq]
        rw [← map_add (MvPolynomial.monomial q.monic.toFinsupp), hc,
            MvPolynomial.monomial_zero]
      have hrearrange :
          p.toMvPoly + (ps'.map Monomial.toMvPoly).sum +
          (monomial q.monic.toFinsupp (f q.coeff.val) +
            (qs'.map (fun q => monomial q.monic.toFinsupp (f q.coeff.val))).sum) =
          (p.toMvPoly + monomial q.monic.toFinsupp (f q.coeff.val)) +
          ((ps'.map Monomial.toMvPoly).sum +
            (qs'.map (fun q => monomial q.monic.toFinsupp (f q.coeff.val))).sum) := by
        abel
      rw [hrearrange, hcancel, zero_add]
    · -- equal monics, nonzero sum: emit combined monomial
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_mergeSorted f hf ps' qs']
      have heq : p.monic = q.monic :=
        le_antisymm (not_lt.mp hpq) (not_lt.mp hqp)
      have hcomb :
          (⟨⟨p.coeff.val + f q.coeff.val, hc⟩, p.monic⟩ : Monomial n R ord).toMvPoly =
          p.toMvPoly + monomial q.monic.toFinsupp (f q.coeff.val) := by
        simp only [Monomial.toMvPoly, heq]
        exact map_add (monomial q.monic.toFinsupp) (p.coeff : R) (f q.coeff.val)
      rw [hcomb]; abel
termination_by ps.length + qs.length

end Azurite
