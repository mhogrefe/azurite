/-
  Generic equivalence proof for `mergeSortedNew`.

  Shows that `mergeSortedNew f hf` preserves the MvPolynomial semantics.
-/
import Azurite.AzMvPolynomial.New.MergeSorted
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Azurite
open AzMvPolynomialNew MvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- `mergeSortedNew f hf` preserves the MvPolynomial sum. -/
theorem toMvPoly_mergeSortedNew
    (f : R → R) (hf : ∀ x, x ≠ 0 → f x ≠ 0)
    (ps qs : List (MonomialNew n R ord)) :
    ((mergeSortedNew f hf ps qs).map MonomialNew.toMvPoly).sum =
    (ps.map MonomialNew.toMvPoly).sum +
    (qs.map (fun q => MvPolynomial.monomial q.monic.toFinsupp (f q.coeff.val))).sum := by
  match ps, qs with
  | [], [] => simp [mergeSortedNew]
  | [], q :: qs' =>
    unfold mergeSortedNew
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
    rw [toMvPoly_mergeSortedNew f hf [] qs']
    simp only [List.map_nil, List.sum_nil, zero_add, MonomialNew.toMvPoly]
  | p :: ps', [] =>
    simp only [mergeSortedNew, List.map_nil, List.sum_nil, add_zero]
  | p :: ps', q :: qs' =>
    unfold mergeSortedNew
    split_ifs with hpq hqp hc
    · -- p > q: emit p
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_mergeSortedNew f hf ps' (q :: qs')]
      simp only [List.map_cons, List.sum_cons]; abel
    · -- q > p: emit f(q)
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_mergeSortedNew f hf (p :: ps') qs']
      simp only [List.map_cons, List.sum_cons, MonomialNew.toMvPoly]; abel
    · -- equal monics, zero sum: terms cancel
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_mergeSortedNew f hf ps' qs']
      have heq : p.monic = q.monic :=
        le_antisymm (not_lt.mp hpq) (not_lt.mp hqp)
      have hcancel : p.toMvPoly +
          MvPolynomial.monomial q.monic.toFinsupp (f q.coeff.val) = 0 := by
        simp only [MonomialNew.toMvPoly, heq]
        rw [← map_add (MvPolynomial.monomial q.monic.toFinsupp), hc,
            MvPolynomial.monomial_zero]
      have hrearrange :
          p.toMvPoly + (ps'.map MonomialNew.toMvPoly).sum +
          (monomial q.monic.toFinsupp (f q.coeff.val) +
            (qs'.map (fun q => monomial q.monic.toFinsupp (f q.coeff.val))).sum) =
          (p.toMvPoly + monomial q.monic.toFinsupp (f q.coeff.val)) +
          ((ps'.map MonomialNew.toMvPoly).sum +
            (qs'.map (fun q => monomial q.monic.toFinsupp (f q.coeff.val))).sum) := by
        abel
      rw [hrearrange, hcancel, zero_add]
    · -- equal monics, nonzero sum: emit combined monomial
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_mergeSortedNew f hf ps' qs']
      have heq : p.monic = q.monic :=
        le_antisymm (not_lt.mp hpq) (not_lt.mp hqp)
      have hcomb :
          (⟨⟨p.coeff.val + f q.coeff.val, hc⟩, p.monic⟩ : MonomialNew n R ord).toMvPoly =
          p.toMvPoly + monomial q.monic.toFinsupp (f q.coeff.val) := by
        simp only [MonomialNew.toMvPoly, heq]
        exact map_add (monomial q.monic.toFinsupp) (p.coeff : R) (f q.coeff.val)
      rw [hcomb]; abel
termination_by ps.length + qs.length

end Azurite
