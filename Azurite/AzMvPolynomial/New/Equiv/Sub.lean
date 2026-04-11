/-
  Equivalence proofs for `AzMvPolynomialNew` subtraction.
-/
import Azurite.AzMvPolynomial.New.Sub
import Azurite.AzMvPolynomial.New.Equiv.MergeSorted

namespace Azurite
open AzMvPolynomialNew MvPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [DecidableEq R] in
private theorem neg_preserves_new : ∀ (x : R), x ≠ 0 → -x ≠ 0 :=
  fun _ h => neg_ne_zero.mpr h

/-- Subtraction commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_sub_new (p q : AzMvPolynomialNew n R ord) :
    (p - q).toMvPoly = p.toMvPoly - q.toMvPoly := by
  have h1 : (p - q).toMvPoly =
      ((mergeSortedNew Neg.neg neg_preserves_new p.terms.toList q.terms.toList).map
        MonomialNew.toMvPoly).sum := by
    show (AzMvPolynomialNew.sub p q).toMvPoly = _
    simp only [AzMvPolynomialNew.toMvPoly, AzMvPolynomialNew.sub]
    rw [← Array.foldl_toList, foldl_add_map_eq_sum_new, List.toList_toArray]
  rw [h1, toMvPoly_mergeSortedNew,
      AzMvPolynomialNew.toMvPoly_eq_list_sum p, AzMvPolynomialNew.toMvPoly_eq_list_sum q]
  rw [sub_eq_add_neg]; congr 1
  -- Show: sum(qs.map (monomial · (-·))) = -(sum(qs.map toMvPoly))
  have hmap : ∀ (l : List (MonomialNew n R ord)),
      (l.map (fun t => MvPolynomial.monomial t.monic.toFinsupp (Neg.neg t.coeff.val))).sum =
      -(l.map MonomialNew.toMvPoly).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih, neg_add]
      congr 1
      simp only [MonomialNew.toMvPoly, MvPolynomial.monomial]
      exact Finsupp.single_neg a.monic.toFinsupp a.coeff.val
  exact hmap q.terms.toList

/-- Subtraction commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_sub_new (p q : MvPolynomial (Fin n) R) :
    (AzMvPolynomialNew.ofMvPoly (p - q) : AzMvPolynomialNew n R ord) =
      AzMvPolynomialNew.ofMvPoly p - AzMvPolynomialNew.ofMvPoly q := by
  set a := AzMvPolynomialNew.ofMvPoly (ord := ord) p
  set b := AzMvPolynomialNew.ofMvPoly (ord := ord) q
  have hp : a.toMvPoly = p := toMvPoly_ofMvPoly_new p
  have hq : b.toMvPoly = q := toMvPoly_ofMvPoly_new q
  rw [← hp, ← hq, ← toMvPoly_sub_new a b]
  exact ofMvPoly_toMvPoly_new (a - b)

end Azurite
