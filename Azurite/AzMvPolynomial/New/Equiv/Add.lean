/-
  Equivalence proofs for `AzMvPolynomialNew` addition.
-/
import Azurite.AzMvPolynomial.New.Add
import Azurite.AzMvPolynomial.New.Equiv.MergeSorted

namespace Azurite
open AzMvPolynomialNew MvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [DecidableEq R] in
private theorem id_preserves_new_equiv : ∀ (x : R), x ≠ 0 → id x ≠ 0 := fun _ h => h

/-- Addition commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_add_new (p q : AzMvPolynomialNew n R ord) :
    (p + q).toMvPoly = p.toMvPoly + q.toMvPoly := by
  have h1 : (p + q).toMvPoly =
      ((mergeSortedNew id id_preserves_new_equiv p.terms.toList q.terms.toList).map
        MonomialNew.toMvPoly).sum := by
    show (AzMvPolynomialNew.add p q).toMvPoly = _
    simp only [AzMvPolynomialNew.toMvPoly, AzMvPolynomialNew.add]
    rw [← Array.foldl_toList, foldl_add_map_eq_sum_new, List.toList_toArray]
  rw [h1, toMvPoly_mergeSortedNew,
      AzMvPolynomialNew.toMvPoly_eq_list_sum p, AzMvPolynomialNew.toMvPoly_eq_list_sum q]
  congr 1

/-- Addition commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_add_new (p q : MvPolynomial (Fin n) R) :
    (AzMvPolynomialNew.ofMvPoly (p + q) : AzMvPolynomialNew n R ord) =
      AzMvPolynomialNew.ofMvPoly p + AzMvPolynomialNew.ofMvPoly q := by
  set a := AzMvPolynomialNew.ofMvPoly (ord := ord) p
  set b := AzMvPolynomialNew.ofMvPoly (ord := ord) q
  have hp : a.toMvPoly = p := toMvPoly_ofMvPoly_new p
  have hq : b.toMvPoly = q := toMvPoly_ofMvPoly_new q
  rw [← hp, ← hq, ← toMvPoly_add_new a b]
  exact ofMvPoly_toMvPoly_new (a + b)

end Azurite
