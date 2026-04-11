/-
  Equivalence proofs for `AzMvPolynomial` addition.
-/
import Azurite.AzMvPolynomial.Add
import Azurite.AzMvPolynomial.Equiv.MergeSorted

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [DecidableEq R] in
private theorem id_preserves_equiv : ∀ (x : R), x ≠ 0 → id x ≠ 0 := fun _ h => h

/-- Addition commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_add (p q : AzMvPolynomial n R ord) :
    (p + q).toMvPoly = p.toMvPoly + q.toMvPoly := by
  have h1 : (p + q).toMvPoly =
      ((mergeSorted id id_preserves_equiv p.terms.toList q.terms.toList).map
        Monomial.toMvPoly).sum := by
    show (AzMvPolynomial.add p q).toMvPoly = _
    simp only [AzMvPolynomial.toMvPoly, AzMvPolynomial.add]
    rw [← Array.foldl_toList, foldl_add_map_eq_sum, List.toList_toArray]
  rw [h1, toMvPoly_mergeSorted,
      AzMvPolynomial.toMvPoly_eq_list_sum p, AzMvPolynomial.toMvPoly_eq_list_sum q]
  congr 1

/-- Addition commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_add (p q : MvPolynomial (Fin n) R) :
    (AzMvPolynomial.ofMvPoly (p + q) : AzMvPolynomial n R ord) =
      AzMvPolynomial.ofMvPoly p + AzMvPolynomial.ofMvPoly q := by
  set a := AzMvPolynomial.ofMvPoly (ord := ord) p
  set b := AzMvPolynomial.ofMvPoly (ord := ord) q
  have hp : a.toMvPoly = p := toMvPoly_ofMvPoly p
  have hq : b.toMvPoly = q := toMvPoly_ofMvPoly q
  rw [← hp, ← hq, ← toMvPoly_add a b]
  exact ofMvPoly_toMvPoly (a + b)

end Azurite
