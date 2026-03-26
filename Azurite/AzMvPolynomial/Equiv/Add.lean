/-
  Equivalence proofs for AzMvPolynomial addition.
-/
import Azurite.AzMvPolynomial.Add
import Azurite.AzMvPolynomial.Equiv.MergeSorted

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

omit [DecidableEq R] in
private theorem id_preserves : ∀ (x : R), x ≠ 0 → id x ≠ 0 := fun _ h => h

/-- Addition commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_add (p q : AzMvPolynomial σ R ord) :
    (p + q).toMvPoly = p.toMvPoly + q.toMvPoly := by
  have h1 : (p + q).toMvPoly =
      ((mergeSorted id id_preserves p.terms.toList q.terms.toList).map
        Monomial.toMvPoly).sum := by
    show (AzMvPolynomial.add p q).toMvPoly = _
    simp only [AzMvPolynomial.toMvPoly, AzMvPolynomial.add]
    rw [← Array.foldl_toList, foldl_add_map_eq_sum, List.toList_toArray]
  rw [h1, toMvPoly_mergeSorted,
      AzMvPolynomial.toMvPoly_eq_list_sum p, AzMvPolynomial.toMvPoly_eq_list_sum q]
  -- RHS second sum: (qs.map (fun q => monomial q.monic.toFinsupp (id q.coeff.val)))
  -- = (qs.map (fun q => monomial q.monic.toFinsupp q.coeff.val))
  -- = (qs.map Monomial.toMvPoly)    by definition of toMvPoly
  congr 1

/-- Addition commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_add (p q : MvPolynomial σ R) :
    (AzMvPolynomial.ofMvPoly (p + q) : AzMvPolynomial σ R ord) =
      AzMvPolynomial.ofMvPoly p + AzMvPolynomial.ofMvPoly q := by
  set a := AzMvPolynomial.ofMvPoly (ord := ord) p
  set b := AzMvPolynomial.ofMvPoly (ord := ord) q
  have hp : a.toMvPoly = p := toMvPoly_ofMvPoly p
  have hq : b.toMvPoly = q := toMvPoly_ofMvPoly q
  rw [← hp, ← hq, ← toMvPoly_add a b]
  exact ofMvPoly_toMvPoly (a + b)

end Azurite
