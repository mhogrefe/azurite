/-
  Equivalence proof for `AzMvPolynomialNew` negation.
-/
import Azurite.AzMvPolynomial.New.Neg
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Azurite
open AzMvPolynomialNew MvPolynomial

variable {R : Type _} [CommRing R]
         {n : ℕ} {ord : MonomialOrder}

/-- Negation commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_neg_new (p : AzMvPolynomialNew n R ord) :
    (-p).toMvPoly = -p.toMvPoly := by
  show (mapZeroInjective (fun x => -x) _ p).toMvPoly = -p.toMvPoly
  simp only [AzMvPolynomialNew.toMvPoly_eq_list_sum, mapZeroInjective,
             Array.toList_map, List.map_map, List.sum_neg]
  congr 1
  show List.map (MonomialNew.toMvPoly ∘ mapCoeffNew (fun x => -x) _) p.terms.toList =
       List.map (Neg.neg ∘ MonomialNew.toMvPoly) p.terms.toList
  congr 1; ext m : 1
  show Finsupp.single m.monic.toFinsupp (-m.coeff.val) =
       -Finsupp.single m.monic.toFinsupp m.coeff.val
  exact Finsupp.single_neg m.monic.toFinsupp m.coeff.val

/-- Negation commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_neg_new (p : MvPolynomial (Fin n) R) :
    (AzMvPolynomialNew.ofMvPoly (-p) : AzMvPolynomialNew n R ord) =
      -AzMvPolynomialNew.ofMvPoly p := by
  set q := AzMvPolynomialNew.ofMvPoly (ord := ord) p
  have hp : q.toMvPoly = p := toMvPoly_ofMvPoly_new p
  rw [← hp, ← toMvPoly_neg_new q]
  exact ofMvPoly_toMvPoly_new (-q)

end Azurite
