/-
  Equivalence proof for `AzMvPolynomial` negation.
-/
import Azurite.AzMvPolynomial.Neg
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommRing R]
         {n : ℕ} {ord : MonomialOrder}

/-- Negation commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_neg (p : AzMvPolynomial n R ord) :
    (-p).toMvPoly = -p.toMvPoly := by
  show (mapZeroInjective (fun x => -x) _ p).toMvPoly = -p.toMvPoly
  simp only [AzMvPolynomial.toMvPoly_eq_list_sum, mapZeroInjective,
             Array.toList_map, List.map_map, List.sum_neg]
  congr 1
  show List.map (Monomial.toMvPoly ∘ mapCoeff (fun x => -x) _) p.terms.toList =
       List.map (Neg.neg ∘ Monomial.toMvPoly) p.terms.toList
  congr 1; ext m : 1
  show (MvPolynomial.monomial m.monic.toFinsupp) (-m.coeff.val) =
       -(MvPolynomial.monomial m.monic.toFinsupp) m.coeff.val
  exact map_neg (MvPolynomial.monomial m.monic.toFinsupp) m.coeff.val

/-- Negation commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_neg (p : MvPolynomial (Fin n) R) :
    (AzMvPolynomial.ofMvPoly (-p) : AzMvPolynomial n R ord) =
      -AzMvPolynomial.ofMvPoly p := by
  set q := AzMvPolynomial.ofMvPoly (ord := ord) p
  have hp : q.toMvPoly = p := toMvPoly_ofMvPoly p
  rw [← hp, ← toMvPoly_neg q]
  exact ofMvPoly_toMvPoly (-q)

end Azurite
