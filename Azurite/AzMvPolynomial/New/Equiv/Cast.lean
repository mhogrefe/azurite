/-
  Equivalence proofs for `AzMvPolynomialNew` cast functions.
-/
import Azurite.AzMvPolynomial.New.Cast
import Azurite.AzMvPolynomial.New.Equiv.Map

namespace Azurite
open MvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

@[simp] theorem toMvPoly_mapNatToInt_new
    (p : AzMvPolynomialNew n ℕ ord) :
    (p.mapNatToInt).toMvPoly =
      MvPolynomial.map (algebraMap ℕ ℤ) p.toMvPoly := by
  exact toMvPoly_mapAlgebraMap_new _ p

@[simp] theorem toMvPoly_mapIntToRat_new
    (p : AzMvPolynomialNew n ℤ ord) :
    (p.mapIntToRat).toMvPoly =
      MvPolynomial.map (algebraMap ℤ ℚ) p.toMvPoly := by
  exact toMvPoly_mapAlgebraMap_new _ p

@[simp] theorem toMvPoly_mapNatToZMod_new {n' : ℕ} [NeZero n']
    (p : AzMvPolynomialNew n ℕ ord) :
    (p.mapNatToZMod (n' := n')).toMvPoly =
      MvPolynomial.map (Nat.castRingHom (ZMod n')) p.toMvPoly := by
  exact toMvPoly_map_new _ p

@[simp] theorem toMvPoly_mapIntToZMod_new {n' : ℕ} [NeZero n']
    (p : AzMvPolynomialNew n ℤ ord) :
    (p.mapIntToZMod (n' := n')).toMvPoly =
      MvPolynomial.map (Int.castRingHom (ZMod n')) p.toMvPoly := by
  exact toMvPoly_map_new _ p

end Azurite
