/-
  Equivalence proofs for AzMvPolynomial cast functions.
-/
import Azurite.AzMvPolynomial.Cast
import Azurite.AzMvPolynomial.Equiv.Map

namespace Azurite
open MvPolynomial

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

@[simp] theorem toMvPoly_mapNatToInt
    (p : AzMvPolynomial σ ℕ ord) :
    (p.mapNatToInt).toMvPoly =
      MvPolynomial.map (algebraMap ℕ ℤ) p.toMvPoly := by
  exact toMvPoly_mapAlgebraMap _ p

@[simp] theorem toMvPoly_mapIntToRat
    (p : AzMvPolynomial σ ℤ ord) :
    (p.mapIntToRat).toMvPoly =
      MvPolynomial.map (algebraMap ℤ ℚ) p.toMvPoly := by
  exact toMvPoly_mapAlgebraMap _ p

@[simp] theorem toMvPoly_mapNatToZMod {n' : ℕ} [NeZero n']
    (p : AzMvPolynomial σ ℕ ord) :
    (p.mapNatToZMod).toMvPoly =
      MvPolynomial.map (Nat.castRingHom (ZMod n')) p.toMvPoly := by
  exact toMvPoly_map _ p

@[simp] theorem toMvPoly_mapIntToZMod {n' : ℕ} [NeZero n']
    (p : AzMvPolynomial σ ℤ ord) :
    (p.mapIntToZMod).toMvPoly =
      MvPolynomial.map (Int.castRingHom (ZMod n')) p.toMvPoly := by
  exact toMvPoly_map _ p

end Azurite
