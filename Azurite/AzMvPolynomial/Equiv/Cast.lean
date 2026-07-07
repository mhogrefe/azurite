/-
  Equivalence proofs for `AzMvPolynomial` cast functions.

  The previous Mathlib-bridge theorems (`toMvPoly_mapNatToInt`, …) related the
  cast functions to `MvPolynomial.map (algebraMap ℕ ℤ)` etc. over the GMP-backed
  `ℕ`/`ℤ`/`ℚ`/`ZMod` coefficient types.  Those coefficient types are no longer
  used (the casts now operate between the Az types `AzNat`/`AzInt`/`AzRat`/`AzZMod`
  in `AzMvPolynomial/Cast.lean`), so the bridge theorems have been removed.
-/
import Azurite.AzMvPolynomial.Cast
import Azurite.AzMvPolynomial.Equiv.Map
import Azurite.AzInt.Equiv.RingEquiv
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Add
import Azurite.AzRat.Equiv.Mul
import Azurite.AzRat.Equiv.RingEquiv

namespace Azurite

open MvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- The `AzInt → AzRat` coefficient embedding, bundled as a ring hom (its
underlying function is `AzInt.toAzRat`). -/
def AzInt.toAzRatRingHom : AzInt →+* AzRat where
  toFun := AzInt.toAzRat
  map_one' := by
    apply AzRat.toRat_injective
    rw [AzRat.toRat_toAzRat_int, AzRat.toRat_one,
      show (1 : AzInt).toInt = 1 from map_one AzInt.ringEquivInt]; norm_num
  map_mul' a b := by
    apply AzRat.toRat_injective
    rw [AzRat.toRat_mul, AzRat.toRat_toAzRat_int, AzRat.toRat_toAzRat_int,
      AzRat.toRat_toAzRat_int, AzInt.toInt_mul]; push_cast; ring
  map_zero' := by
    apply AzRat.toRat_injective
    rw [AzRat.toRat_toAzRat_int, AzRat.toRat_zero,
      show (0 : AzInt).toInt = 0 from map_zero AzInt.ringEquivInt]; norm_num
  map_add' a b := by
    apply AzRat.toRat_injective
    rw [AzRat.toRat_add, AzRat.toRat_toAzRat_int, AzRat.toRat_toAzRat_int,
      AzRat.toRat_toAzRat_int, AzInt.toInt_add]; push_cast; ring

@[simp] theorem AzInt.toAzRatRingHom_apply (z : AzInt) :
    AzInt.toAzRatRingHom z = z.toAzRat := rfl

theorem AzInt.toAzRatRingHom_injective : Function.Injective AzInt.toAzRatRingHom := by
  intro a b h
  apply AzInt.ringEquivInt.injective
  have : AzRat.toRat a.toAzRat = AzRat.toRat b.toAzRat := congrArg AzRat.toRat h
  rw [AzRat.toRat_toAzRat_int, AzRat.toRat_toAzRat_int] at this
  exact_mod_cast this

/-- `mapAzIntToAzRat` commutes with `toMvPoly`: on the Mathlib side it is
`MvPolynomial.map` of the `AzInt → AzRat` coefficient hom. -/
theorem AzMvPolynomial.toMvPoly_mapAzIntToAzRat (p : AzMvPolynomial n AzInt ord) :
    (p.mapAzIntToAzRat).toMvPoly = MvPolynomial.map AzInt.toAzRatRingHom p.toMvPoly := by
  rw [show p.mapAzIntToAzRat
      = p.mapInjective AzInt.toAzRatRingHom AzInt.toAzRatRingHom_injective from rfl]
  exact toMvPoly_mapInjective _ _ p

end Azurite
