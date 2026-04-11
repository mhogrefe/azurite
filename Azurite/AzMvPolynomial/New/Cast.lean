/-
  Cast functions for `AzMvPolynomialNew`.
-/
import Azurite.AzMvPolynomial.New.Map
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite

variable {n : ℕ} {ord : MonomialOrder}

/-- Lifts an `AzMvPolynomialNew n ℕ` to `AzMvPolynomialNew n ℤ`. -/
def AzMvPolynomialNew.mapNatToInt (p : AzMvPolynomialNew n ℕ ord) :
    AzMvPolynomialNew n ℤ ord :=
  AzMvPolynomialNew.mapAlgebraMap (by intro x y h; exact Nat.cast_inj.mp h) p

/-- Lifts an `AzMvPolynomialNew n ℤ` to `AzMvPolynomialNew n ℚ`. -/
def AzMvPolynomialNew.mapIntToRat (p : AzMvPolynomialNew n ℤ ord) :
    AzMvPolynomialNew n ℚ ord :=
  AzMvPolynomialNew.mapAlgebraMap (by intro x y h; exact Int.cast_inj.mp h) p

/-- Maps an `AzMvPolynomialNew n (ZMod n')` to `AzMvPolynomialNew n ℕ`. -/
def AzMvPolynomialNew.mapZModToNat {n' : ℕ} [NeZero n']
    (p : AzMvPolynomialNew n (ZMod n') ord) :
    AzMvPolynomialNew n ℕ ord :=
  AzMvPolynomialNew.mapZeroInjective ZMod.val (fun r => ⟨fun hr => by
    have h1 : (r.val : ZMod n') = (0 : ZMod n') := by rw [hr, Nat.cast_zero]
    have h2 : (r.val : ZMod n') = r := ZMod.natCast_zmod_val r
    rw [h2] at h1; exact h1,
    fun hr => by rw [hr, ZMod.val_zero]⟩) p

/-- Maps an `AzMvPolynomialNew n ℕ` to `AzMvPolynomialNew n (ZMod n')`. -/
def AzMvPolynomialNew.mapNatToZMod {n' : ℕ} [NeZero n']
    (p : AzMvPolynomialNew n ℕ ord) :
    AzMvPolynomialNew n (ZMod n') ord :=
  AzMvPolynomialNew.map (Nat.castRingHom (ZMod n')) p

/-- Maps an `AzMvPolynomialNew n ℤ` to `AzMvPolynomialNew n (ZMod n')`. -/
def AzMvPolynomialNew.mapIntToZMod {n' : ℕ} [NeZero n']
    (p : AzMvPolynomialNew n ℤ ord) :
    AzMvPolynomialNew n (ZMod n') ord :=
  AzMvPolynomialNew.map (Int.castRingHom (ZMod n')) p

end Azurite
