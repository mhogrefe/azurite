/-
  Cast functions for `AzMvPolynomial`.
-/
import Azurite.AzMvPolynomial.Map
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite

variable {n : ℕ} {ord : MonomialOrder}

/-- Lifts an `AzMvPolynomial n ℕ` to `AzMvPolynomial n ℤ`. -/
def AzMvPolynomial.mapNatToInt (p : AzMvPolynomial n ℕ ord) :
    AzMvPolynomial n ℤ ord :=
  AzMvPolynomial.mapAlgebraMap (by intro x y h; exact Nat.cast_inj.mp h) p

/-- Lifts an `AzMvPolynomial n ℤ` to `AzMvPolynomial n ℚ`. -/
def AzMvPolynomial.mapIntToRat (p : AzMvPolynomial n ℤ ord) :
    AzMvPolynomial n ℚ ord :=
  AzMvPolynomial.mapAlgebraMap (by intro x y h; exact Int.cast_inj.mp h) p

/-- Maps an `AzMvPolynomial n (ZMod n')` to `AzMvPolynomial n ℕ`. -/
def AzMvPolynomial.mapZModToNat {n' : ℕ} [NeZero n']
    (p : AzMvPolynomial n (ZMod n') ord) :
    AzMvPolynomial n ℕ ord :=
  AzMvPolynomial.mapZeroInjective ZMod.val (fun r => ⟨fun hr => by
    have h1 : (r.val : ZMod n') = (0 : ZMod n') := by rw [hr, Nat.cast_zero]
    have h2 : (r.val : ZMod n') = r := ZMod.natCast_zmod_val r
    rw [h2] at h1; exact h1,
    fun hr => by rw [hr, ZMod.val_zero]⟩) p

/-- Maps an `AzMvPolynomial n ℕ` to `AzMvPolynomial n (ZMod n')`. -/
def AzMvPolynomial.mapNatToZMod {n' : ℕ} [NeZero n']
    (p : AzMvPolynomial n ℕ ord) :
    AzMvPolynomial n (ZMod n') ord :=
  AzMvPolynomial.map (Nat.castRingHom (ZMod n')) p

/-- Maps an `AzMvPolynomial n ℤ` to `AzMvPolynomial n (ZMod n')`. -/
def AzMvPolynomial.mapIntToZMod {n' : ℕ} [NeZero n']
    (p : AzMvPolynomial n ℤ ord) :
    AzMvPolynomial n (ZMod n') ord :=
  AzMvPolynomial.map (Int.castRingHom (ZMod n')) p

end Azurite
