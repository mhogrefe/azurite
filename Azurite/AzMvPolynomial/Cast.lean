/-
  Cast functions for AzMvPolynomial.
  Analogous to the casts in AzPolynomial/Cast.lean.
-/
import Azurite.AzMvPolynomial.Map
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- Lifts an `AzMvPolynomial σ ℕ` to `AzMvPolynomial σ ℤ`. -/
def AzMvPolynomial.mapNatToInt (p : AzMvPolynomial σ ℕ ord) :
    AzMvPolynomial σ ℤ ord :=
  AzMvPolynomial.mapAlgebraMap (by intro x y h; exact Nat.cast_inj.mp h) p

/-- Lifts an `AzMvPolynomial σ ℤ` to `AzMvPolynomial σ ℚ`. -/
def AzMvPolynomial.mapIntToRat (p : AzMvPolynomial σ ℤ ord) :
    AzMvPolynomial σ ℚ ord :=
  AzMvPolynomial.mapAlgebraMap (by intro x y h; exact Int.cast_inj.mp h) p

/-- Maps an `AzMvPolynomial σ (ZMod n)` to `AzMvPolynomial σ ℕ`.
    Uses `ZMod.val` which preserves zeros strictly. -/
def AzMvPolynomial.mapZModToNat {n' : ℕ} [NeZero n']
    (p : AzMvPolynomial σ (ZMod n') ord) :
    AzMvPolynomial σ ℕ ord :=
  AzMvPolynomial.mapZeroInjective ZMod.val (fun r => ⟨fun hr => by
    have h1 : (r.val : ZMod n') = (0 : ZMod n') := by rw [hr, Nat.cast_zero]
    have h2 : (r.val : ZMod n') = r := ZMod.natCast_zmod_val r
    rw [h2] at h1; exact h1,
    fun hr => by rw [hr, ZMod.val_zero]⟩) p

/-- Maps an `AzMvPolynomial σ ℕ` to `AzMvPolynomial σ (ZMod n)`.
    Performs filtering since elements can vanish modulo `n`. -/
def AzMvPolynomial.mapNatToZMod {n' : ℕ} [NeZero n']
    (p : AzMvPolynomial σ ℕ ord) :
    AzMvPolynomial σ (ZMod n') ord :=
  AzMvPolynomial.map (Nat.castRingHom (ZMod n')) p

/-- Maps an `AzMvPolynomial σ ℤ` to `AzMvPolynomial σ (ZMod n)`.
    Performs filtering since elements can vanish modulo `n`. -/
def AzMvPolynomial.mapIntToZMod {n' : ℕ} [NeZero n']
    (p : AzMvPolynomial σ ℤ ord) :
    AzMvPolynomial σ (ZMod n') ord :=
  AzMvPolynomial.map (Int.castRingHom (ZMod n')) p

end Azurite
