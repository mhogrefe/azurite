import Azurite.AzPolynomial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite
namespace AzPolynomial

/-- Lifts a `AzPolynomial ℕ` to `AzPolynomial ℤ`. -/
def mapNatToInt (p : AzPolynomial ℕ) : AzPolynomial ℤ :=
  mapAlgebraMap (by intro x y h; exact Nat.cast_inj.mp h) p

/-- Lifts a `AzPolynomial ℤ` to `AzPolynomial ℚ`. -/
def mapIntToRat (p : AzPolynomial ℤ) : AzPolynomial ℚ :=
  mapAlgebraMap (by intro x y h; exact Int.cast_inj.mp h) p

/-- Maps a `AzPolynomial (ZMod n)` to `AzPolynomial ℕ`. -/
def mapZModToNat {n : ℕ} [NeZero n] (p : AzPolynomial (ZMod n)) : AzPolynomial ℕ :=
  mapZeroInjective ZMod.val (fun r => ⟨fun hr => by
    have h1 : (r.val : ZMod n) = (0 : ZMod n) := by rw [hr, Nat.cast_zero]
    have h2 : (r.val : ZMod n) = r := ZMod.natCast_zmod_val r
    rw [h2] at h1
    exact h1, fun hr => by rw [hr, ZMod.val_zero]⟩) p

/-- Maps a `AzPolynomial ℕ` to `AzPolynomial (ZMod n)`. Performs normalization since elements can vanish modulo `n`. -/
def mapNatToZMod {n : ℕ} [NeZero n] (p : AzPolynomial ℕ) : AzPolynomial (ZMod n) :=
  map (Nat.castRingHom (ZMod n)) p

/-- Maps a `AzPolynomial ℤ` to `AzPolynomial (ZMod n)`. Performs normalization since elements can vanish modulo `n`. -/
def mapIntToZMod {n : ℕ} [NeZero n] (p : AzPolynomial ℤ) : AzPolynomial (ZMod n) :=
  map (Int.castRingHom (ZMod n)) p

end AzPolynomial
end Azurite
