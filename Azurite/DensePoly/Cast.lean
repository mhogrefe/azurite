import Azurite.DensePoly.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite
namespace DensePoly

/-- Lifts a `DensePoly ℕ` to `DensePoly ℤ`. -/
def mapNatToInt (p : DensePoly ℕ) : DensePoly ℤ :=
  mapAlgebraMap (by intro x y h; exact Nat.cast_inj.mp h) p

/-- Lifts a `DensePoly ℤ` to `DensePoly ℚ`. -/
def mapIntToRat (p : DensePoly ℤ) : DensePoly ℚ :=
  mapAlgebraMap (by intro x y h; exact Int.cast_inj.mp h) p

/-- Maps a `DensePoly (ZMod n)` to `DensePoly ℕ`. -/
def mapZModToNat {n : ℕ} [NeZero n] (p : DensePoly (ZMod n)) : DensePoly ℕ :=
  mapZeroInjective ZMod.val (fun r => ⟨fun hr => by
    have h1 : (r.val : ZMod n) = (0 : ZMod n) := by rw [hr, Nat.cast_zero]
    have h2 : (r.val : ZMod n) = r := ZMod.natCast_zmod_val r
    rw [h2] at h1
    exact h1, fun hr => by rw [hr, ZMod.val_zero]⟩) p

/-- Maps a `DensePoly ℕ` to `DensePoly (ZMod n)`. Performs normalization since elements can vanish modulo `n`. -/
def mapNatToZMod {n : ℕ} [NeZero n] (p : DensePoly ℕ) : DensePoly (ZMod n) :=
  map (Nat.castRingHom (ZMod n)) p

/-- Maps a `DensePoly ℤ` to `DensePoly (ZMod n)`. Performs normalization since elements can vanish modulo `n`. -/
def mapIntToZMod {n : ℕ} [NeZero n] (p : DensePoly ℤ) : DensePoly (ZMod n) :=
  map (Int.castRingHom (ZMod n)) p

end DensePoly
end Azurite
