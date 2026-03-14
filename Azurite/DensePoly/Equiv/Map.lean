import Azurite.DensePoly.Basic
import Azurite.DensePoly.Equiv.Basic
import Azurite.DensePoly.Cast
import Mathlib.Algebra.Polynomial.Basic

open Polynomial

variable {R S : Type _} [Semiring R] [Semiring S]

namespace Azurite
namespace DensePoly

lemma toPoly_map_list (f : R →+* S) (l : List R) :
  (l.map f).toPoly = (l.toPoly).map f := by
  induction l with
  | nil =>
    simp [List.toPoly]
  | cons a as ih =>
    simp [List.toPoly, ih, Polynomial.map_add, Polynomial.map_mul]

@[simp] lemma toPoly_map [DecidableEq S] (f : R →+* S) (p : DensePoly R) :
  DensePoly.toPoly (p.map f) = (DensePoly.toPoly p).map f := by
  dsimp [map]
  rw [_root_.toPoly_normalize]
  have h1 : (p.coeffs.map f).toList = p.coeffs.toList.map f := by simp
  rw [h1]
  exact toPoly_map_list f p.coeffs.toList

@[simp] lemma ofPoly_map [DecidableEq R] [DecidableEq S] (f : R →+* S) (p : Polynomial R) :
  DensePoly.ofPoly (p.map f) = (DensePoly.ofPoly p).map f := by
  apply equivPolynomial.injective
  change DensePoly.toPoly (DensePoly.ofPoly (p.map f)) = DensePoly.toPoly ((DensePoly.ofPoly p).map f)
  rw [toPoly_ofPoly, toPoly_map, toPoly_ofPoly]

@[simp] lemma toPoly_mapInjective [DecidableEq S] (f : R →+* S) (hf : Function.Injective f) (p : DensePoly R) :
  DensePoly.toPoly (p.mapInjective f hf) = (DensePoly.toPoly p).map f := by
  dsimp [mapInjective, mapZeroInjective, DensePoly.toPoly]
  have h1 : (p.coeffs.map (⇑f)).toList = p.coeffs.toList.map (⇑f) := by rw [Array.toList_map]
  rw [h1]
  exact toPoly_map_list f p.coeffs.toList

@[simp] lemma toPoly_mapAlgebraMap {R S : Type _} [CommSemiring R] [Semiring S] [Algebra R S] [DecidableEq S]
  (hf : Function.Injective (algebraMap R S)) (p : DensePoly R) :
  DensePoly.toPoly (p.mapAlgebraMap hf) = (DensePoly.toPoly p).map (algebraMap R S) := by
  dsimp [mapAlgebraMap]
  exact toPoly_mapInjective (algebraMap R S) hf p

@[simp] lemma toPoly_mapNatToInt (p : DensePoly ℕ) :
  DensePoly.toPoly (mapNatToInt p) = (DensePoly.toPoly p).map (algebraMap ℕ ℤ) := by
  dsimp [mapNatToInt]
  exact toPoly_mapAlgebraMap _ p

@[simp] lemma toPoly_mapIntToRat (p : DensePoly ℤ) :
  DensePoly.toPoly (mapIntToRat p) = (DensePoly.toPoly p).map (algebraMap ℤ ℚ) := by
  dsimp [mapIntToRat]
  exact toPoly_mapAlgebraMap _ p

@[simp] lemma toPoly_mapNatToZMod {n : ℕ} [NeZero n] (p : DensePoly ℕ) :
  DensePoly.toPoly (mapNatToZMod p) = (DensePoly.toPoly p).map (algebraMap ℕ (ZMod n)) := by
  dsimp [mapNatToZMod]
  exact toPoly_map (Nat.castRingHom (ZMod n)) p

@[simp] lemma toPoly_mapIntToZMod {n : ℕ} [NeZero n] (p : DensePoly ℤ) :
  DensePoly.toPoly (mapIntToZMod p) = (DensePoly.toPoly p).map (algebraMap ℤ (ZMod n)) := by
  dsimp [mapIntToZMod]
  exact toPoly_map (Int.castRingHom (ZMod n)) p

@[simp] lemma coeff_mapZModToNat {n : ℕ} [NeZero n] (p : DensePoly (ZMod n)) (i : ℕ) :
  (DensePoly.toPoly (mapZModToNat p)).coeff i = (p.coeff i).val := by
  rw [coeff_toPoly_eq]
  dsimp [mapZModToNat, mapZeroInjective, coeff]
  rw [Array.getElem?_map]
  cases p.coeffs[i]? with
  | none => exact ZMod.val_zero.symm
  | some val => rfl

end DensePoly
end Azurite
