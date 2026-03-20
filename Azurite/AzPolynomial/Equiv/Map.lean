import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Cast
import Mathlib.Algebra.Polynomial.Basic

open Polynomial

variable {R S : Type _} [Semiring R] [Semiring S]

namespace Azurite
namespace AzPolynomial

lemma toPoly_map_list (f : R →+* S) (l : List R) :
  (l.map f).toPoly = (l.toPoly).map f := by
  induction l with
  | nil =>
    simp [List.toPoly]
  | cons a as ih =>
    simp [List.toPoly, ih, Polynomial.map_add, Polynomial.map_mul]

@[simp] lemma toPoly_map [DecidableEq S] (f : R →+* S) (p : AzPolynomial R) :
  AzPolynomial.toPoly (p.map f) = (AzPolynomial.toPoly p).map f := by
  dsimp [map]
  rw [_root_.toPoly_normalize]
  have h1 : (p.coeffs.map f).toList = p.coeffs.toList.map f := by simp
  rw [h1]
  exact toPoly_map_list f p.coeffs.toList

@[simp] lemma ofPoly_map [DecidableEq R] [DecidableEq S] (f : R →+* S) (p : Polynomial R) :
  AzPolynomial.ofPoly (p.map f) = (AzPolynomial.ofPoly p).map f := by
  apply equivPolynomial.injective
  change AzPolynomial.toPoly (AzPolynomial.ofPoly (p.map f)) = AzPolynomial.toPoly ((AzPolynomial.ofPoly p).map f)
  rw [toPoly_ofPoly, toPoly_map, toPoly_ofPoly]

@[simp] lemma toPoly_mapInjective [DecidableEq S] (f : R →+* S) (hf : Function.Injective f) (p : AzPolynomial R) :
  AzPolynomial.toPoly (p.mapInjective f hf) = (AzPolynomial.toPoly p).map f := by
  dsimp [mapInjective, mapZeroInjective, AzPolynomial.toPoly]
  have h1 : (p.coeffs.map (⇑f)).toList = p.coeffs.toList.map (⇑f) := by rw [Array.toList_map]
  rw [h1]
  exact toPoly_map_list f p.coeffs.toList

@[simp] lemma toPoly_mapAlgebraMap {R S : Type _} [CommSemiring R] [Semiring S] [Algebra R S] [DecidableEq S]
  (hf : Function.Injective (algebraMap R S)) (p : AzPolynomial R) :
  AzPolynomial.toPoly (p.mapAlgebraMap hf) = (AzPolynomial.toPoly p).map (algebraMap R S) := by
  dsimp [mapAlgebraMap]
  exact toPoly_mapInjective (algebraMap R S) hf p

@[simp] lemma toPoly_mapNatToInt (p : AzPolynomial ℕ) :
  AzPolynomial.toPoly (mapNatToInt p) = (AzPolynomial.toPoly p).map (algebraMap ℕ ℤ) := by
  dsimp [mapNatToInt]
  exact toPoly_mapAlgebraMap _ p

@[simp] lemma toPoly_mapIntToRat (p : AzPolynomial ℤ) :
  AzPolynomial.toPoly (mapIntToRat p) = (AzPolynomial.toPoly p).map (algebraMap ℤ ℚ) := by
  dsimp [mapIntToRat]
  exact toPoly_mapAlgebraMap _ p

@[simp] lemma toPoly_mapNatToZMod {n : ℕ} [NeZero n] (p : AzPolynomial ℕ) :
  AzPolynomial.toPoly (mapNatToZMod p) = (AzPolynomial.toPoly p).map (algebraMap ℕ (ZMod n)) := by
  dsimp [mapNatToZMod]
  exact toPoly_map (Nat.castRingHom (ZMod n)) p

@[simp] lemma toPoly_mapIntToZMod {n : ℕ} [NeZero n] (p : AzPolynomial ℤ) :
  AzPolynomial.toPoly (mapIntToZMod p) = (AzPolynomial.toPoly p).map (algebraMap ℤ (ZMod n)) := by
  dsimp [mapIntToZMod]
  exact toPoly_map (Int.castRingHom (ZMod n)) p

@[simp] lemma coeff_mapZModToNat {n : ℕ} [NeZero n] (p : AzPolynomial (ZMod n)) (i : ℕ) :
  (AzPolynomial.toPoly (mapZModToNat p)).coeff i = (p.coeff i).val := by
  rw [coeff_toPoly_eq]
  dsimp [mapZModToNat, mapZeroInjective, coeff]
  rw [Array.getElem?_map]
  cases p.coeffs[i]? with
  | none => exact ZMod.val_zero.symm
  | some val => rfl

end AzPolynomial
end Azurite
