import Azurite.DensePoly.Neg
import Azurite.DensePoly.Equiv.Basic

open Polynomial

variable {R : Type _} [Ring R]

namespace Azurite.DensePoly

lemma toPoly_map_neg (l : List R) : (l.map (-·)).toPoly = - l.toPoly := by
  induction l with
  | nil => simp [List.toPoly]
  | cons a as ih =>
    dsimp [List.toPoly]
    rw [ih]
    rw [map_neg, mul_neg]
    exact (neg_add (C a) (X * as.toPoly)).symm

@[simp] lemma toPoly_neg [DecidableEq R] (p : DensePoly R) : DensePoly.toPoly (-p) = - DensePoly.toPoly p := by
  change DensePoly.toPoly (mapZeroInjective _ _ p) = - DensePoly.toPoly p
  dsimp [DensePoly.mapZeroInjective, DensePoly.toPoly]
  have hw : (p.coeffs.map (fun x => -x)).toList = p.coeffs.toList.map (fun x => -x) := by simp
  rw [hw]
  exact toPoly_map_neg p.coeffs.toList

@[simp] lemma ofPoly_neg [DecidableEq R] (p : Polynomial R) : DensePoly.ofPoly (-p) = - DensePoly.ofPoly p := by
  apply equivPolynomial.injective
  change DensePoly.toPoly (DensePoly.ofPoly (-p)) = DensePoly.toPoly (- DensePoly.ofPoly p)
  rw [toPoly_ofPoly, toPoly_neg, toPoly_ofPoly]

end Azurite.DensePoly
