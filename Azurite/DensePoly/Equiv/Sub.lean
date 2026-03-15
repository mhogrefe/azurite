import Azurite.DensePoly.Sub
import Azurite.DensePoly.Equiv.Add
import Azurite.DensePoly.Equiv.Neg

open Polynomial

namespace Azurite.DensePoly

variable {R : Type _} [Ring R] [DecidableEq R]

@[simp] lemma toPoly_sub (p q : DensePoly R) :
  DensePoly.toPoly (p - q) = DensePoly.toPoly p - DensePoly.toPoly q := by
  dsimp [HSub.hSub, Sub.sub, sub]
  rw [toPoly_add, toPoly_neg]

@[simp] lemma coeff_sub (p q : DensePoly R) (n : ℕ) :
  coeff (p - q) n = coeff p n - coeff q n := by
  have h := toPoly_sub p q
  have hc : (DensePoly.toPoly (p - q)).coeff n = (DensePoly.toPoly p - DensePoly.toPoly q).coeff n := by rw [h]
  rw [Polynomial.coeff_sub, coeff_toPoly p, coeff_toPoly q] at hc
  rw [← hc]
  exact (coeff_toPoly (p - q) n).symm

@[simp] lemma ofPoly_sub (p q : Polynomial R) :
  DensePoly.ofPoly (p - q) = DensePoly.ofPoly p - DensePoly.ofPoly q := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_sub, toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

end Azurite.DensePoly
