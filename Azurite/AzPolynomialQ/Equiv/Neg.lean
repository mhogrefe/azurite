import Azurite.AzPolynomialQ.Neg
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Neg

open Polynomial

namespace Azurite.AzPolynomialQ

@[simp] lemma toAzPolynomial_neg (p : AzPolynomialQ) : (-p).toAzPolynomial = - p.toAzPolynomial := by
  ext i
  simp

@[simp] lemma toPoly_neg (p : AzPolynomialQ) : (-p).toPoly = - p.toPoly := by
  ext i
  simp

@[simp] lemma ofAzPolynomial_neg (p : Azurite.AzPolynomial ℚ) : ofAzPolynomial (-p) = - ofAzPolynomial p := by
  apply AzPolynomialQ.coeff_ext
  intro i
  simp

end Azurite.AzPolynomialQ
