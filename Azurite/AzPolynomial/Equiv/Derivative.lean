import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.Equiv.Add
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Equivalence: AzPolynomial.derivative ↔ Polynomial.derivative

The `PolynomialDerivative` typeclass guarantees that any implementation has the
same coefficients as `derivativeNormalize`. We prove equivalence for
`derivativeNormalize`, then lift it to the typeclass-dispatched `derivative`.
-/

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

private lemma derivativeNormalize_coeff_eq (p : AzPolynomial R) (n : ℕ) :
    (derivativeNormalize p).coeff n = p.coeff (n + 1) * (↑(n + 1) : R) := by
  unfold derivativeNormalize
  split
  · next h =>
    simp only [zero, coeff]; simp
    have : p.coeffs[n + 1]? = none := Array.getElem?_eq_none (by omega)
    simp [this]
  · next h =>
    push_neg at h
    rw [coeff_normalize]
    simp only [Array.getElem?_ofFn]
    split
    · rfl
    · next h2 =>
      simp [coeff]
      have : p.coeffs[n + 1]? = none := Array.getElem?_eq_none (by omega)
      simp [this]

@[simp] theorem toPoly_derivative [PolynomialDerivative R] (p : AzPolynomial R) :
    AzPolynomial.toPoly (derivative p) = Polynomial.derivative (AzPolynomial.toPoly p) := by
  ext n
  rw [coeff_toPoly, Polynomial.coeff_derivative, coeff_toPoly]
  rw [show (derivative p).coeff n = (derivativeNormalize p).coeff n from
    PolynomialDerivative.coeff_eq p n]
  rw [derivativeNormalize_coeff_eq, Nat.cast_succ]

@[simp] theorem ofPoly_derivative [PolynomialDerivative R] (p : Polynomial R) :
    AzPolynomial.ofPoly (Polynomial.derivative p) = derivative (AzPolynomial.ofPoly p) := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_derivative, toPoly_ofPoly, toPoly_ofPoly]

end Azurite.AzPolynomial
