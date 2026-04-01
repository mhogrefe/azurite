import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.Equiv.Add
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Equivalence: AzPolynomial.derivative ↔ Polynomial.derivative

We prove that `AzPolynomial.derivative` agrees with Mathlib's
`Polynomial.derivative` under the `toPoly` / `ofPoly` correspondence.
-/

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

private lemma derivative_coeff_eq (p : AzPolynomial R) (n : ℕ) :
    (derivative p).coeff n = p.coeff (n + 1) * (↑(n + 1) : R) := by
  unfold derivative
  split
  · next h =>
    -- p.coeffs.size ≤ 1, so derivative is zero
    simp only [zero, coeff]
    simp
    have : p.coeffs[n + 1]? = none :=
      Array.getElem?_eq_none (by omega)
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

@[simp] theorem toPoly_derivative (p : AzPolynomial R) :
    AzPolynomial.toPoly (derivative p) = Polynomial.derivative (AzPolynomial.toPoly p) := by
  ext n
  rw [coeff_toPoly, Polynomial.coeff_derivative, coeff_toPoly,
      derivative_coeff_eq p n, Nat.cast_succ]

@[simp] theorem ofPoly_derivative (p : Polynomial R) :
    AzPolynomial.ofPoly (Polynomial.derivative p) = derivative (AzPolynomial.ofPoly p) := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_derivative, toPoly_ofPoly, toPoly_ofPoly]

end Azurite.AzPolynomial
