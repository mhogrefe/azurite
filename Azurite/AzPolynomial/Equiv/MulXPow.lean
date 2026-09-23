import Azurite.AzPolynomial.MulXPow
import Azurite.AzPolynomial.Equiv.Basic
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Equivalence: `AzPolynomial.mulXPow` ↔ `p * Polynomial.X ^ n`

Shows that the efficient shift-by-`X^n` on `AzPolynomial R` agrees with
multiplication by `X^n` in Mathlib's `Polynomial R`.
-/

namespace Azurite.AzPolynomial

open Polynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

omit [DecidableEq R] in
/-- The coefficient description of `mulXPow n p`: shifted by `n`. -/
lemma coeff_mulXPow (n : ℕ) (p : AzPolynomial R) (i : ℕ) :
    (mulXPow n p).coeff i = if n ≤ i then p.coeff (i - n) else 0 := by
  unfold mulXPow
  split
  · -- p.coeffs.size = 0: p = 0 and mulXPow n p = p = 0
    next hp =>
      have hp_zero : ∀ k, p.coeff k = 0 := by
        intro k
        dsimp [coeff]
        have : p.coeffs[k]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
        rw [this]
        rfl
      rw [hp_zero i]
      split <;> [rw [hp_zero (i - n)]; rfl]
  · -- p.coeffs.size ≠ 0: coeffs are `Array.replicate n 0 ++ p.coeffs`
    next hp =>
      dsimp [coeff]
      by_cases hni : n ≤ i
      · rw [ite_eq_left hni]
        rw [Array.getElem?_append_right (by simp; omega)]
        congr 2
        simp
      · rw [ite_eq_right hni]
        rw [Array.getElem?_append_left (by simp; omega)]
        simp only [Array.getElem?_replicate]
        rw [ite_eq_left (by omega)]
        rfl

omit [DecidableEq R] in
@[simp] theorem toPoly_mulXPow (n : ℕ) (p : AzPolynomial R) :
    AzPolynomial.toPoly (mulXPow n p) = AzPolynomial.toPoly p * Polynomial.X ^ n := by
  ext i
  rw [coeff_toPoly_eq, Polynomial.coeff_mul_X_pow', coeff_mulXPow]
  split
  · rw [coeff_toPoly_eq]
  · rfl

@[simp] theorem ofPoly_mul_X_pow (n : ℕ) (p : Polynomial R) :
    AzPolynomial.ofPoly (p * Polynomial.X ^ n) =
    mulXPow n (AzPolynomial.ofPoly p) := by
  rw [← toPoly_inj, toPoly_ofPoly, toPoly_mulXPow, toPoly_ofPoly]

end Azurite.AzPolynomial
