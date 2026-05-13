import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# BPR §8.1 Notation 8.7: Horner polynomials

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1, Notation 8.7, p. 284.

Let `P = aₚ Xᵖ + ⋯ + a₀ ∈ A[X]`, where `A` is a ring. The **Horner
polynomials** associated to `P` are defined inductively by

  `Hor₀(P, X) = aₚ`,
  `Horᵢ(P, X) = X · Horᵢ₋₁(P, X) + aₚ₋ᵢ`,

for `0 ≤ i ≤ p`, so that

  `Horᵢ(P, X) = aₚ Xⁱ + aₚ₋₁ Xⁱ⁻¹ + ⋯ + aₚ₋ᵢ`.

In particular, `Horₚ(P, X) = P`. The Horner polynomials are the
intermediate state of Horner's method for evaluating `P` at a point
(Algorithm 8.7).

The definitions live in the `Polynomial` namespace (outside
`Azurite.BPR`) so they extend Mathlib's `Polynomial`.
-/

section Horner

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **BPR Notation 8.7 (Horner polynomials).** Given `P ∈ R[X]` with
    `p = natDegree P`, the `i`-th Horner polynomial is defined by:
    - `Hor₀(P, X) = C(aₚ)` (the leading coefficient as a constant polynomial)
    - `Horᵢ₊₁(P, X) = X · Horᵢ(P, X) + C(aₚ₋ᵢ₋₁)` -/
noncomputable def Polynomial.horner (P : R[X]) : ℕ → R[X]
  | 0 => C (P.coeff P.natDegree)
  | i + 1 => X * P.horner i + C (P.coeff (P.natDegree - (i + 1)))

/-- The base case: `Hor₀(P, X) = C(leadingCoeff P)`. -/
theorem Polynomial.horner_zero (P : R[X]) :
    P.horner 0 = C P.leadingCoeff := by
  unfold Polynomial.horner; rw [leadingCoeff]

/-- The recurrence: `Horᵢ₊₁(P, X) = X · Horᵢ(P, X) + C(aₚ₋ᵢ₋₁)`. -/
theorem Polynomial.horner_succ (P : R[X]) (i : ℕ) :
    P.horner (i + 1) = X * P.horner i + C (P.coeff (P.natDegree - (i + 1))) :=
  rfl

/-- **Closed-form characterization.**
    `Horᵢ(P, X) = ∑ j ∈ range (i+1), C(aₚ₋ⱼ) · X^{i−j}`
    `         = aₚ Xⁱ + aₚ₋₁ Xⁱ⁻¹ + ⋯ + aₚ₋ᵢ`. -/
theorem Polynomial.horner_eq_sum (P : R[X]) (i : ℕ) :
    P.horner i = ∑ j ∈ range (i + 1),
      C (P.coeff (P.natDegree - j)) * X ^ (i - j) := by
  induction i with
  | zero => simp [Polynomial.horner]
  | succ n ih =>
    rw [Polynomial.horner, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show n + 1 - (n + 1) = 0 from Nat.sub_self _, pow_zero, mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mul_comm X (C _ * X ^ _), mul_assoc, ← pow_succ,
        show n - j + 1 = n + 1 - j from by omega]

/-- **`Horₚ(P, X) = P`.** The last Horner polynomial recovers `P`. -/
theorem Polynomial.horner_natDegree (P : R[X]) :
    P.horner P.natDegree = P := by
  rw [Polynomial.horner_eq_sum]
  conv_rhs => rw [Polynomial.as_sum_range P]
  rw [← Finset.sum_flip]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show P.natDegree - (P.natDegree - j) = j from by omega,
      C_mul_X_pow_eq_monomial]

end Horner
