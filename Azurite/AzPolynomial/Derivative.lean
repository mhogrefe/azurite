import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse

/-!
# Derivative of AzPolynomial

The formal derivative of `[a₀, a₁, a₂, ..., aₙ]` is
`[1·a₁, 2·a₂, 3·a₃, ..., n·aₙ]`.

Coefficient `i` of the derivative is `(i+1) * a_{i+1}`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- The formal derivative of a polynomial.
    Given `p = a₀ + a₁X + a₂X² + ⋯ + aₙXⁿ`, returns
    `a₁ + 2a₂X + 3a₃X² + ⋯ + naₙXⁿ⁻¹`. -/
def derivative (p : AzPolynomial R) : AzPolynomial R :=
  if _ : p.coeffs.size ≤ 1 then
    zero
  else
    normalize (Array.ofFn (fun (i : Fin (p.coeffs.size - 1)) =>
      p.coeff (i.val + 1) * (↑(i.val + 1) : R)))

-- Testing the implementation using Integer polynomials
-- derivative of x^3 + x = 3x^2 + 1
#guard derivative (parseAzPolynomial (R := ℤ) "x^3+x").get! == (parseAzPolynomial (R := ℤ) "3*x^2+1").get!
-- derivative of 2x^2 + 3x + 5 = 4x + 3
#guard derivative (parseAzPolynomial (R := ℤ) "2*x^2+3*x+5").get! == (parseAzPolynomial (R := ℤ) "4*x+3").get!
-- derivative of constant = 0
#guard derivative (parseAzPolynomial (R := ℤ) "42").get! == (0 : AzPolynomial ℤ)
-- derivative of 0 = 0
#guard derivative (0 : AzPolynomial ℤ) == (0 : AzPolynomial ℤ)
-- derivative of x = 1
#guard derivative (parseAzPolynomial (R := ℤ) "x").get! == (parseAzPolynomial (R := ℤ) "1").get!
-- derivative of x^4 = 4x^3
#guard derivative (parseAzPolynomial (R := ℤ) "x^4").get! == (parseAzPolynomial (R := ℤ) "4*x^3").get!

/-!
## No-normalization variant

In a `CharZero` ring with `NoZeroDivisors`, the derivative of a nonzero
polynomial of degree ≥ 1 always has a nonzero leading coefficient.
The leading term `aₙ * n` satisfies `aₙ ≠ 0` (polynomial invariant)
and `(n : R) ≠ 0` (`CharZero`), so `aₙ * n ≠ 0` (`NoZeroDivisors`).
This lets us skip `normalize`.
-/

private abbrev derivArray (p : AzPolynomial R) (_h : ¬p.coeffs.size ≤ 1) :=
  Array.ofFn (fun (i : Fin (p.coeffs.size - 1)) =>
    p.coeff (i.val + 1) * (↑(i.val + 1) : R))

omit [DecidableEq R] in
private lemma derivArray_back_ne_zero [CharZero R] [NoZeroDivisors R]
    (p : AzPolynomial R) (h : ¬p.coeffs.size ≤ 1) :
    (derivArray p h).back? ≠ some 0 := by
  have hgt : 1 < p.coeffs.size := by omega
  have hlen : p.coeffs.size - 1 - 1 < p.coeffs.size - 1 := by omega
  unfold Array.back?; simp [hlen]
  constructor
  · -- p.coeff (size - 1) ≠ 0
    have hsub : p.coeffs.size - 1 - 1 + 1 = p.coeffs.size - 1 := by omega
    rw [hsub]
    simp [coeff]
    have hlt : p.coeffs.size - 1 < p.coeffs.size := by omega
    have hback : p.coeffs[p.coeffs.size - 1]? = p.coeffs.back? := by
      simp [Array.back?, hlt]
    rw [hback]
    intro heq
    have := p.last_ne_zero
    rw [show p.coeffs.back? = some (p.coeffs.back?.getD 0) from by
      simp [Array.back?, hlt]] at this
    exact this (by rw [Option.some.injEq]; exact heq)
  · -- ↑(size-1-1) + 1 ≠ 0 in R
    exact Nat.cast_add_one_ne_zero _

/-- Specialized derivative for `CharZero` + `NoZeroDivisors` rings (e.g., ℤ, ℚ, ℝ).
    Never calls `normalize`; the leading coefficient provably stays nonzero. -/
def derivativeNoNormalize [CharZero R] [NoZeroDivisors R]
    (p : AzPolynomial R) : AzPolynomial R :=
  if h : p.coeffs.size ≤ 1 then
    zero
  else
    ⟨derivArray p h, derivArray_back_ne_zero p h⟩

end Azurite.AzPolynomial

