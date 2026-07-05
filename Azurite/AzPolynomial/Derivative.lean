import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Parse

/-!
# Derivative of AzPolynomial

The formal derivative of `[a₀, a₁, a₂, ..., aₙ]` is
`[1·a₁, 2·a₂, 3·a₃, ..., n·aₙ]`.

Coefficient `i` of the derivative is `(i+1) * a_{i+1}`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

abbrev derivArray (p : AzPolynomial R) (_h : ¬p.coeffs.size ≤ 1) :=
  Array.ofFn (fun (i : Fin (p.coeffs.size - 1)) =>
    p.coeff (i.val + 1) * (↑(i.val + 1) : R))

/-- The formal derivative, always normalizing the result.
    Safe for any `Semiring`. -/
def derivativeNormalize (p : AzPolynomial R) : AzPolynomial R :=
  if h : p.coeffs.size ≤ 1 then
    zero
  else
    normalize (derivArray p (by omega))

/-!
## No-normalization variant

In a `CharZero` ring with `NoZeroDivisors`, the derivative of a nonzero
polynomial of degree ≥ 1 always has a nonzero leading coefficient.
The leading term `aₙ * n` satisfies `aₙ ≠ 0` (polynomial invariant)
and `(n : R) ≠ 0` (`CharZero`), so `aₙ * n ≠ 0` (`NoZeroDivisors`).
This lets us skip `normalize`.
-/

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

/-- Specialized derivative for `CharZero` + `NoZeroDivisors` rings (e.g., AzInt, AzRat, ℝ).
    Never calls `normalize`; the leading coefficient provably stays nonzero. -/
def derivativeNoNormalize [CharZero R] [NoZeroDivisors R]
    (p : AzPolynomial R) : AzPolynomial R :=
  if h : p.coeffs.size ≤ 1 then
    zero
  else
    ⟨derivArray p (by omega), derivArray_back_ne_zero p (by omega)⟩

/-!
## Auto-dispatch via typeclass

`derivative` resolves to `derivativeNoNormalize` when both `CharZero R` and
`NoZeroDivisors R` are available (high priority), and falls back to
`derivativeNormalize` otherwise — mirroring the `add` / `addNoCancel` pattern.
-/

/-- Typeclass providing the derivative implementation for `AzPolynomial R`.
    Implementations must agree with `derivativeNormalize` coefficient-wise. -/
class PolynomialDerivative (R : Type _) [Semiring R] [DecidableEq R] where
  derivative : AzPolynomial R → AzPolynomial R
  coeff_eq : ∀ (p : AzPolynomial R) (n : ℕ),
    (derivative p).coeff n = (derivativeNormalize p).coeff n

instance (priority := default) : PolynomialDerivative R where
  derivative := derivativeNormalize
  coeff_eq := fun _ _ => rfl

instance (priority := high) [CharZero R] [NoZeroDivisors R] : PolynomialDerivative R where
  derivative := derivativeNoNormalize
  coeff_eq := fun p n => by
    simp only [derivativeNoNormalize, derivativeNormalize]
    split
    · rfl
    · next h =>
      rw [coeff_normalize]
      simp [coeff, Array.getElem?_ofFn]

/-- The formal derivative of a polynomial.
    Dispatches to `derivativeNoNormalize` for `CharZero + NoZeroDivisors`
    rings, and `derivativeNormalize` otherwise. -/
def derivative [PolynomialDerivative R] (p : AzPolynomial R) : AzPolynomial R :=
  PolynomialDerivative.derivative p

-- Testing: AzInt is CharZero + NoZeroDivisors, so uses the fast path
#guard toChars (derivative (parseAzPolynomial (R := AzInt) "x^3+x").get!) == "3*x^2+1"
#guard toChars (derivative (parseAzPolynomial (R := AzInt) "2*x^2+3*x+5").get!) == "4*x+3"
#guard toChars (derivative (parseAzPolynomial (R := AzInt) "42").get!) == "0"
#guard toChars (derivative (0 : AzPolynomial AzInt)) == "0"
#guard toChars (derivative (parseAzPolynomial (R := AzInt) "x").get!) == "1"
#guard toChars (derivative (parseAzPolynomial (R := AzInt) "x^4").get!) == "4*x^3"

end Azurite.AzPolynomial
