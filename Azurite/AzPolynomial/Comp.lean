import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Parse

/-!
# Polynomial Composition

Computes `p(q)` for univariate polynomials using Horner's method. This matches
`Polynomial.comp` from Mathlib: given `p = a₀ + a₁x + ⋯ + aₙxⁿ`, it returns
`a₀ + q·(a₁ + q·(a₂ + ⋯ + q·aₙ))`.

Horner's method performs `n` multiplications by `q` and `n` additions, where `n`
is the degree of `p`. Each multiplication has cost proportional to the product of
the degrees, so the total cost is O(deg(p) · deg(q) · deg(p)) in the worst case.

## Main Definition

- `AzPolynomial.comp p q`: computes the polynomial composition `p(q)`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R] [AzPolynomialMulConfig R]

/-- Computes the composition `p(q)` using Horner's method.
    Given `p = a₀ + a₁x + a₂x² + ⋯ + aₙxⁿ`, returns
    `a₀ + q·(a₁ + q·(a₂ + ⋯ + q·aₙ))`.

    Matches `Polynomial.comp` from Mathlib. -/
def comp (p q : AzPolynomial R) : AzPolynomial R :=
  p.coeffs.foldr (init := (0 : AzPolynomial R)) fun a acc => C a + acc * q

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- x² ∘ (x+1) = (x+1)² = x²+2x+1
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2").get!.comp (parseAzPolynomial (R := AzInt) "x+1").get!)
    == "x^2+2*x+1"

-- (2x+1) ∘ (x+1) = 2(x+1)+1 = 2x+3
#guard toChars ((parseAzPolynomial (R := AzInt) "2*x+1").get!.comp (parseAzPolynomial (R := AzInt) "x+1").get!)
    == "2*x+3"

-- x³ ∘ 2x = (2x)³ = 8x³
#guard toChars ((parseAzPolynomial (R := AzInt) "x^3").get!.comp (parseAzPolynomial (R := AzInt) "2*x").get!)
    == "8*x^3"

-- Identity: x ∘ g = g
#guard toChars ((parseAzPolynomial (R := AzInt) "x").get!.comp (parseAzPolynomial (R := AzInt) "x^2+1").get!)
    == "x^2+1"

-- Constant: 5 ∘ g = 5
#guard toChars ((parseAzPolynomial (R := AzInt) "5").get!.comp (parseAzPolynomial (R := AzInt) "x^10").get!)
    == "5"

-- Zero: 0 ∘ g = 0
#guard toChars ((0 : AzPolynomial AzInt).comp (parseAzPolynomial (R := AzInt) "x+1").get!) == "0"

-- g ∘ 0 = f(0) = constant term
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2+3*x+7").get!.comp (0 : AzPolynomial AzInt))
    == "7"

-- (x+1)² ∘ (x-1) = ((x-1)+1)² = x²
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2+2*x+1").get!.comp (parseAzPolynomial (R := AzInt) "x-1").get!)
    == "x^2"

end Tests

end Azurite.AzPolynomial
