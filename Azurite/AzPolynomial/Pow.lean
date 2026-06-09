import Azurite.Algorithm.SlidingWindowPow
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Parse

/-!
# Sliding-Window Exponentiation for AzPolynomial

Computable polynomial exponentiation using the generic `slidingWindowPow` algorithm.

The `^` operator on `AzPolynomial R` (from the `Semiring` instance in `Equiv/Algebra.lean`)
already uses `slidingWindowPow` internally, so `p.pow n = p ^ n`. This file provides the explicit
`pow` function for direct use and adds `#guard` tests.

## Main Definition

- `Azurite.AzPolynomial.pow p n`: computes `p ^ n` in O(log n) polynomial multiplications.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R] [AzPolynomialMulConfig R]

/-- Computable exponentiation for `AzPolynomial R` via sliding-window exponentiation.
    Uses the configured multiplication algorithm (basecase or Karatsuba).
    Agrees with `p ^ n` (the `Semiring`'s `Pow` instance). -/
def pow (p : AzPolynomial R) (n : ℕ) : AzPolynomial R :=
  Azurite.slidingWindowPow p n

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

#guard (parseAzPolynomial (R := ℤ) "x+1").get!.pow 0 == 1
#guard (parseAzPolynomial (R := ℤ) "x+1").get!.pow 1 == (parseAzPolynomial (R := ℤ) "x+1").get!
#guard (parseAzPolynomial (R := ℤ) "x+1").get!.pow 2 == (parseAzPolynomial (R := ℤ) "x^2+2*x+1").get!
#guard (parseAzPolynomial (R := ℤ) "x+1").get!.pow 3 == (parseAzPolynomial (R := ℤ) "x^3+3*x^2+3*x+1").get!
#guard (parseAzPolynomial (R := ℤ) "2*x").get!.pow 4 == (parseAzPolynomial (R := ℤ) "16*x^4").get!
#guard (0 : AzPolynomial ℤ).pow 5 == 0
#guard (1 : AzPolynomial ℤ).pow 100 == 1

end Tests

end Azurite.AzPolynomial
