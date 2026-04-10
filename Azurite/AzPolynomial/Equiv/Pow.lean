import Azurite.AzPolynomial.Pow
import Azurite.AzPolynomial.Equiv.Algebra

/-!
# Equivalence: AzPolynomial.pow ↔ Polynomial.pow

Proves that `AzPolynomial.pow p n` (computable, via exponentiation by squaring)
agrees with Mathlib's `Polynomial.pow` (i.e., `toPoly p ^ n`).

Since the `Semiring` instance on `AzPolynomial R` already uses `fastPow` as its `npow`,
`p.pow n` is definitionally `p ^ n`, and `toPoly (p ^ n) = toPoly p ^ n` follows from
`map_pow` on the ring equivalence.

## Main Theorems

- `toPoly_pow`: `toPoly (p.pow n) = toPoly p ^ n`
- `ofPoly_pow`: `(ofPoly p).pow n = ofPoly (p ^ n)`
-/

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Forward direction: `toPoly` preserves `pow`. -/
@[simp] theorem toPoly_pow (p : AzPolynomial R) (n : ℕ) :
    AzPolynomial.toPoly (p.pow n) = AzPolynomial.toPoly p ^ n := by
  show AzPolynomial.toPoly (Azurite.fastPow p n) = _
  rw [Azurite.fastPow, AzPolynomial.toPoly_fastPowAux, toPoly_one, one_mul]

/-- Backward direction: `ofPoly` preserves `pow`. -/
@[simp] theorem ofPoly_pow (p : Polynomial R) (n : ℕ) :
    (AzPolynomial.ofPoly p).pow n = AzPolynomial.ofPoly (p ^ n) := by
  apply toPoly_inj.mp
  rw [toPoly_pow, toPoly_ofPoly, toPoly_ofPoly]

end Azurite.AzPolynomial
