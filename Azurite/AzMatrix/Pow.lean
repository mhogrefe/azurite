import Azurite.Algorithm.FastPow
import Azurite.AzMatrix.Equiv.Algebra
import Azurite.AzMatrix.Parse
import Mathlib.Data.ZMod.Basic

/-!
# Exponentiation by Squaring for AzMatrix

Computable matrix exponentiation for square matrices using the generic `fastPow` algorithm.

The `^` operator on `AzMatrix R n n` (from the `Semiring` instance in `Equiv/Algebra.lean`)
already uses `fastPow` internally, so `A.pow k = A ^ k`. This file provides the explicit
`pow` function for direct use.

## Main Definition

- `Azurite.AzMatrix.pow A k`: computes `A ^ k` in O(log k) matrix multiplications.
-/

namespace Azurite

variable {R : Type _} [CommSemiring R] {n : Nat}

/-- Computable exponentiation for square `AzMatrix R n n` via binary exponentiation.
    Uses the `Mul` and `One` instances for square matrices (basecase multiplication
    and identity matrix). Agrees with `A ^ k` (the `Semiring`'s `Pow` instance). -/
def AzMatrix.pow (A : AzMatrix R n n) (k : ℕ) : AzMatrix R n n :=
  Azurite.fastPow A k

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

/-- The Fibonacci matrix [[1,1],[1,0]] over ZMod p.
    Its n-th power gives Fibonacci numbers mod p:
    `(fibMat^n)[0][1] = F(n) mod p`. -/
private def fibMat : AzMatrix (ZMod 1000000007) 2 2 :=
  AzMatrix.ofLists [[1, 1], [1, 0]]

-- Raise to 10^18 — runs in O(log(10^18)) ≈ 60 matrix multiplications.
-- Computes F(10^18) mod 10^9+7 instantly.
#guard toString (fibMat.pow 1000000000000000000) =
  "[680057396, 209783453; 209783453, 470273943]"

end Tests

end Azurite
