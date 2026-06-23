import Azurite.AzMatrix.Basic
import Azurite.AzMatrix.Parse
import Azurite.AzPolynomial.NewtonSum

/-!
# Newton matrix (computable, over a `CommRing`)

For a monic polynomial `P` over a commutative ring `R` and `k : ℕ`,
`P.newtMatMonic k : AzMatrix R k k` is the `k × k` Hankel matrix whose
`(i, j)` entry is the Newton sum `N_{i + j}`. The Newton sums are
computed via the Newton recurrence (`newtonSumStep`), exactly once each,
rather than via the spec function `newtonSumMonic` (which re-explores
the recursion tree at each call).

This is the computable analog of the BPR matrix `Newt_{p-k}(P)` defined
noncomputably as `Azurite.BPR.Chapter4.newtMat` over an algebraically
closed field.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R]

/-- **Computable Newton matrix.** For a monic polynomial `P : AzPolynomial R`
    of degree `p` and `k : ℕ`, `P.newtMatMonic k` is the `k × k` Hankel
    matrix with entry `N_{i + j} = newtonSumMonic P (i + j)` at row `i`,
    column `j`.

    The implementation precomputes the first `2 · k − 1` Newton sums via
    `newtonSumsMonicIter` (linear-time iterative recurrence) and indexes
    into the resulting array to fill the matrix, so each Newton sum is
    computed exactly once per call regardless of `k²` matrix entries. -/
def newtMatMonic (P : AzPolynomial R) (k : ℕ) : AzMatrix R k k :=
  let sums := newtonSumsMonicIter P (2 * k - 1)
  AzMatrix.ofFn fun i j => sums.getD (i.val + j.val) 0

-- Sanity checks.
section Tests

-- P = X^2 - 3X + 2, Newton sums [N_0, …] = [2, 3, 5, 9, 17].
#guard
  toString ((parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!.newtMatMonic 1) ==
    "[2]"

#guard
  toString ((parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!.newtMatMonic 2) ==
    "[2, 3; 3, 5]"

#guard
  toString ((parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!.newtMatMonic 3) ==
    "[2, 3, 5; 3, 5, 9; 5, 9, 17]"

-- P = X^3 - 6X^2 + 11X - 6, roots {1, 2, 3}; Newton sums [3, 6, 14, 36, 98].
#guard
  toString
      ((parseAzPolynomial (R := AzInt) "x^3-6*x^2+11*x-6").get!.newtMatMonic 3) ==
    "[3, 6, 14; 6, 14, 36; 14, 36, 98]"

-- Vacuous `k = 0` case (no entries).
#guard
  toString ((parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!.newtMatMonic 0) == "[]"

end Tests

end Azurite.AzPolynomial
