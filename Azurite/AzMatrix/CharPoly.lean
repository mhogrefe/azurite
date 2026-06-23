import Azurite.AzMatrix.Operations
import Azurite.AzMatrix.Equiv.Algebra
import Azurite.AzPolynomial.NewtonSum

/-!
# BPR Algorithm 8.17: Characteristic polynomial via baby-step/giant-step Newton sums

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.2, Algorithm 8.17.

Computes `CharPol(M) = det(X·Idₙ − M)` for a square matrix `M` over a field, using
the **baby-step/giant-step** method of BPR Algorithm 8.17. The trace of `Mⁱ` is the
`i`-th Newton sum (power sum) of the eigenvalues of `M`, so

  `N₀ = Tr(Id) = n`,  `Nᵢ = Tr(Mⁱ)`  for `i = 1, …, n`,

are the Newton sums of the (monic) characteristic polynomial, from which its
coefficients are recovered by BPR Algorithm 8.11 (`polyFromNewtonSumsMonic`).

To compute all of `M⁰, …, Mⁿ` with only `O(√n)` matrix multiplications, write
`r = ⌊√n⌋ + 1` (the smallest integer with `r² > n`) and `k = j·r + i` with
`0 ≤ i, j < r`. Then `Mᵏ = M^{jr}·Mⁱ`, so it suffices to precompute the
*baby steps* `Bᵢ = Mⁱ` (`i < r`) and the *giant steps* `C_j = M^{jr}` (`j < r`),
each an `O(√n)`-long chain of multiplications, and read off
`Nᵏ = Tr(C_j · Bᵢ)`. The trace of a product is computed directly as
`Tr(A·B) = ∑_{a,b} A_{a,b} B_{b,a}` (`traceMul`), without forming the product.

> BPR states the algorithm over a "ring with integer division"; the Newton-sums
> recovery `polyFromNewtonSumsMonic` divides by `1, …, n`, so here we use `[Field A]`,
> the computable home for those divisions (e.g. `AzRat`).
-/

namespace Azurite
namespace AzMatrix

variable {R : Type _} {n : ℕ}

/-- The **trace** of a square matrix: the sum of its diagonal entries. -/
def trace [AddCommMonoid R] (M : AzMatrix R n n) : R :=
  ∑ i : Fin n, M.get i i

/-- The **trace of a product** `Tr(A · B) = ∑_{i,j} A_{i,j} B_{j,i}`, computed
    directly without forming the product `A · B`. -/
def traceMul [Mul R] [AddCommMonoid R] (A B : AzMatrix R n n) : R :=
  ∑ i : Fin n, ∑ j : Fin n, A.get i j * B.get j i

/-- **BPR Algorithm 8.17: characteristic polynomial.** For a square matrix `M`
    over a field, `charPoly M = det(X·Idₙ − M)`, the monic characteristic
    polynomial, computed by the baby-step/giant-step Newton-sum method.

    With `r = ⌊√n⌋ + 1` (the smallest integer with `r² > n`):
    * `baby[i] = Mⁱ` for `i = 0, …, r−1` (the baby steps);
    * `giant[j] = M^{rj}` for `j = 0, …, r−1` (the giant steps);
    * `Nₖ = Tr(M^{k%r} · M^{r·(k/r)}) = Tr(Mᵏ)` for `k = 0, …, n`, since
      `(k%r) + r·(k/r) = k`;
    * the coefficients follow from `polyFromNewtonSumsMonic` (Algorithm 8.11). -/
def charPoly {A : Type _} [Field A] (M : AzMatrix A n n) : AzPolynomial A :=
  let r := n.sqrt + 1
  -- baby steps `baby[i] = Mⁱ` and giant steps `giant[j] = M^{rj}`.
  let baby : Array (AzMatrix A n n) := Array.ofFn (n := r) (fun i => M ^ (i : ℕ))
  let giant : Array (AzMatrix A n n) := Array.ofFn (n := r) (fun j => M ^ (r * (j : ℕ)))
  -- `Nₖ = Tr(Mᵏ)`, with `k = (k%r) + r·(k/r)` so `Mᵏ = M^{k%r} · M^{r·(k/r)}`.
  let N : Array A := (Array.range (n + 1)).map (fun k =>
    traceMul (baby.getD (k % r) 1) (giant.getD (k / r) 1))
  AzPolynomial.polyFromNewtonSumsMonic N

/-! ## Worked examples -/

section Tests

-- `M = [[1, 2], [3, 4]]`: `CharPol = X² − 5X − 2` (trace 5, det −2).
#guard
  match (AzMatrix.parseStr "[1, 2; 3, 4]" : Option (AzMatrix AzRat 2 2)) with
  | some M => toString M.charPoly == "x^2-5*x-2"
  | none => False

-- The `2 × 2` identity: `CharPol = (X − 1)² = X² − 2X + 1`.
#guard toString (1 : AzMatrix AzRat 2 2).charPoly == "x^2-2*x+1"

-- `M = diag(1, 2, 3)`: `CharPol = (X−1)(X−2)(X−3) = X³ − 6X² + 11X − 6`.
#guard
  match (AzMatrix.parseStr "[1, 0, 0; 0, 2, 0; 0, 0, 3]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => toString M.charPoly == "x^3-6*x^2+11*x-6"
  | none => False

-- A general `3 × 3` matrix `M = [[2,1,1],[1,3,2],[1,0,0]]`: trace 5, det −1,
-- sum of 2×2 principal minors 5 − 1 + 0 = 4, so `CharPol = X³ − 5X² + 4X + 1`.
#guard
  match (AzMatrix.parseStr "[2, 1, 1; 1, 3, 2; 1, 0, 0]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => toString M.charPoly == "x^3-5*x^2+4*x+1"
  | none => False

-- `4 × 4` identity: `CharPol = (X − 1)⁴ = X⁴ − 4X³ + 6X² − 4X + 1`
-- (exercises the `r = 3` baby-step/giant-step split, since `⌊√4⌋ + 1 = 3`).
#guard toString (1 : AzMatrix AzRat 4 4).charPoly == "x^4-4*x^3+6*x^2-4*x+1"

end Tests

end AzMatrix
end Azurite
