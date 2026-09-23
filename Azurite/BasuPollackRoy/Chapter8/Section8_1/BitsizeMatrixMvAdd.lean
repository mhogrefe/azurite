import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMvAdd
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Matrix.Basic

/-!
# BPR §8.1: Total degree and coefficient bitsize of a sum of two matrices
            over `ℤ[Y₁, …, Y_t]`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact: if `M, N` are sum-compatible matrices over
`A = ℤ[Y₁, …, Y_t]` whose entries have total degree in `Y` bounded by
`c` and whose coefficient bitsizes are bounded by `τ`, then the entries
of `M + N` have total degree in `Y` bounded by `c` and their coefficient
bitsizes are bounded by `τ + 1`.

The degree claim is `totalDegree (P + Q) ≤ max (totalDegree P) (totalDegree Q)`
applied entrywise. The bitsize claim is the multivariate-polynomial-sum
bitsize bound (BPR §8.1) applied entrywise.
-/

namespace Azurite.BPR

/-- **BPR §8.1 (unnumbered lemma, degree part).** Entrywise total degrees
    of a sum of two matrices over `MvPolynomial σ ℤ` are bounded by the
    common entrywise total-degree bound on the summands. -/
theorem Matrix.totalDegree_mvAdd_le {σ m n : Type _}
    {M N : Matrix m n (MvPolynomial σ ℤ)} {c : ℕ}
    (hM : ∀ i j, (M i j).totalDegree ≤ c)
    (hN : ∀ i j, (N i j).totalDegree ≤ c) :
    ∀ i j, ((M + N) i j).totalDegree ≤ c := by
  intro i j
  rw [_root_.Matrix.add_apply]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hM i j) (hN i j))

/-- **BPR §8.1 (unnumbered lemma, bitsize part).** Entrywise coefficient
    bitsizes of a sum of two matrices over `MvPolynomial σ ℤ` are bounded
    by `τ + 1` when the summands' coefficient bitsizes are bounded by `τ`. -/
theorem Matrix.bitsize_coeff_mvAdd_le {σ m n : Type _}
    {M N : Matrix m n (MvPolynomial σ ℤ)} {τ : ℕ}
    (hM : ∀ i j k, ((M i j).coeff k).natAbs.size ≤ τ)
    (hN : ∀ i j k, ((N i j).coeff k).natAbs.size ≤ τ) :
    ∀ i j k, (((M + N) i j).coeff k).natAbs.size ≤ τ + 1 := by
  intro i j k
  rw [_root_.Matrix.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact Int.size_add_le _ _ τ (hM i j k) (hN i j k)

end Azurite.BPR
