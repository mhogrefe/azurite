import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMvMul
import Mathlib.Data.Matrix.Mul

/-!
# BPR §8.1: Bitsize of a product of two matrices

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact: if `M : Matrix l m ℤ` and `N : Matrix m n ℤ`
have entry bitsizes bounded by `τ` and `σ` respectively, then every
entry of `M * N` has bitsize `≤ τ + σ + bit(card m)`.

Proof: each entry `(M * N) i k = ∑ j, M i j * N j k` is a sum of
`card m` integer products; each product has bitsize `≤ τ + σ`
(`Int.size_mul_le`), and the bitsize of a Finset sum of bounded
integers picks up `Nat.size` of the index-set cardinality
(`Int.size_finset_sum_le`).
-/

namespace Azurite.BPR

/-- **BPR §8.1 (unnumbered lemma).** Multiplying two matrices over `ℤ`
    whose entry bitsizes are bounded by `τ` and `σ` respectively
    produces a matrix whose entry bitsizes are bounded by
    `τ + σ + Nat.size (Fintype.card m)`, where `m` is the shared
    middle dimension. -/
theorem Matrix.bitsize_mul_le {l m n : Type _} [Fintype m]
    {M : Matrix l m ℤ} {N : Matrix m n ℤ} {τ σ : ℕ}
    (hM : ∀ i j, (M i j).natAbs.size ≤ τ)
    (hN : ∀ i j, (N i j).natAbs.size ≤ σ) :
    ∀ i k, ((M * N) i k).natAbs.size ≤ τ + σ + Nat.size (Fintype.card m) := by
  intro i k
  rw [_root_.Matrix.mul_apply, ← Finset.card_univ]
  exact Int.size_finset_sum_le
    (fun j _ => Int.size_mul_le _ _ τ σ (hM i j) (hN j k))

end Azurite.BPR
