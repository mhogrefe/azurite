import Azurite.BasuPollackRoy.Chapter4.Section4_1.VandermondeMatrix

/-!
# BPR Lemma 4.11: Vandermonde determinant formula

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

`det(V(x_1, …, x_r)) = ∏_{r ≥ i > j ≥ 1} (x_i - x_j)`.

In Mathlib's `Fin`-indexed form: `∏ i, ∏ j ∈ Finset.Ioi i, (x j - x i)`,
which iterates over pairs `(i, j)` with `i < j` and contributes
`x_j - x_i`. This is the same as BPR's product over `i > j` of
`x_i - x_j` after swapping `i ↔ j`.

The proof leverages Mathlib's `Matrix.det_vandermonde` directly,
combined with `vandermondeDet_eq_mathlib` to bridge BPR's column-by-
element convention to Mathlib's row-by-element convention.
-/

namespace Azurite.BPR.Chapter4

open Matrix

variable {R : Type*} [CommRing R]

/-- **BPR Lemma 4.11**. The Vandermonde determinant factors as
    `∏ over (i, j) with i < j of (x_j - x_i)`. -/
theorem lemma_4_11 {r : ℕ} (x : Fin r → R) :
    vandermondeDet x = ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x j - x i) := by
  rw [vandermondeDet_eq_mathlib]
  exact Matrix.det_vandermonde x

end Azurite.BPR.Chapter4
