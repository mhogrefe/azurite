import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Division-free determinant by cofactor expansion

`detFn n M` computes the determinant of the `n × n` matrix given by the
entry function `M : ℕ → ℕ → S` by Laplace expansion along the first row —
**no division at all**, so it is valid over an arbitrary commutative ring
(BPR Remark 8.23's fallback route; contrast the Bareiss algorithm, which is
*fraction-free* but not *division-free*: it performs exact divisions by
previous pivots and therefore needs an integral domain with exact division).

The cost is `O(n!)` ring operations: this is a correctness-first fallback,
not a performance algorithm (Berkowitz's `O(n⁴)` division-free method is the
upgrade path). Correctness: `detFn_eq_det` identifies it with `Matrix.det`
for any entry function agreeing with the matrix on the index square.
-/

namespace Azurite

variable {S : Type _} [CommRing S]

/-- Determinant of the `n × n` matrix with entries `M i j`
(`0 ≤ i, j < n`), by cofactor expansion along the first row. Division-free:
valid over any commutative ring. `O(n!)`. -/
def detFn : (n : ℕ) → (M : ℕ → ℕ → S) → S
  | 0, _ => 1
  | n + 1, M =>
    (List.range (n + 1)).foldl
      (fun acc j =>
        acc + (-1) ^ j * M 0 j
          * detFn n (fun r c => M (r + 1) (if c < j then c else c + 1))) 0

/-- Additive fold over `List.range` is the `Finset.range` sum. -/
private theorem foldl_range_add {n : ℕ} (f : ℕ → S) :
    (List.range n).foldl (fun acc j => acc + f j) 0 = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Finset.sum_range_succ]

/-- **Correctness of the expansion determinant**: `detFn n M` computes
`Matrix.det A` whenever `M` agrees with `A` on the index square. -/
theorem detFn_eq_det : ∀ (n : ℕ) (M : ℕ → ℕ → S) (A : Matrix (Fin n) (Fin n) S),
    (∀ (i j : ℕ) (hi : i < n) (hj : j < n), M i j = A ⟨i, hi⟩ ⟨j, hj⟩) →
    detFn n M = A.det
  | 0, _, A, _ => by rw [Matrix.det_fin_zero]; rfl
  | n + 1, M, A, h => by
    rw [Matrix.det_succ_row_zero, detFn, foldl_range_add
      (f := fun j => (-1) ^ j * M 0 j
        * detFn n (fun r c => M (r + 1) (if c < j then c else c + 1))),
      ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [h 0 j (by omega) j.isLt]
    have h0 : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
    rw [h0]
    congr 1
    -- the recursive minor agrees with `submatrix Fin.succ j.succAbove`
    refine detFn_eq_det n _ (A.submatrix Fin.succ j.succAbove) ?_
    intro r c hr hc
    simp only [Matrix.submatrix_apply]
    rcases Nat.lt_or_ge c (j : ℕ) with hcj | hcj
    · rw [if_pos hcj, h (r + 1) c (by omega) (by omega)]
      congr 1
      apply Fin.ext
      simp only [Fin.succAbove]
      rw [if_pos (by
        simp only [Fin.lt_def, Fin.val_castSucc]
        omega)]
      rfl
    · rw [if_neg (by omega), h (r + 1) (c + 1) (by omega) (by omega)]
      congr 1
      apply Fin.ext
      simp only [Fin.succAbove]
      rw [if_neg (by
        simp only [Fin.lt_def, Fin.val_castSucc]
        omega)]
      rfl

/-- `detFn` commutes with ring homomorphisms. -/
theorem map_detFn {T : Type _} [CommRing T] (f : S →+* T) :
    ∀ (n : ℕ) (M : ℕ → ℕ → S), f (detFn n M) = detFn n (fun i j => f (M i j))
  | 0, _ => by rw [detFn, detFn, map_one]
  | n + 1, M => by
    rw [detFn, detFn]
    -- push `f` through the additive fold
    have hfold : ∀ (l : List ℕ) (acc : S),
        f (l.foldl (fun a j => a + (-1) ^ j * M 0 j
            * detFn n (fun r c => M (r + 1) (if c < j then c else c + 1))) acc)
          = l.foldl (fun a j => a + (-1) ^ j * f (M 0 j)
            * detFn n (fun r c => f (M (r + 1) (if c < j then c else c + 1)))) (f acc) := by
      intro l
      induction l with
      | nil => intro acc; rfl
      | cons x xs ih =>
        intro acc
        rw [List.foldl_cons, List.foldl_cons, ih, map_add, map_mul, map_mul, map_pow,
          map_neg, map_one, map_detFn f n]
    rw [hfold, map_zero]

end Azurite
