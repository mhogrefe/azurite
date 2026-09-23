/-
  Correctness of `AzMatrix.gaussRank` over a field.

  Proves `M.gaussRank = Matrix.rank M.toFn` by induction on the algorithm
  trace. The key lemmas are:

  * **Swap invariance** (`swapRows`/`swapCols`): rank is invariant under
    row and column permutation, via Mathlib's `Matrix.rank_submatrix`.
  * **Elimination invariance** (`eliminateBelow`): the operation is left-
    multiplication by an invertible matrix `E`, so by Mathlib's
    `Matrix.rank_mul_eq_right_of_isUnit_det`, rank is preserved.
  * **Block-triangular decomposition**: after `start` pivot rounds, the
    matrix has the form `[A B; 0 D]` with `A` `start × start` invertible,
    and `rank M = start + rank D`. When `D` is identically zero (no
    pivot found by `findFirstNonzero`), `rank M = start = gaussRank M`.
-/
import Azurite.AzMatrix.GaussRank
import Azurite.AzMatrix.Equiv.Det
import Azurite.AzMatrix.Equiv.RowEchelon
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.unusedSectionVars false

namespace Azurite

variable {K : Type _} [Field K] [DecidableEq K] {n : Nat}

/-! ### `toFn` of `swapRows` / `swapCols` as `Matrix.submatrix` -/

theorem AzMatrix.toFn_swapRows_eq_submatrix
    (M : AzMatrix K n n) (i₁ i₂ : Fin n) :
    (M.swapRows i₁ i₂).toFn =
      Matrix.submatrix M.toFn (Equiv.swap i₁ i₂) id := by
  funext i j
  rw [AzMatrix.toFn_swapRows]
  show (if i = i₁ then M.toFn i₂ j
        else if i = i₂ then M.toFn i₁ j
        else M.toFn i j) = M.toFn ((Equiv.swap i₁ i₂) i) j
  by_cases h₁ : i = i₁
  · rw [ite_eq_left h₁, h₁, Equiv.swap_apply_left]
  · by_cases h₂ : i = i₂
    · rw [ite_eq_right h₁, ite_eq_left h₂, h₂, Equiv.swap_apply_right]
    · rw [ite_eq_right h₁, ite_eq_right h₂, Equiv.swap_apply_of_ne_of_ne h₁ h₂]

/-! ### Rank invariance under row/column swaps -/

theorem AzMatrix.rank_swapRows (M : AzMatrix K n n) (i₁ i₂ : Fin n) :
    Matrix.rank (Matrix.of (M.swapRows i₁ i₂).toFn) =
      Matrix.rank (Matrix.of M.toFn) := by
  show Matrix.rank (M.swapRows i₁ i₂).toFn = Matrix.rank M.toFn
  rw [AzMatrix.toFn_swapRows_eq_submatrix]
  exact Matrix.rank_submatrix M.toFn (Equiv.swap i₁ i₂) (Equiv.refl _)

theorem AzMatrix.rank_swapCols (M : AzMatrix K n n) (j₁ j₂ : Fin n) :
    Matrix.rank (Matrix.of (M.swapCols j₁ j₂).toFn) =
      Matrix.rank (Matrix.of M.toFn) := by
  show Matrix.rank (M.swapCols j₁ j₂).toFn = Matrix.rank M.toFn
  rw [AzMatrix.toFn_swapCols_eq_submatrix]
  exact Matrix.rank_submatrix M.toFn (Equiv.refl _) (Equiv.swap j₁ j₂)

/-! ### Elimination matrix for `eliminateBelow`

    The matrix `M.elimMatrix k` is the lower-triangular elementary matrix
    whose only off-diagonal entries are in column `k`, below the diagonal:
    `(elimMatrix M k) i k = -M[i][k] / M[k][k]` for `k < i`.
    Multiplying `M.toFn` on the left by this matrix performs the BPR
    Algorithm 8.15 elimination step `row_i := row_i - (M[i][k]/M[k][k]) ·
    row_k` simultaneously for every `i > k`. -/
def AzMatrix.elimMatrix (M : AzMatrix K n n) (k : Fin n) :
    Matrix (Fin n) (Fin n) K :=
  fun i l =>
    if i = l then 1
    else if k.val < i.val ∧ l = k then -(M.toFn i k / M.toFn k k)
    else 0

theorem AzMatrix.elimMatrix_apply_diag (M : AzMatrix K n n) (k : Fin n)
    (i : Fin n) : M.elimMatrix k i i = 1 := by
  unfold AzMatrix.elimMatrix
  rw [ite_eq_left rfl]

theorem AzMatrix.elimMatrix_apply_of_ne (M : AzMatrix K n n) (k : Fin n)
    (i l : Fin n) (h : i ≠ l) :
    M.elimMatrix k i l =
      (if k.val < i.val ∧ l = k then -(M.toFn i k / M.toFn k k) else 0) := by
  unfold AzMatrix.elimMatrix
  rw [ite_eq_right h]

/-! ### `det` of the elimination matrix is `1` -/

theorem AzMatrix.det_elimMatrix (M : AzMatrix K n n) (k : Fin n) :
    Matrix.det (M.elimMatrix k) = 1 := by
  -- Compare `elimMatrix M k` to the identity matrix `1` row-by-row:
  -- `(elimMatrix M k) i j = 1 i j + c i * 1 k j`
  -- where `c i := if k.val < i.val then -M[i][k]/M[k][k] else 0`.
  rw [show (1 : K) = Matrix.det (1 : Matrix (Fin n) (Fin n) K) from
        Matrix.det_one.symm]
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const
    (c := fun i => if k.val < i.val then -(M.toFn i k / M.toFn k k) else 0) k
  · -- `c k = 0`
    simp
  · intro i j
    -- LHS: `(elimMatrix M k) i j`
    -- RHS: `(1 : Matrix _ _ _) i j + c i * (1 : Matrix _ _ _) k j`
    unfold AzMatrix.elimMatrix
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h_ij : i = j
    · -- Diagonal of A; RHS = 1 + c i * (1 k j)
      rw [ite_eq_left h_ij, ite_eq_left h_ij]
      by_cases h_jk : j = k
      · -- j = k, so 1 k j = 1; RHS = 1 + c i. With i = j = k, c i = c k = 0.
        rw [ite_eq_left h_jk.symm]
        subst h_ij; subst h_jk
        rw [ite_eq_right (Nat.lt_irrefl _)]
        ring
      · rw [ite_eq_right (Ne.symm h_jk)]
        ring
    · -- Off-diagonal of A: A i j = if (k < i ∧ j = k) then c_term else 0
      rw [ite_eq_right h_ij, ite_eq_right h_ij]
      by_cases h_jk : j = k
      · -- j = k, so 1 k j = 1, RHS = 0 + c i * 1 = c i
        have h_kj : k = j := h_jk.symm
        rw [ite_eq_left h_kj]
        by_cases h_ki : k.val < i.val
        · rw [ite_eq_left (And.intro h_ki h_jk), ite_eq_left h_ki]
          ring
        · have h_neg : ¬ (k.val < i.val ∧ j = k) := fun ⟨h, _⟩ => h_ki h
          rw [ite_eq_right h_neg, ite_eq_right h_ki]
          ring
      · -- j ≠ k, so 1 k j = 0, RHS = 0 + c i * 0 = 0
        have h_kj_ne : k ≠ j := fun h => h_jk h.symm
        rw [ite_eq_right h_kj_ne]
        have h_neg : ¬ (k.val < i.val ∧ j = k) := fun ⟨_, h⟩ => h_jk h
        rw [ite_eq_right h_neg]
        ring

theorem AzMatrix.isUnit_det_elimMatrix (M : AzMatrix K n n) (k : Fin n) :
    IsUnit (Matrix.det (M.elimMatrix k)) := by
  rw [M.det_elimMatrix k]
  exact isUnit_one

/-! ### `eliminateBelow` factors through `elimMatrix` -/

/-- When the pivot `M[k][k]` is nonzero and row `k` is already zero to
    the left of the diagonal (the `PartialZero` invariant at step `k.val`),
    `eliminateBelow M k` is exactly `(elimMatrix M k) * M.toFn`. -/
theorem AzMatrix.toFn_eliminateBelow_eq_elimMatrix_mul
    (M : AzMatrix K n n) (k : Fin n)
    (h_pivot : M.toFn k k ≠ 0)
    (h_row : ∀ j : Fin n, j.val < k.val → M.toFn k j = 0) :
    Matrix.of (M.eliminateBelow k).toFn =
      M.elimMatrix k * Matrix.of M.toFn := by
  funext i j
  rw [Matrix.of_apply, AzMatrix.toFn_eliminateBelow, Matrix.mul_apply]
  simp only [Matrix.of_apply]
  -- Compute the sum `∑ l, (elimMatrix M k) i l * M.toFn l j`. It has the
  -- diagonal contribution `1 * M.toFn i j` and, when `k < i`, the column-`k`
  -- contribution `(-M[i][k]/M[k][k]) * M[k][j]`. All other terms vanish.
  by_cases h_ile : i.val ≤ k.val
  · -- i ≤ k: only the diagonal term contributes (since `k < i` is false).
    rw [ite_eq_left h_ile]
    rw [Finset.sum_eq_single i]
    · rw [M.elimMatrix_apply_diag k i, one_mul]
    · intro l _ h_li
      rw [M.elimMatrix_apply_of_ne k i l (Ne.symm h_li)]
      have h_neg : ¬ (k.val < i.val ∧ l = k) := by
        intro ⟨h, _⟩
        omega
      rw [ite_eq_right h_neg, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · -- i > k: diagonal `M[i][j]` plus column-`k` term `c * M[k][j]`.
    rw [ite_eq_right h_ile]
    have h_ki : k.val < i.val := by omega
    have h_ik_ne : i ≠ k := by
      intro h; rw [h] at h_ki; exact Nat.lt_irrefl _ h_ki
    -- Isolate the `l = i` term, then the `l = k` term within the remainder.
    -- Simplify the RHS sum to a closed form in M.toFn entries.
    have h_sum :
        ∑ l, M.elimMatrix k i l * M.toFn l j =
          M.toFn i j + -(M.toFn i k / M.toFn k k) * M.toFn k j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      rw [M.elimMatrix_apply_diag k i, one_mul]
      rw [← Finset.add_sum_erase _ _
            (Finset.mem_erase.mpr ⟨Ne.symm h_ik_ne, Finset.mem_univ k⟩)]
      rw [M.elimMatrix_apply_of_ne k i k h_ik_ne]
      have h_elim_k : (if k.val < i.val ∧ k = k then
            -(M.toFn i k / M.toFn k k) else 0) =
          -(M.toFn i k / M.toFn k k) := ite_eq_left ⟨h_ki, rfl⟩
      rw [h_elim_k]
      have h_rest :
          ∑ l ∈ (Finset.univ.erase i).erase k,
            M.elimMatrix k i l * M.toFn l j = 0 := by
        apply Finset.sum_eq_zero
        intro l h_l
        rw [Finset.mem_erase, Finset.mem_erase] at h_l
        obtain ⟨h_lk, h_li, _⟩ := h_l
        rw [M.elimMatrix_apply_of_ne k i l (Ne.symm h_li)]
        have h_neg : ¬ (k.val < i.val ∧ l = k) := fun ⟨_, h⟩ => h_lk h
        rw [ite_eq_right h_neg, zero_mul]
      rw [h_rest, add_zero]
    rw [h_sum]
    -- Goal: (case-split on j) = M[i][j] + (-M[i][k]/M[k][k]) * M[k][j].
    by_cases h_jk_lt : j.val < k.val
    · rw [ite_eq_left h_jk_lt]
      rw [h_row j h_jk_lt]; ring
    · rw [ite_eq_right h_jk_lt]
      by_cases h_jk : j = k
      · rw [ite_eq_left h_jk]
        subst h_jk
        field_simp; ring
      · rw [ite_eq_right h_jk]; ring

/-! ### Rank invariance under `eliminateBelow` -/

theorem AzMatrix.rank_eliminateBelow
    (M : AzMatrix K n n) (k : Fin n)
    (h_pivot : M.toFn k k ≠ 0)
    (h_row : ∀ j : Fin n, j.val < k.val → M.toFn k j = 0) :
    Matrix.rank (Matrix.of (M.eliminateBelow k).toFn) =
      Matrix.rank (Matrix.of M.toFn) := by
  rw [M.toFn_eliminateBelow_eq_elimMatrix_mul k h_pivot h_row]
  exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ (M.isUnit_det_elimMatrix k)

/-! ### Block-triangular rank decomposition

    After `start` pivot rounds, the matrix has the form `[A ⋆; 0 0]`
    where `A` is `start × start` upper triangular with nonzero diagonal,
    so `A` is invertible. We extract this structure and conclude
    `rank M = start`. -/

/-- The leading `start × start` submatrix, viewed as a `Matrix (Fin start)
    (Fin start) K`. -/
def AzMatrix.leadingBlock (M : AzMatrix K n n) (start : Nat) (h : start ≤ n) :
    Matrix (Fin start) (Fin start) K :=
  fun i j => M.toFn (Fin.castLE h i) (Fin.castLE h j)

/-- Under `PartialZero M start`, the leading block is upper triangular
    (in Mathlib's `BlockTriangular id` sense: entries `(i, j)` with `j < i`
    vanish). -/
theorem AzMatrix.leadingBlock_blockTriangular
    (M : AzMatrix K n n) (start : Nat) (h : start ≤ n)
    (h_partial : M.PartialZero start) :
    (M.leadingBlock start h).BlockTriangular id := by
  intro i j h_lt
  unfold AzMatrix.leadingBlock
  apply h_partial
  · show (Fin.castLE h j).val < (Fin.castLE h i).val
    rw [Fin.val_castLE, Fin.val_castLE]
    exact h_lt
  · show (Fin.castLE h j).val < start
    rw [Fin.val_castLE]
    exact j.isLt

/-- Under the pivot-nonzero hypothesis, the diagonal of the leading block
    is entirely nonzero, so its determinant is nonzero. -/
theorem AzMatrix.det_leadingBlock_ne_zero
    (M : AzMatrix K n n) (start : Nat) (h : start ≤ n)
    (h_partial : M.PartialZero start)
    (h_diag : ∀ i : Fin n, i.val < start → M.toFn i i ≠ 0) :
    Matrix.det (M.leadingBlock start h) ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular
        (M.leadingBlock_blockTriangular start h h_partial)]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  show M.toFn (Fin.castLE h i) (Fin.castLE h i) ≠ 0
  exact h_diag _ (by rw [Fin.val_castLE]; exact i.isLt)

theorem AzMatrix.isUnit_leadingBlock
    (M : AzMatrix K n n) (start : Nat) (h : start ≤ n)
    (h_partial : M.PartialZero start)
    (h_diag : ∀ i : Fin n, i.val < start → M.toFn i i ≠ 0) :
    IsUnit (M.leadingBlock start h) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr
      (M.det_leadingBlock_ne_zero start h h_partial h_diag))

theorem AzMatrix.rank_leadingBlock_eq
    (M : AzMatrix K n n) (start : Nat) (h : start ≤ n)
    (h_partial : M.PartialZero start)
    (h_diag : ∀ i : Fin n, i.val < start → M.toFn i i ≠ 0) :
    Matrix.rank (M.leadingBlock start h) = start := by
  have h_rank : Matrix.rank (M.leadingBlock start h) = Fintype.card (Fin start) :=
    Matrix.rank_of_isUnit _ (M.isUnit_leadingBlock start h h_partial h_diag)
  rw [h_rank, Fintype.card_fin]

/-- The leading block is a submatrix of `Matrix.of M.toFn`, so the rank
    inequality propagates: `rank (Matrix.of M.toFn) ≥ start`. -/
theorem AzMatrix.rank_ge_start
    (M : AzMatrix K n n) (start : Nat) (h : start ≤ n)
    (h_partial : M.PartialZero start)
    (h_diag : ∀ i : Fin n, i.val < start → M.toFn i i ≠ 0) :
    start ≤ Matrix.rank (Matrix.of M.toFn) := by
  rw [← M.rank_leadingBlock_eq start h h_partial h_diag]
  -- `leadingBlock` is exactly `(Matrix.of M.toFn).submatrix (Fin.castLE h) (Fin.castLE h)`.
  have : M.leadingBlock start h =
      (Matrix.of M.toFn).submatrix (Fin.castLE h) (Fin.castLE h) := by
    funext i j; rfl
  rw [this]
  exact Matrix.rank_submatrix_le _ _ _

/-! ### Upper bound: rank ≤ start when rows ≥ start vanish -/

/-- If rows `i ≥ start` of `M` are all zero, the rank is bounded by `start`. -/
theorem AzMatrix.rank_le_start_of_rows_zero
    (M : AzMatrix K n n) (start : Nat) (h : start ≤ n)
    (h_zero : ∀ i : Fin n, start ≤ i.val →
      ∀ j : Fin n, M.toFn i j = 0) :
    Matrix.rank (Matrix.of M.toFn) ≤ start := by
  -- Use `rank_eq_finrank_span_row`. The row span is contained in the
  -- subspace spanned by the first `start` rows.
  rw [Matrix.rank_eq_finrank_span_row]
  -- We bound the span by `Submodule.span K (M.row '' { i | i.val < start })`.
  have h_subset :
      Set.range (Matrix.of M.toFn).row ⊆
        (Matrix.of M.toFn).row '' { i : Fin n | i.val < start } ∪ {0} := by
    rintro v ⟨i, rfl⟩
    by_cases h_i : i.val < start
    · left; exact ⟨i, h_i, rfl⟩
    · right
      simp only [Set.mem_singleton_iff]
      funext j
      exact h_zero i (Nat.le_of_not_lt h_i) j
  have h_span_le :
      Submodule.span K (Set.range (Matrix.of M.toFn).row) ≤
        Submodule.span K
          ((Matrix.of M.toFn).row '' { i : Fin n | i.val < start }) := by
    refine Submodule.span_le.mpr (h_subset.trans ?_)
    rintro v (hv | hv)
    · exact Submodule.subset_span hv
    · simp only [Set.mem_singleton_iff] at hv
      rw [hv]; exact Submodule.zero_mem _
  refine (Submodule.finrank_mono h_span_le).trans ?_
  -- The span of `M.row '' { i | i.val < start }` is the span of the image
  -- of `M.row ∘ Fin.castLE h`. Its dimension is at most `Fintype.card (Fin start) = start`.
  have h_eq :
      (Matrix.of M.toFn).row '' { i : Fin n | i.val < start } =
        Set.range ((Matrix.of M.toFn).row ∘ Fin.castLE h) := by
    ext v
    constructor
    · rintro ⟨i, h_i, rfl⟩
      exact ⟨⟨i.val, h_i⟩, by simp [Fin.castLE, Fin.eta]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨Fin.castLE h i, ?_, rfl⟩
      show (Fin.castLE h i).val < start
      rw [Fin.val_castLE]
      exact i.isLt
  rw [h_eq]
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_range]
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, Fintype.card_fin]

/-! ### Spec lemmas for `findFirstNonzero` -/

theorem AzMatrix.findFirstNonzeroAux_eq_none
    (M : AzMatrix K n n) (c_start : Nat) :
    ∀ (i : Nat), M.findFirstNonzeroAux i c_start = none →
      ∀ i' j' : Fin n, i ≤ i'.val → c_start ≤ j'.val →
        M.toFn i' j' = 0 := by
  intro i
  apply AzMatrix.findFirstNonzeroAux.induct M c_start
    (motive := fun i =>
      M.findFirstNonzeroAux i c_start = none →
        ∀ i' j' : Fin n, i ≤ i'.val → c_start ≤ j'.val →
          M.toFn i' j' = 0)
  · -- case: i < n, found `some j` (so output = some, not none — contradiction)
    intro i h_lt j h_match h_rec
    exfalso
    rw [AzMatrix.findFirstNonzeroAux.eq_def] at h_rec
    simp [h_lt, h_match] at h_rec
  · -- case: i < n, findPivotAux returned none, recurse on i + 1
    intro i h_lt h_match ih h_rec i' j' h_i'_ge h_j'_ge
    have h_row_zero : M.toFn ⟨i, h_lt⟩ j' = 0 :=
      M.findPivotAux_eq_none ⟨i, h_lt⟩ c_start h_match j' h_j'_ge
    have h_rec_eq : M.findFirstNonzeroAux (i + 1) c_start = none := by
      rw [AzMatrix.findFirstNonzeroAux.eq_def] at h_rec
      simp only [dite_eq_left h_lt, h_match] at h_rec
      exact h_rec
    by_cases h_i'_eq : i'.val = i
    · have : i' = ⟨i, h_lt⟩ := Fin.ext h_i'_eq
      rw [this]; exact h_row_zero
    · exact ih h_rec_eq i' j' (by omega) h_j'_ge
  · -- case: i ≥ n, vacuously true since no i' : Fin n has i ≤ i'.val
    intro i h_ge _ i' _ h_i'_ge _
    have : i'.val < n := i'.isLt
    omega

theorem AzMatrix.findFirstNonzero_eq_none
    (M : AzMatrix K n n) (r_start c_start : Nat)
    (h : M.findFirstNonzero r_start c_start = none) :
    ∀ i j : Fin n, r_start ≤ i.val → c_start ≤ j.val →
      M.toFn i j = 0 :=
  M.findFirstNonzeroAux_eq_none c_start r_start h

theorem AzMatrix.findFirstNonzeroAux_some_mem
    (M : AzMatrix K n n) (c_start : Nat) :
    ∀ (i : Nat) (i' j' : Fin n),
      M.findFirstNonzeroAux i c_start = some (i', j') →
        i ≤ i'.val ∧ c_start ≤ j'.val ∧ M.toFn i' j' ≠ 0 := by
  intro i i' j'
  apply AzMatrix.findFirstNonzeroAux.induct M c_start
    (motive := fun i => ∀ i' j' : Fin n,
      M.findFirstNonzeroAux i c_start = some (i', j') →
        i ≤ i'.val ∧ c_start ≤ j'.val ∧ M.toFn i' j' ≠ 0)
  · -- case: i < n, findPivotAux returns `some j`, output is `some (⟨i, _⟩, j)`
    intro i h_lt j h_match i' j' h_rec
    rw [AzMatrix.findFirstNonzeroAux.eq_def] at h_rec
    simp only [dite_eq_left h_lt, h_match, Option.some.injEq, Prod.mk.injEq] at h_rec
    obtain ⟨h_i', h_j'⟩ := h_rec
    refine ⟨?_, ?_, ?_⟩
    · rw [← h_i']
    · rw [← h_j']
      exact M.findPivotAux_some_le ⟨i, h_lt⟩ c_start j h_match
    · rw [← h_i', ← h_j']
      exact M.findPivotAux_some_nonzero ⟨i, h_lt⟩ c_start j h_match
  · -- case: i < n, findPivotAux returns none, recurse
    intro i h_lt h_match ih i' j' h_rec
    have h_rec_eq : M.findFirstNonzeroAux (i + 1) c_start = some (i', j') := by
      rw [AzMatrix.findFirstNonzeroAux.eq_def] at h_rec
      simp only [dite_eq_left h_lt, h_match] at h_rec
      exact h_rec
    obtain ⟨h_a, h_b, h_c⟩ := ih i' j' h_rec_eq
    exact ⟨by omega, h_b, h_c⟩
  · -- case: i ≥ n, output is none → contradiction with some
    intro i h_ge i' j' h_rec
    exfalso
    rw [AzMatrix.findFirstNonzeroAux.eq_def] at h_rec
    simp [h_ge] at h_rec

theorem AzMatrix.findFirstNonzero_some_mem
    (M : AzMatrix K n n) (r_start c_start : Nat) (i' j' : Fin n)
    (h : M.findFirstNonzero r_start c_start = some (i', j')) :
    r_start ≤ i'.val ∧ c_start ≤ j'.val ∧ M.toFn i' j' ≠ 0 :=
  M.findFirstNonzeroAux_some_mem c_start r_start i' j' h

/-- The block-triangular rank theorem: under the partial-zero invariant
    with nonzero pivots and the lower-right submatrix being identically
    zero (the algorithm-terminates-via-`none` situation), `rank M = start`. -/
theorem AzMatrix.rank_eq_of_pivoted_zero_below
    (M : AzMatrix K n n) (start : Nat) (h : start ≤ n)
    (h_partial : M.PartialZero start)
    (h_diag : ∀ i : Fin n, i.val < start → M.toFn i i ≠ 0)
    (h_no_lower_right : ∀ i j : Fin n,
      start ≤ i.val → start ≤ j.val → M.toFn i j = 0) :
    Matrix.rank (Matrix.of M.toFn) = start := by
  -- Rows `i ≥ start` are entirely zero: for `j < start ≤ i`, PartialZero
  -- gives zero; for `j ≥ start`, the lower-right hypothesis gives zero.
  have h_rows_zero : ∀ i : Fin n, start ≤ i.val →
      ∀ j : Fin n, M.toFn i j = 0 := by
    intro i h_i j
    by_cases h_j : j.val < start
    · exact h_partial i j (Nat.lt_of_lt_of_le h_j h_i) h_j
    · exact h_no_lower_right i j h_i (Nat.le_of_not_lt h_j)
  refine le_antisymm
    (M.rank_le_start_of_rows_zero start h h_rows_zero)
    (M.rank_ge_start start h h_partial h_diag)

/-! ### Helper: rank invariance via the full pivot step

    A combined `swapRows` + `swapCols` + `eliminateBelow` step preserves
    rank. We package this for the inductive proof of correctness. -/

/-- `swapRows` preserves `PartialZero` (analogue of
    `swapCols_preservesPartialZero`): swapping a row `i ≥ start` with row
    `start` keeps the lower-left zero block at level `start` intact. -/
theorem AzMatrix.swapRows_preservesPartialZero
    (M : AzMatrix K n n) (start : Nat) (h_lt : start < n)
    (h_inv : M.PartialZero start) (iₚ : Fin n) (h_iₚ_ge : start ≤ iₚ.val) :
    (M.swapRows ⟨start, h_lt⟩ iₚ).PartialZero start := by
  intro i j h_lt_ij h_bnd
  rw [AzMatrix.toFn_swapRows]
  by_cases h_i_kp : i = ⟨start, h_lt⟩
  · -- i = kp; new row is old row iₚ. Apply PartialZero at iₚ.
    rw [ite_eq_left h_i_kp]
    apply h_inv iₚ j
    · -- j.val < iₚ.val: j.val < start ≤ iₚ.val.
      have h_j_lt : j.val < start := h_bnd
      omega
    · exact h_bnd
  · by_cases h_i_iₚ : i = iₚ
    · -- i = iₚ; new row is old row kp. Apply PartialZero at kp.
      rw [ite_eq_right h_i_kp, ite_eq_left h_i_iₚ]
      apply h_inv ⟨start, h_lt⟩ j h_bnd h_bnd
    · -- Other rows are unchanged.
      rw [ite_eq_right h_i_kp, ite_eq_right h_i_iₚ]
      exact h_inv i j h_lt_ij h_bnd

/-! ### Main correctness theorem: `gaussRank = Matrix.rank`

    The algorithm preserves a rank invariant at every step: throughout
    the recursion, the partial-zero structure and the
    nonzero-diagonal-pivots invariant are maintained, and the rank of
    the current matrix equals the rank of the original. At termination
    (`findFirstNonzero = none`), the matrix has the block-triangular
    structure required by `rank_eq_of_pivoted_zero_below`, giving the
    final rank as `start`. -/

/-! ### Diagonal preservation under swaps below `start` -/

theorem AzMatrix.swapRows_preservesDiag
    (M : AzMatrix K n n) (kp : Fin n) (iₚ : Fin n)
    (h_iₚ_ge : kp.val ≤ iₚ.val)
    (i : Fin n) (h_i_lt : i.val < kp.val) :
    (M.swapRows kp iₚ).toFn i i = M.toFn i i := by
  rw [AzMatrix.toFn_swapRows]
  have h_i_neq_kp : i ≠ kp := by
    intro h; rw [h] at h_i_lt; exact Nat.lt_irrefl _ h_i_lt
  have h_i_neq_iₚ : i ≠ iₚ := by
    intro h; rw [h] at h_i_lt; omega
  rw [ite_eq_right h_i_neq_kp, ite_eq_right h_i_neq_iₚ]

theorem AzMatrix.swapCols_preservesDiag
    (M : AzMatrix K n n) (kp : Fin n) (jₚ : Fin n)
    (h_jₚ_ge : kp.val ≤ jₚ.val)
    (i : Fin n) (h_i_lt : i.val < kp.val) :
    (M.swapCols kp jₚ).toFn i i = M.toFn i i := by
  rw [AzMatrix.toFn_swapCols]
  have h_i_neq_kp : i ≠ kp := by
    intro h; rw [h] at h_i_lt; exact Nat.lt_irrefl _ h_i_lt
  have h_i_neq_jₚ : i ≠ jₚ := by
    intro h; rw [h] at h_i_lt; omega
  rw [ite_eq_right h_i_neq_kp, ite_eq_right h_i_neq_jₚ]

theorem AzMatrix.eliminateBelow_preservesDiag
    (M : AzMatrix K n n) (kp : Fin n) (i : Fin n) (h_i_lt : i.val < kp.val) :
    (M.eliminateBelow kp).toFn i i = M.toFn i i := by
  rw [AzMatrix.toFn_eliminateBelow]
  have h_i_le_kp : i.val ≤ kp.val := Nat.le_of_lt h_i_lt
  rw [ite_eq_left h_i_le_kp]

/-! ### Main correctness: inductive proof -/

theorem AzMatrix.gaussRankAux_eq_rank
    (M : AzMatrix K n n) (start : Nat) (h_start_le : start ≤ n)
    (h_partial : M.PartialZero start)
    (h_diag : ∀ i : Fin n, i.val < start → M.toFn i i ≠ 0) :
    M.gaussRankAux start = Matrix.rank (Matrix.of M.toFn) := by
  induction h_k : n - start using Nat.strong_induction_on generalizing M start
  case _ k ih =>
    rw [AzMatrix.gaussRankAux.eq_def]
    split
    · -- Case: start + 1 < n
      rename_i h_lt
      -- Set up the pivot row index.
      set kp : Fin n := ⟨start, by omega⟩
      -- Dispatch on findFirstNonzero.
      cases h_pivot : M.findFirstNonzero start start with
      | none =>
        -- No pivot: rank = start by block-triangular decomposition.
        simp only
        symm
        apply M.rank_eq_of_pivoted_zero_below start h_start_le h_partial h_diag
        intro i j h_i_ge h_j_ge
        exact M.findFirstNonzero_eq_none start start h_pivot i j h_i_ge h_j_ge
      | some ij =>
        -- Pivot found: do the row/col swaps, eliminate, recurse.
        obtain ⟨i_p, j_p⟩ := ij
        obtain ⟨h_i_ge, h_j_ge, h_pivot_nz⟩ :=
          M.findFirstNonzero_some_mem start start i_p j_p h_pivot
        -- Define the post-swap matrices.
        set M_row := if i_p = kp then M else M.swapRows kp i_p with hM_row
        set M_swapped := if j_p = kp then M_row
          else M_row.swapCols kp j_p with hM_swapped
        set M_new := M_swapped.eliminateBelow kp with hM_new
        -- Rank: M_row and M_swapped preserve M's rank (via swap invariance).
        have h_rank_row :
            Matrix.rank (Matrix.of M_row.toFn) =
              Matrix.rank (Matrix.of M.toFn) := by
          by_cases h_eq : i_p = kp
          · rw [hM_row, ite_eq_left h_eq]
          · rw [hM_row, ite_eq_right h_eq]; exact M.rank_swapRows kp i_p
        have h_rank_swapped :
            Matrix.rank (Matrix.of M_swapped.toFn) =
              Matrix.rank (Matrix.of M.toFn) := by
          by_cases h_eq : j_p = kp
          · rw [hM_swapped, ite_eq_left h_eq]; exact h_rank_row
          · rw [hM_swapped, ite_eq_right h_eq]
            rw [M_row.rank_swapCols kp j_p]
            exact h_rank_row
        -- PartialZero is preserved by both swaps (since i_p, j_p ≥ start).
        have h_partial_row : M_row.PartialZero start := by
          by_cases h_eq : i_p = kp
          · rw [hM_row, ite_eq_left h_eq]; exact h_partial
          · rw [hM_row, ite_eq_right h_eq]
            exact M.swapRows_preservesPartialZero start (by omega) h_partial
              i_p h_i_ge
        have h_partial_swapped : M_swapped.PartialZero start := by
          by_cases h_eq : j_p = kp
          · rw [hM_swapped, ite_eq_left h_eq]; exact h_partial_row
          · rw [hM_swapped, ite_eq_right h_eq]
            exact M_row.swapCols_preservesPartialZero start (by omega)
              h_partial_row j_p h_j_ge
        -- The new diagonal pivot: M_swapped[kp][kp] = M[i_p][j_p] ≠ 0.
        have h_M_swapped_kp_kp : M_swapped.toFn kp kp = M.toFn i_p j_p := by
          -- Compute through both swap layers.
          show M_swapped.toFn kp kp = M.toFn i_p j_p
          by_cases h_jp_kp : j_p = kp
          · -- No column swap.
            rw [hM_swapped, ite_eq_left h_jp_kp]
            -- M_swapped = M_row; check M_row[kp][kp].
            by_cases h_ip_kp : i_p = kp
            · rw [hM_row, ite_eq_left h_ip_kp, h_ip_kp, h_jp_kp]
            · rw [hM_row, ite_eq_right h_ip_kp, AzMatrix.toFn_swapRows]
              rw [ite_eq_left rfl, h_jp_kp]
          · -- Column swap applies.
            rw [hM_swapped, ite_eq_right h_jp_kp, AzMatrix.toFn_swapCols]
            rw [ite_eq_left rfl]
            by_cases h_ip_kp : i_p = kp
            · rw [hM_row, ite_eq_left h_ip_kp, h_ip_kp]
            · rw [hM_row, ite_eq_right h_ip_kp, AzMatrix.toFn_swapRows]
              rw [ite_eq_left rfl]
        have h_M_swapped_kp_kp_nz : M_swapped.toFn kp kp ≠ 0 := by
          rw [h_M_swapped_kp_kp]; exact h_pivot_nz
        -- Diagonal of M_swapped: for i.val < start, M_swapped[i][i] = M[i][i].
        have h_diag_swapped : ∀ i : Fin n, i.val < start →
            M_swapped.toFn i i ≠ 0 := by
          intro i h_i_lt
          have h_row_eq : M_row.toFn i i = M.toFn i i := by
            by_cases h_eq : i_p = kp
            · rw [hM_row, ite_eq_left h_eq]
            · rw [hM_row, ite_eq_right h_eq]
              exact M.swapRows_preservesDiag kp i_p h_i_ge i
                (by show i.val < kp.val; exact h_i_lt)
          have h_swapped_eq : M_swapped.toFn i i = M_row.toFn i i := by
            by_cases h_eq : j_p = kp
            · rw [hM_swapped, ite_eq_left h_eq]
            · rw [hM_swapped, ite_eq_right h_eq]
              exact M_row.swapCols_preservesDiag kp j_p h_j_ge i
                (by show i.val < kp.val; exact h_i_lt)
          rw [h_swapped_eq, h_row_eq]
          exact h_diag i h_i_lt
        -- The eliminate step extends PartialZero and preserves rank.
        have h_partial_new : M_new.PartialZero (start + 1) := by
          rw [hM_new]
          exact M_swapped.eliminateBelow_preservesPartialZero start
            (by omega) h_partial_swapped
        have h_rank_new :
            Matrix.rank (Matrix.of M_new.toFn) =
              Matrix.rank (Matrix.of M.toFn) := by
          rw [hM_new]
          rw [M_swapped.rank_eliminateBelow kp h_M_swapped_kp_kp_nz]
          · exact h_rank_swapped
          · intro j h_j_lt
            have h_kp_val : kp.val = start := rfl
            exact h_partial_swapped kp j (by omega) (by omega)
        -- Diagonal of M_new at index start = kp.val.
        have h_M_new_kp_kp : M_new.toFn kp kp = M_swapped.toFn kp kp := by
          rw [hM_new, AzMatrix.toFn_eliminateBelow]
          rw [ite_eq_left (le_refl _)]
        have h_diag_new : ∀ i : Fin n, i.val < start + 1 →
            M_new.toFn i i ≠ 0 := by
          intro i h_i_lt
          by_cases h_i_eq : i.val = start
          · -- i = kp
            have h_i_eq_kp : i = kp := Fin.ext h_i_eq
            rw [h_i_eq_kp, h_M_new_kp_kp]
            exact h_M_swapped_kp_kp_nz
          · -- i.val < start
            have h_i_lt' : i.val < start := by omega
            rw [hM_new]
            rw [M_swapped.eliminateBelow_preservesDiag kp i
                  (by show i.val < kp.val; exact h_i_lt')]
            exact h_diag_swapped i h_i_lt'
        -- Apply IH at start + 1.
        have h_start_le' : start + 1 ≤ n := by omega
        have h_dec : n - (start + 1) < k := by omega
        change M_new.gaussRankAux (start + 1) = (Matrix.of M.toFn).rank
        rw [ih (n - (start + 1)) h_dec M_new (start + 1) h_start_le'
              h_partial_new h_diag_new rfl]
        exact h_rank_new
    · -- Case: start + 1 ≥ n (terminal step).
      rename_i h_ge
      split
      · rename_i hn
        set kp_last : Fin n := ⟨n - 1, by omega⟩
        cases h_pivot : M.findFirstNonzero (n - 1) (n - 1) with
        | none =>
          simp only
          symm
          -- After (n-1) steps, rank = n - 1 when last position is zero.
          have h_partial' : M.PartialZero (n - 1) := by
            intro i j h_lt_ij h_bnd
            exact h_partial i j h_lt_ij (by omega)
          have h_diag' : ∀ i : Fin n, i.val < n - 1 → M.toFn i i ≠ 0 := by
            intro i h_i
            exact h_diag i (by omega)
          apply M.rank_eq_of_pivoted_zero_below (n - 1) (by omega)
            h_partial' h_diag'
          intro i j h_i_ge h_j_ge
          exact M.findFirstNonzero_eq_none (n - 1) (n - 1) h_pivot i j
            h_i_ge h_j_ge
        | some ij =>
          obtain ⟨i_p, j_p⟩ := ij
          obtain ⟨h_i_ge, h_j_ge, h_pivot_nz⟩ :=
            M.findFirstNonzero_some_mem (n - 1) (n - 1) i_p j_p h_pivot
          -- i_p, j_p : Fin n with i_p.val ≥ n-1 and j_p.val ≥ n-1, hence
          -- i_p.val = j_p.val = n - 1.
          have h_ip : i_p.val = n - 1 := by
            have : i_p.val < n := i_p.isLt; omega
          have h_jp : j_p.val = n - 1 := by
            have : j_p.val < n := j_p.isLt; omega
          have h_kp_last_eq_ip : kp_last = i_p := Fin.ext h_ip.symm
          have h_kp_last_eq_jp : kp_last = j_p := Fin.ext h_jp.symm
          simp only
          symm
          -- After verifying full pivots: rank = n.
          -- Apply rank_eq_of_pivoted_zero_below with start = n. The
          -- diag-nonzero needs to extend to index n - 1.
          have h_diag_full : ∀ i : Fin n, i.val < n → M.toFn i i ≠ 0 := by
            intro i h_i_lt
            by_cases h_i_lt' : i.val < start
            · exact h_diag i h_i_lt'
            · have h_i_val : i.val = n - 1 := by omega
              have h_i_eq_ip : i = i_p := Fin.ext (h_i_val.trans h_ip.symm)
              have h_i_eq_jp : i = j_p := Fin.ext (h_i_val.trans h_jp.symm)
              have h_pt : M.toFn i i = M.toFn i_p j_p := by
                rw [h_i_eq_ip]
                congr 1
                exact (h_i_eq_ip.symm.trans h_i_eq_jp)
              rw [h_pt]
              exact h_pivot_nz
          have h_partial_full : M.PartialZero n := by
            intro i j h_lt_ij _
            by_cases h_j_lt_start : j.val < start
            · exact h_partial i j h_lt_ij h_j_lt_start
            · have h_i_lt : i.val < n := i.isLt
              have h_j_lt : j.val < n := j.isLt
              omega
          apply M.rank_eq_of_pivoted_zero_below n (le_refl _)
            h_partial_full h_diag_full
          intro i j h_i_ge _
          have : i.val < n := i.isLt; omega
      · -- n = 0
        rename_i h_zero_not
        push Not at h_zero_not
        have h_n_eq : n = 0 := Nat.le_zero.mp h_zero_not
        subst h_n_eq
        -- rank of 0 × 0 matrix is 0.
        symm
        rw [show Matrix.of M.toFn = (0 : Matrix (Fin 0) (Fin 0) K) from ?_]
        · exact Matrix.rank_zero
        · funext i
          exact i.elim0

theorem AzMatrix.gaussRank_eq_rank (M : AzMatrix K n n) :
    M.gaussRank = Matrix.rank (Matrix.of M.toFn) := by
  refine AzMatrix.gaussRankAux_eq_rank M 0 (Nat.zero_le _) ?_ ?_
  · intro _ _ _ h
    exact absurd h (Nat.not_lt_zero _)
  · intro _ h
    exact absurd h (Nat.not_lt_zero _)

end Azurite
