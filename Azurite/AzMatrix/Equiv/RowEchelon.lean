/-
  Equivalence proof: `AzMatrix.rowEchelon` produces an upper-triangular
  matrix in the sense of Mathlib's `Matrix.BlockTriangular id`.
-/
import Azurite.AzMatrix.RowEchelon
import Mathlib.LinearAlgebra.Matrix.Block

namespace Azurite

variable {K : Type _} {n : Nat}

/-! ### Unfolding lemmas for `eliminateBelow` and `swapRows` -/

theorem AzMatrix.toFn_eliminateBelow [Field K]
    (M : AzMatrix K n n) (k i j : Fin n) :
    (M.eliminateBelow k).toFn i j =
      (if i.val ≤ k.val then M.toFn i j
       else if j.val < k.val then M.toFn i j
       else if j = k then 0
       else M.toFn i j - (M.toFn i k / M.toFn k k) * M.toFn k j) := by
  unfold AzMatrix.eliminateBelow
  rw [AzMatrix.toFn_ofFn]
  rfl

theorem AzMatrix.toFn_swapRows (M : AzMatrix K n n) (i₁ i₂ i j : Fin n) :
    (M.swapRows i₁ i₂).toFn i j =
      (if i = i₁ then M.toFn i₂ j
       else if i = i₂ then M.toFn i₁ j
       else M.toFn i j) := by
  unfold AzMatrix.swapRows
  rw [AzMatrix.toFn_ofFn]
  rfl

/-! ### Behavior of `findRowPivot` -/

/-- Helper: if `findRowPivotAux M k start = none`, then `M[i][k] = 0` for every
    row `i ≥ start`. -/
theorem AzMatrix.findRowPivotAux_eq_none [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (k : Fin n) :
    ∀ (start : Nat), M.findRowPivotAux k start = none →
      ∀ i : Fin n, start ≤ i.val → M.toFn i k = 0 := by
  apply AzMatrix.findRowPivotAux.induct M k
    (motive := fun start => M.findRowPivotAux k start = none →
      ∀ i : Fin n, start ≤ i.val → M.toFn i k = 0)
  · -- case 1: start < n and M[start][k] = 0
    intro start h_lt h_zero ih h_rec i h_ge
    have hrec_eq : M.findRowPivotAux k (start + 1) = none := by
      rw [AzMatrix.findRowPivotAux.eq_def] at h_rec
      simp only [dite_eq_left h_lt, ite_eq_left h_zero] at h_rec
      exact h_rec
    by_cases h_eq : i.val = start
    · have hi : i = ⟨start, h_lt⟩ := Fin.ext h_eq
      rw [hi]
      exact h_zero
    · exact ih hrec_eq i (by omega)
  · -- case 2: start < n and M[start][k] ≠ 0
    intro start h_lt h_nz h_rec
    have h_eq : M.findRowPivotAux k start = some ⟨start, h_lt⟩ := by
      rw [AzMatrix.findRowPivotAux.eq_def]
      simp only [dite_eq_left h_lt, ite_eq_right h_nz]
    rw [h_eq] at h_rec
    nomatch h_rec
  · -- case 3: start ≥ n
    intro start h_ge _ i _
    have : i.val < n := i.isLt
    omega

/-- If `findRowPivot M k = none`, then `M[i][k] = 0` for every row `i ≥ k`. -/
theorem AzMatrix.findRowPivot_eq_none [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (k : Fin n) (h : M.findRowPivot k = none) :
    ∀ i : Fin n, k.val ≤ i.val → M.toFn i k = 0 :=
  M.findRowPivotAux_eq_none k k.val h

/-- If `findRowPivot M k = some j`, then `k ≤ j` (the pivot is at or below
    the diagonal row). -/
theorem AzMatrix.findRowPivotAux_some_le [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (k : Fin n) :
    ∀ (start : Nat) (j : Fin n),
      M.findRowPivotAux k start = some j → start ≤ j.val := by
  intro start
  apply AzMatrix.findRowPivotAux.induct M k
    (motive := fun start => ∀ j : Fin n,
      M.findRowPivotAux k start = some j → start ≤ j.val)
  · intro start h_lt h_zero ih j h_rec
    have hrec_eq : M.findRowPivotAux k (start + 1) = some j := by
      rw [AzMatrix.findRowPivotAux.eq_def] at h_rec
      simp only [dite_eq_left h_lt, ite_eq_left h_zero] at h_rec
      exact h_rec
    have := ih j hrec_eq
    omega
  · intro start h_lt h_nz j h_rec
    have h_eq : M.findRowPivotAux k start = some ⟨start, h_lt⟩ := by
      rw [AzMatrix.findRowPivotAux.eq_def]
      simp only [dite_eq_left h_lt, ite_eq_right h_nz]
    rw [h_eq] at h_rec
    have h_eq_j : ⟨start, h_lt⟩ = j := by injection h_rec
    have : j.val = start := by rw [← h_eq_j]
    omega
  · intro start h_ge j h_rec
    rw [AzMatrix.findRowPivotAux.eq_def] at h_rec
    simp only [dite_eq_right h_ge] at h_rec
    nomatch h_rec

/-- If `findRowPivot M k = some j`, then `k ≤ j`. -/
theorem AzMatrix.findRowPivot_some_le [Zero K] [DecidableEq K]
    (M : AzMatrix K n n) (k j : Fin n) (h : M.findRowPivot k = some j) :
    k.val ≤ j.val :=
  M.findRowPivotAux_some_le k k.val j h

/-! ### Main result: `rowEchelon` produces an upper-triangular matrix -/

/-- The recursive helper preserves the partial-zero invariant. After running
    `rowEchelonAux M start s` starting from an `M` whose entries below
    the diagonal are zero in columns `< start`, the output's entries below
    the diagonal are zero everywhere. -/
theorem AzMatrix.rowEchelonAux_blockTriangular [Field K] [DecidableEq K]
    (M : AzMatrix K n n) (start s : Nat)
    (h_inv : ∀ i j : Fin n, j.val < i.val → j.val < start → M.toFn i j = 0) :
    ∀ i j : Fin n, j.val < i.val →
      (M.rowEchelonAux start s).1.toFn i j = 0 := by
  induction M, start, s using AzMatrix.rowEchelonAux.induct with
  | case1 M start s h_lt kp h_none ih =>
    -- No pivot in column `start` at or below row `start`; the column is
    -- already zero below the diagonal there.
    have h_kp_val : kp.val = start := rfl
    -- Reformulate `h_none` to match the goal's syntactic form
    have h_none' : M.findRowPivot ⟨start, by omega⟩ = none := h_none
    have h_inv' : ∀ i' j' : Fin n, j'.val < i'.val → j'.val < start + 1 →
        M.toFn i' j' = 0 := by
      intro i' j' h_lt_ij' h_bnd
      by_cases h_j_start : j'.val = start
      · have h_j_eq : j' = ⟨start, by omega⟩ := Fin.ext h_j_start
        rw [h_j_eq]
        have h_le : (⟨start, by omega⟩ : Fin n).val ≤ i'.val := by
          show start ≤ i'.val
          omega
        exact M.findRowPivot_eq_none ⟨start, by omega⟩ h_none' i' h_le
      · exact h_inv i' j' h_lt_ij' (by omega)
    have h_step_eq : M.rowEchelonAux start s =
        M.rowEchelonAux (start + 1) s := by
      rw [AzMatrix.rowEchelonAux.eq_def]
      simp only [dite_eq_left h_lt, h_none']
    intro i j h_lt_ij
    rw [h_step_eq]
    exact ih h_inv' i j h_lt_ij
  | case2 M start s h_lt kp h_pivot_kp ih =>
    have h_kp_val : kp.val = start := rfl
    have h_kp_eq : kp = ⟨start, by omega⟩ := rfl
    have h_pivot_kp' :
        M.findRowPivot ⟨start, by omega⟩ = some ⟨start, by omega⟩ := h_pivot_kp
    have h_inv' : ∀ i' j' : Fin n, j'.val < i'.val → j'.val < start + 1 →
        (M.eliminateBelow ⟨start, by omega⟩).toFn i' j' = 0 := by
      intro i' j' h_lt_ij' h_bnd
      rw [AzMatrix.toFn_eliminateBelow]
      by_cases h_i'_le : i'.val ≤ (⟨start, by omega⟩ : Fin n).val
      · rw [ite_eq_left h_i'_le]
        have h_j_lt_start : j'.val < start := by
          have : i'.val ≤ start := h_i'_le
          omega
        exact h_inv i' j' h_lt_ij' h_j_lt_start
      · rw [ite_eq_right h_i'_le]
        by_cases h_j_lt : j'.val < (⟨start, by omega⟩ : Fin n).val
        · rw [ite_eq_left h_j_lt]
          exact h_inv i' j' h_lt_ij' h_j_lt
        · rw [ite_eq_right h_j_lt]
          have h_j_eq : j'.val = start := by
            have h1 : j'.val ≥ start := by
              have : ¬ j'.val < (⟨start, by omega⟩ : Fin n).val := h_j_lt
              omega
            omega
          have h_j_kp : j' = ⟨start, by omega⟩ := Fin.ext h_j_eq
          rw [ite_eq_left h_j_kp]
    have h_step_eq : M.rowEchelonAux start s =
        (M.eliminateBelow ⟨start, by omega⟩).rowEchelonAux (start + 1) s := by
      rw [AzMatrix.rowEchelonAux.eq_def]
      simp only [dite_eq_left h_lt, h_pivot_kp', ite_true]
    intro i j h_lt_ij
    rw [h_step_eq]
    -- We have ih on (M.eliminateBelow kp), but we need it on
    -- (M.eliminateBelow ⟨start, by omega⟩). These are equal by defeq.
    exact ih h_inv' i j h_lt_ij
  | case3 M start s h_lt kp j h_pivot_j h_neq ih =>
    have h_kp_val : kp.val = start := rfl
    have h_kp_eq : kp = ⟨start, by omega⟩ := rfl
    have h_pivot_j' : M.findRowPivot ⟨start, by omega⟩ = some j := h_pivot_j
    have h_neq' : ¬ j = ⟨start, by omega⟩ := h_neq
    have h_j_ge : start ≤ j.val :=
      M.findRowPivot_some_le ⟨start, by omega⟩ j h_pivot_j'
    have h_inv' : ∀ i'' j'' : Fin n, j''.val < i''.val → j''.val < start + 1 →
        ((M.swapRows ⟨start, by omega⟩ j).eliminateBelow
          ⟨start, by omega⟩).toFn i'' j'' = 0 := by
      intro i'' j'' h_lt_ij'' h_bnd
      rw [AzMatrix.toFn_eliminateBelow]
      by_cases h_i''_le : i''.val ≤ (⟨start, by omega⟩ : Fin n).val
      · rw [ite_eq_left h_i''_le]
        rw [AzMatrix.toFn_swapRows]
        by_cases h_i_kp : i'' = ⟨start, by omega⟩
        · rw [ite_eq_left h_i_kp]
          have h_j''_lt_start : j''.val < start := by
            have : i''.val ≤ start := h_i''_le
            omega
          have h_j''_lt_j : j''.val < j.val := by omega
          exact h_inv j j'' h_j''_lt_j h_j''_lt_start
        · rw [ite_eq_right h_i_kp]
          by_cases h_i_j : i'' = j
          · rw [ite_eq_left h_i_j]
            -- M.toFn ⟨start, _⟩ j'' with j''.val < start
            have h_j''_lt_start : j''.val < start := by
              have : i''.val ≤ start := h_i''_le
              omega
            exact h_inv ⟨start, by omega⟩ j''
              (show j''.val < (⟨start, by omega⟩ : Fin n).val from h_j''_lt_start)
              h_j''_lt_start
          · rw [ite_eq_right h_i_j]
            have h_j''_lt_start : j''.val < start := by
              have : i''.val ≤ start := h_i''_le
              omega
            exact h_inv i'' j'' h_lt_ij'' h_j''_lt_start
      · rw [ite_eq_right h_i''_le]
        by_cases h_j_lt : j''.val < (⟨start, by omega⟩ : Fin n).val
        · rw [ite_eq_left h_j_lt]
          rw [AzMatrix.toFn_swapRows]
          have h_j''_lt_start : j''.val < start := h_j_lt
          by_cases h_i_kp : i'' = ⟨start, by omega⟩
          · rw [ite_eq_left h_i_kp]
            have h_j''_lt_j : j''.val < j.val := by omega
            exact h_inv j j'' h_j''_lt_j h_j''_lt_start
          · rw [ite_eq_right h_i_kp]
            by_cases h_i_j : i'' = j
            · rw [ite_eq_left h_i_j]
              exact h_inv ⟨start, by omega⟩ j''
                (show j''.val < (⟨start, by omega⟩ : Fin n).val from h_j''_lt_start)
                h_j''_lt_start
            · rw [ite_eq_right h_i_j]
              exact h_inv i'' j'' h_lt_ij'' h_j''_lt_start
        · rw [ite_eq_right h_j_lt]
          have h_j_eq : j''.val = start := by
            have h1 : j''.val ≥ start := by
              have : ¬ j''.val < (⟨start, by omega⟩ : Fin n).val := h_j_lt
              omega
            omega
          have h_j_kp : j'' = ⟨start, by omega⟩ := Fin.ext h_j_eq
          rw [ite_eq_left h_j_kp]
    have h_step_eq : M.rowEchelonAux start s =
        ((M.swapRows ⟨start, by omega⟩ j).eliminateBelow
          ⟨start, by omega⟩).rowEchelonAux (start + 1) (s + 1) := by
      rw [AzMatrix.rowEchelonAux.eq_def]
      simp only [dite_eq_left h_lt, h_pivot_j', ite_eq_right h_neq']
    intro i' j' h_lt_ij'
    rw [h_step_eq]
    exact ih h_inv' i' j' h_lt_ij'
  | case4 M start s h_no_step =>
    intro i j h_lt_ij
    have h_step_eq : M.rowEchelonAux start s = (M, s) := by
      rw [AzMatrix.rowEchelonAux.eq_def]
      simp only [dite_eq_right h_no_step]
    rw [h_step_eq]
    apply h_inv i j h_lt_ij
    have h_i_lt : i.val < n := i.isLt
    omega

/-- **The always-triangular variant produces an upper-triangular matrix.**
    `AzMatrix.rowEchelon M` returns a matrix whose `toFn` view is
    `BlockTriangular id` — i.e., upper triangular in Mathlib's sense. -/
theorem AzMatrix.rowEchelon_blockTriangular [Field K] [DecidableEq K]
    (M : AzMatrix K n n) :
    Matrix.BlockTriangular (M.rowEchelon).1.toFn id := by
  intro i j h_lt
  have h_lt' : j.val < i.val := h_lt
  exact M.rowEchelonAux_blockTriangular 0 0
    (fun _ _ _ h_bnd => absurd h_bnd (Nat.not_lt_zero _)) i j h_lt'

end Azurite
