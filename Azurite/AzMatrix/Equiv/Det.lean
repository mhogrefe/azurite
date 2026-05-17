/-
  Equivalence proof: `AzMatrix.det M = Matrix.det M.toFn`.

  The Gaussian-elimination determinant computed by `AzMatrix.det` agrees with
  Mathlib's `Matrix.det`. The proof tracks the determinant through each step
  of `gaussAux` (the BPR early-abort variant):

  * `eliminateBelow` is a row operation that preserves `Matrix.det` (when the
    pivot is nonzero and the pivot row has zeros to the left of the pivot
    column — both invariants of the gauss loop).
  * `swapCols` is a column transposition, which flips `Matrix.det`.
  * Hence `(-1)^s · Matrix.det M` is invariant under each step, and the
    output's determinant is the product of its diagonal (either via
    `Matrix.det_of_upperTriangular` in the no-abort case or via
    `Matrix.det_eq_zero_of_row_eq_zero` when the algorithm aborts on a zero
    pivot row).
-/
import Azurite.AzMatrix.Det
import Azurite.AzMatrix.Equiv.RowEchelon
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination

namespace Azurite

variable {K : Type _} [Field K] [DecidableEq K] {n : Nat}

/-! ### `swapCols` entrywise unfolding -/

omit [Field K] [DecidableEq K] in
theorem AzMatrix.toFn_swapCols (M : AzMatrix K n n) (j₁ j₂ i j : Fin n) :
    (M.swapCols j₁ j₂).toFn i j =
      (if j = j₁ then M.toFn i j₂
       else if j = j₂ then M.toFn i j₁
       else M.toFn i j) := by
  unfold AzMatrix.swapCols
  rw [AzMatrix.toFn_ofFn]
  rfl

/-! ### `findPivot` behavior (column search) -/

omit [Field K] in
theorem AzMatrix.findPivotAux_eq_none [Zero K]
    (M : AzMatrix K n n) (k : Fin n) :
    ∀ (start : Nat), M.findPivotAux k start = none →
      ∀ j : Fin n, start ≤ j.val → M.toFn k j = 0 := by
  apply AzMatrix.findPivotAux.induct M k
    (motive := fun start => M.findPivotAux k start = none →
      ∀ j : Fin n, start ≤ j.val → M.toFn k j = 0)
  · intro start h_lt h_zero ih h_rec j h_ge
    have hrec_eq : M.findPivotAux k (start + 1) = none := by
      rw [AzMatrix.findPivotAux.eq_def] at h_rec
      simp only [dif_pos h_lt, if_pos h_zero] at h_rec
      exact h_rec
    by_cases h_eq : j.val = start
    · have hj : j = ⟨start, h_lt⟩ := Fin.ext h_eq
      rw [hj]; exact h_zero
    · exact ih hrec_eq j (by omega)
  · intro start h_lt h_nz h_rec
    have h_eq : M.findPivotAux k start = some ⟨start, h_lt⟩ := by
      rw [AzMatrix.findPivotAux.eq_def]
      simp only [dif_pos h_lt, if_neg h_nz]
    rw [h_eq] at h_rec
    nomatch h_rec
  · intro start h_ge _ j _
    have : j.val < n := j.isLt
    omega

omit [Field K] in
theorem AzMatrix.findPivot_eq_none [Zero K]
    (M : AzMatrix K n n) (k : Fin n) (h : M.findPivot k = none) :
    ∀ j : Fin n, k.val ≤ j.val → M.toFn k j = 0 :=
  M.findPivotAux_eq_none k k.val h

omit [Field K] in
theorem AzMatrix.findPivotAux_some_le [Zero K]
    (M : AzMatrix K n n) (k : Fin n) :
    ∀ (start : Nat) (j : Fin n),
      M.findPivotAux k start = some j → start ≤ j.val := by
  intro start
  apply AzMatrix.findPivotAux.induct M k
    (motive := fun start => ∀ j : Fin n,
      M.findPivotAux k start = some j → start ≤ j.val)
  · intro start h_lt h_zero ih j h_rec
    have hrec_eq : M.findPivotAux k (start + 1) = some j := by
      rw [AzMatrix.findPivotAux.eq_def] at h_rec
      simp only [dif_pos h_lt, if_pos h_zero] at h_rec
      exact h_rec
    have := ih j hrec_eq
    omega
  · intro start h_lt h_nz j h_rec
    have h_eq : M.findPivotAux k start = some ⟨start, h_lt⟩ := by
      rw [AzMatrix.findPivotAux.eq_def]
      simp only [dif_pos h_lt, if_neg h_nz]
    rw [h_eq] at h_rec
    have h_eq_j : ⟨start, h_lt⟩ = j := by injection h_rec
    have : j.val = start := by rw [← h_eq_j]
    omega
  · intro start h_ge j h_rec
    rw [AzMatrix.findPivotAux.eq_def] at h_rec
    simp only [dif_neg h_ge] at h_rec
    nomatch h_rec

omit [Field K] in
theorem AzMatrix.findPivot_some_le [Zero K]
    (M : AzMatrix K n n) (k j : Fin n) (h : M.findPivot k = some j) :
    k.val ≤ j.val :=
  M.findPivotAux_some_le k k.val j h

omit [Field K] in
theorem AzMatrix.findPivotAux_some_nonzero [Zero K]
    (M : AzMatrix K n n) (k : Fin n) :
    ∀ (start : Nat) (j : Fin n),
      M.findPivotAux k start = some j → M.toFn k j ≠ 0 := by
  intro start
  apply AzMatrix.findPivotAux.induct M k
    (motive := fun start => ∀ j : Fin n,
      M.findPivotAux k start = some j → M.toFn k j ≠ 0)
  · intro start h_lt h_zero ih j h_rec
    have hrec_eq : M.findPivotAux k (start + 1) = some j := by
      rw [AzMatrix.findPivotAux.eq_def] at h_rec
      simp only [dif_pos h_lt, if_pos h_zero] at h_rec
      exact h_rec
    exact ih j hrec_eq
  · intro start h_lt h_nz j h_rec
    have h_eq : M.findPivotAux k start = some ⟨start, h_lt⟩ := by
      rw [AzMatrix.findPivotAux.eq_def]
      simp only [dif_pos h_lt, if_neg h_nz]
    rw [h_eq] at h_rec
    have h_j_eq : j = ⟨start, h_lt⟩ := (Option.some.inj h_rec).symm
    rw [h_j_eq]
    exact h_nz
  · intro start h_ge j h_rec
    rw [AzMatrix.findPivotAux.eq_def] at h_rec
    simp only [dif_neg h_ge] at h_rec
    nomatch h_rec

omit [Field K] in
theorem AzMatrix.findPivot_some_nonzero [Zero K]
    (M : AzMatrix K n n) (k j : Fin n) (h : M.findPivot k = some j) :
    M.toFn k j ≠ 0 :=
  M.findPivotAux_some_nonzero k k.val j h

/-! ### Det of `eliminateBelow` -/

omit [DecidableEq K] in
theorem AzMatrix.det_eliminateBelow
    (M : AzMatrix K n n) (k : Fin n)
    (h_pivot : M.toFn k k ≠ 0)
    (h_row : ∀ j : Fin n, j.val < k.val → M.toFn k j = 0) :
    Matrix.det (M.eliminateBelow k).toFn = Matrix.det M.toFn := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const
    (c := fun i => if k.val < i.val then -(M.toFn i k / M.toFn k k) else 0) k
  · simp
  · intro i j
    rw [AzMatrix.toFn_eliminateBelow]
    by_cases h_i_le : i.val ≤ k.val
    · rw [if_pos h_i_le]
      have h_not_lt : ¬ k.val < i.val := by omega
      rw [if_neg h_not_lt]
      ring
    · rw [if_neg h_i_le]
      have h_i_gt : k.val < i.val := by omega
      rw [if_pos h_i_gt]
      by_cases h_j_lt : j.val < k.val
      · rw [if_pos h_j_lt]
        rw [h_row j h_j_lt]
        ring
      · rw [if_neg h_j_lt]
        by_cases h_j_eq : j = k
        · rw [if_pos h_j_eq, h_j_eq]
          field_simp
          ring
        · rw [if_neg h_j_eq]
          ring

/-! ### Det of `swapCols` -/

omit [Field K] [DecidableEq K] in
theorem AzMatrix.toFn_swapCols_eq_submatrix
    (M : AzMatrix K n n) (j₁ j₂ : Fin n) :
    (M.swapCols j₁ j₂).toFn =
      Matrix.submatrix M.toFn id (Equiv.swap j₁ j₂) := by
  funext i j
  rw [AzMatrix.toFn_swapCols]
  show _ = M.toFn i ((Equiv.swap j₁ j₂) j)
  by_cases h₁ : j = j₁
  · rw [if_pos h₁, h₁, Equiv.swap_apply_left]
  · by_cases h₂ : j = j₂
    · rw [if_neg h₁, if_pos h₂, h₂, Equiv.swap_apply_right]
    · rw [if_neg h₁, if_neg h₂, Equiv.swap_apply_of_ne_of_ne h₁ h₂]

omit [DecidableEq K] in
theorem AzMatrix.det_swapCols
    (M : AzMatrix K n n) (j₁ j₂ : Fin n) (h_neq : j₁ ≠ j₂) :
    Matrix.det (M.swapCols j₁ j₂).toFn = -Matrix.det M.toFn := by
  rw [AzMatrix.toFn_swapCols_eq_submatrix]
  rw [Matrix.det_permute']
  rw [Equiv.Perm.sign_swap h_neq]
  push_cast
  ring

/-! ### Invariant -/

/-- The partial-zero invariant: `M[i][j] = 0` for all `j < i` with `j < start`. -/
def AzMatrix.PartialZero (M : AzMatrix K n n) (start : Nat) : Prop :=
  ∀ i j : Fin n, j.val < i.val → j.val < start → M.toFn i j = 0

omit [DecidableEq K] in
/-- `eliminateBelow M ⟨start, _⟩` extends `PartialZero` from `start` to
    `start + 1`. -/
theorem AzMatrix.eliminateBelow_preservesPartialZero
    (M : AzMatrix K n n) (start : Nat) (h_lt : start < n)
    (h_inv : M.PartialZero start) :
    (M.eliminateBelow ⟨start, h_lt⟩).PartialZero (start + 1) := by
  intro i j h_lt_ij h_bnd
  rw [AzMatrix.toFn_eliminateBelow]
  by_cases h_i_le : i.val ≤ start
  · rw [if_pos h_i_le]
    have h_j_lt_start : j.val < start := by omega
    exact h_inv i j h_lt_ij h_j_lt_start
  · rw [if_neg h_i_le]
    by_cases h_j_lt : j.val < start
    · rw [if_pos h_j_lt]
      exact h_inv i j h_lt_ij h_j_lt
    · rw [if_neg h_j_lt]
      have h_j_eq : j.val = start := by omega
      have h_j_kp : j = ⟨start, h_lt⟩ := Fin.ext h_j_eq
      rw [if_pos h_j_kp]

omit [DecidableEq K] in
/-- After swapping cols `⟨start, _⟩` and `jₚ` (with `jₚ ≥ start`), the
    invariant up to `start` is preserved. -/
theorem AzMatrix.swapCols_preservesPartialZero
    (M : AzMatrix K n n) (start : Nat) (h_lt : start < n)
    (h_inv : M.PartialZero start) (jₚ : Fin n) (h_jₚ_ge : start ≤ jₚ.val) :
    (M.swapCols ⟨start, h_lt⟩ jₚ).PartialZero start := by
  intro i j h_lt_ij h_bnd
  rw [AzMatrix.toFn_swapCols]
  have h_j_neq_kp : j ≠ ⟨start, h_lt⟩ := by
    intro h_eq
    have : j.val = start := by rw [h_eq]
    omega
  have h_j_neq_jₚ : j ≠ jₚ := by
    intro h_eq
    have : j.val = jₚ.val := by rw [h_eq]
    omega
  rw [if_neg h_j_neq_kp, if_neg h_j_neq_jₚ]
  exact h_inv i j h_lt_ij h_bnd

omit [DecidableEq K] in
/-- Row `⟨start, _⟩` of the swap-result has zeros to the left of column
    `start`. -/
theorem AzMatrix.swapCols_row_zeros
    (M : AzMatrix K n n) (start : Nat) (h_lt : start < n)
    (h_inv : M.PartialZero start) (jₚ : Fin n) (h_jₚ_ge : start ≤ jₚ.val) :
    ∀ j : Fin n, j.val < start →
      (M.swapCols ⟨start, h_lt⟩ jₚ).toFn ⟨start, h_lt⟩ j = 0 := by
  intro j h_j_lt
  rw [AzMatrix.toFn_swapCols]
  have h_j_neq_kp : j ≠ ⟨start, h_lt⟩ := by
    intro h_eq
    have : j.val = start := by rw [h_eq]
    omega
  have h_j_neq_jₚ : j ≠ jₚ := by
    intro h_eq
    have : j.val = jₚ.val := by rw [h_eq]
    omega
  rw [if_neg h_j_neq_kp, if_neg h_j_neq_jₚ]
  -- Need M.toFn ⟨start, h_lt⟩ j = 0; use h_inv with i = ⟨start, h_lt⟩.
  exact h_inv ⟨start, h_lt⟩ j h_j_lt h_j_lt

/-! ### Per-step det invariant -/

/-- At any point during `gaussAux`, the quantity `det M · (-1)^s` equals
    `(-1)^(final s) · ∏ (final diagonal)`. -/
theorem AzMatrix.gaussAux_det_eq
    (M : AzMatrix K n n) (start s : Nat) (h_inv : M.PartialZero start) :
    Matrix.det M.toFn * (-1 : K)^s =
      (-1 : K)^((M.gaussAux start s).2) *
        ∏ i : Fin n, (M.gaussAux start s).1.toFn i i := by
  induction M, start, s using AzMatrix.gaussAux.induct with
  | case1 M start s h_lt kp h_findPivot =>
    -- Abort: output = (M, s). Row ⟨start, _⟩ of M is all zero.
    have h_findPivot' : M.findPivot ⟨start, by omega⟩ = none := h_findPivot
    have h_step_eq : M.gaussAux start s = (M, s) := by
      rw [AzMatrix.gaussAux.eq_def]
      simp only [dif_pos h_lt, h_findPivot']
    rw [h_step_eq]
    have h_start_lt : start < n := by omega
    have h_start_zero : ∀ j : Fin n, M.toFn ⟨start, h_start_lt⟩ j = 0 := by
      intro j
      by_cases h_j_lt : j.val < start
      · exact h_inv ⟨start, h_start_lt⟩ j h_j_lt h_j_lt
      · have h_j_ge : start ≤ j.val := by omega
        exact M.findPivot_eq_none ⟨start, h_start_lt⟩ h_findPivot' j h_j_ge
    have h_det_zero : Matrix.det M.toFn = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero ⟨start, h_start_lt⟩ h_start_zero
    have h_prod_zero : ∏ i : Fin n, M.toFn i i = 0 := by
      apply Finset.prod_eq_zero (i := ⟨start, h_start_lt⟩) (Finset.mem_univ _)
      exact h_start_zero _
    rw [h_det_zero, h_prod_zero]
    ring
  | case2 M start s h_lt kp h_pivot_kp ih =>
    -- No swap: eliminate then recurse. Pivot at (start, start), nonzero.
    have h_start_lt : start < n := by omega
    have h_pivot_kp' :
        M.findPivot ⟨start, h_start_lt⟩ = some ⟨start, h_start_lt⟩ := h_pivot_kp
    have h_pivot_nz : M.toFn ⟨start, h_start_lt⟩ ⟨start, h_start_lt⟩ ≠ 0 :=
      M.findPivot_some_nonzero ⟨start, h_start_lt⟩ ⟨start, h_start_lt⟩ h_pivot_kp'
    have h_row_zeros : ∀ j : Fin n, j.val < (⟨start, h_start_lt⟩ : Fin n).val →
        M.toFn ⟨start, h_start_lt⟩ j = 0 := by
      intro j h_j_lt
      have h_j_lt' : j.val < start := h_j_lt
      exact h_inv ⟨start, h_start_lt⟩ j h_j_lt' h_j_lt'
    have h_det_eq :
        Matrix.det (M.eliminateBelow ⟨start, h_start_lt⟩).toFn =
          Matrix.det M.toFn :=
      M.det_eliminateBelow ⟨start, h_start_lt⟩ h_pivot_nz h_row_zeros
    have h_inv_next :
        (M.eliminateBelow ⟨start, h_start_lt⟩).PartialZero (start + 1) :=
      M.eliminateBelow_preservesPartialZero start h_start_lt h_inv
    have h_step_eq : M.gaussAux start s =
        (M.eliminateBelow ⟨start, h_start_lt⟩).gaussAux (start + 1) s := by
      rw [AzMatrix.gaussAux.eq_def]
      simp only [dif_pos h_lt, h_pivot_kp', if_true]
    rw [h_step_eq]
    rw [← h_det_eq]
    exact ih h_inv_next
  | case3 M start s h_lt kp j h_pivot_j h_neq ih =>
    -- Swap then eliminate. After swap, pivot at (start, start) is M[start][j] ≠ 0.
    have h_start_lt : start < n := by omega
    have h_pivot_j' : M.findPivot ⟨start, h_start_lt⟩ = some j := h_pivot_j
    have h_neq' : ¬ j = ⟨start, h_start_lt⟩ := h_neq
    have h_j_ge : start ≤ j.val :=
      M.findPivot_some_le ⟨start, h_start_lt⟩ j h_pivot_j'
    have h_orig_nz : M.toFn ⟨start, h_start_lt⟩ j ≠ 0 :=
      M.findPivot_some_nonzero ⟨start, h_start_lt⟩ j h_pivot_j'
    have h_swap_pivot_nz :
        (M.swapCols ⟨start, h_start_lt⟩ j).toFn
          ⟨start, h_start_lt⟩ ⟨start, h_start_lt⟩ ≠ 0 := by
      rw [AzMatrix.toFn_swapCols, if_pos rfl]
      exact h_orig_nz
    have h_swap_row_zeros : ∀ j' : Fin n,
        j'.val < (⟨start, h_start_lt⟩ : Fin n).val →
        (M.swapCols ⟨start, h_start_lt⟩ j).toFn ⟨start, h_start_lt⟩ j' = 0 := by
      intro j' h_j'_lt
      exact M.swapCols_row_zeros start h_start_lt h_inv j h_j_ge j' h_j'_lt
    have h_det_elim_eq :
        Matrix.det ((M.swapCols ⟨start, h_start_lt⟩ j).eliminateBelow
          ⟨start, h_start_lt⟩).toFn =
        Matrix.det (M.swapCols ⟨start, h_start_lt⟩ j).toFn :=
      (M.swapCols ⟨start, h_start_lt⟩ j).det_eliminateBelow
        ⟨start, h_start_lt⟩ h_swap_pivot_nz h_swap_row_zeros
    have h_kp_neq_j : (⟨start, h_start_lt⟩ : Fin n) ≠ j := fun h => h_neq' h.symm
    have h_det_swap_eq :
        Matrix.det (M.swapCols ⟨start, h_start_lt⟩ j).toFn =
          -Matrix.det M.toFn :=
      M.det_swapCols ⟨start, h_start_lt⟩ j h_kp_neq_j
    have h_inv_next :
        ((M.swapCols ⟨start, h_start_lt⟩ j).eliminateBelow
          ⟨start, h_start_lt⟩).PartialZero (start + 1) :=
      (M.swapCols ⟨start, h_start_lt⟩ j).eliminateBelow_preservesPartialZero
        start h_start_lt
        (M.swapCols_preservesPartialZero start h_start_lt h_inv j h_j_ge)
    have h_step_eq : M.gaussAux start s =
        ((M.swapCols ⟨start, h_start_lt⟩ j).eliminateBelow
          ⟨start, h_start_lt⟩).gaussAux (start + 1) (s + 1) := by
      rw [AzMatrix.gaussAux.eq_def]
      simp only [dif_pos h_lt, h_pivot_j', if_neg h_neq']
    rw [h_step_eq]
    have h_ih := ih h_inv_next
    rw [h_det_elim_eq, h_det_swap_eq] at h_ih
    have h_pow_succ : (-1 : K)^(s + 1) = (-1 : K)^s * (-1 : K) := pow_succ _ _
    rw [h_pow_succ] at h_ih
    linear_combination h_ih
  | case4 M start s h_no_step =>
    have h_step_eq : M.gaussAux start s = (M, s) := by
      rw [AzMatrix.gaussAux.eq_def]
      simp only [dif_neg h_no_step]
    rw [h_step_eq]
    have h_upper : Matrix.BlockTriangular M.toFn id := by
      intro i j h_lt_ij
      have h_lt' : j.val < i.val := h_lt_ij
      have h_i_lt : i.val < n := i.isLt
      have h_j_lt_start : j.val < start := by omega
      exact h_inv i j h_lt' h_j_lt_start
    rw [Matrix.det_of_upperTriangular h_upper]
    ring

/-! ### Main theorem -/

/-- **`AzMatrix.det` agrees with `Matrix.det`.** -/
theorem AzMatrix.det_eq_Matrix_det (M : AzMatrix K n n) :
    M.det = Matrix.det M.toFn := by
  have h_inv : M.PartialZero 0 := fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  have h := M.gaussAux_det_eq 0 0 h_inv
  rw [pow_zero, mul_one] at h
  show (let (U, s) := M.gauss; (-1 : K) ^ s * ∏ i, U.get i i) =
    Matrix.det M.toFn
  unfold AzMatrix.gauss
  show (-1 : K) ^ (M.gaussAux 0 0).2 *
      ∏ i, (M.gaussAux 0 0).1.toFn i i = Matrix.det M.toFn
  rw [← h]

end Azurite
