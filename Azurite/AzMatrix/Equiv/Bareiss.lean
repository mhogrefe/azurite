/-
  BPR equation (8.5):  b_{i,j}^{(k)} = g_{1,1}^{(0)} ⋯ g_{k,k}^{(k-1)} g_{i,j}^{(k)}.

  Reads: the Bareiss minor `det(M_{i,j}^{(k)})` equals the product of the
  first `k` Gauss pivots times the (i, j) entry of `M` after `k` Gauss steps.
  The argument has three parts:

  * **Gauss-block correspondence**: running `gaussSteps` on the Bareiss block
    `M_{i,j}^{(k)}` produces, at every step `ℓ ≤ k` and at every position
    `(l', m') : Fin (k+1) × Fin (k+1)`, the same entry as `gaussSteps` on the
    full `M` at the corresponding position `(bareissIdx i l', bareissIdx j m')`.
  * **Det preservation**: each `eliminateBelow` step preserves `Matrix.det`
    (under the nonzero-pivot hypothesis).
  * **Upper-triangular product**: after `k` steps the block is upper
    triangular, so its det is the product of its diagonal entries; by the
    correspondence the first `k` are the pivots of `M` and the last is
    `g_{i,j}^{(k)}`.
-/
import Azurite.AzMatrix.Bareiss
import Azurite.AzMatrix.Equiv.Det
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fin.Tuple.Basic

namespace Azurite

variable {K : Type _} {n : Nat}

/-! ### Helpers for `bareissIdx` -/

theorem AzMatrix.bareissIdx_val_of_lt {k : Nat} (hk : k ≤ n) (i : Fin n)
    (l' : Fin (k + 1)) (h : l'.val < k) :
    AzMatrix.bareissIdx k hk i l' = ⟨l'.val, lt_of_lt_of_le h hk⟩ := by
  have h_eq : l' = (⟨l'.val, h⟩ : Fin k).castSucc := by ext; rfl
  conv_lhs => rw [h_eq]
  unfold AzMatrix.bareissIdx
  rw [Fin.snoc_castSucc]

theorem AzMatrix.bareissIdx_of_val_eq {k : Nat} (hk : k ≤ n) (i : Fin n)
    (l' : Fin (k + 1)) (h : l'.val = k) :
    AzMatrix.bareissIdx k hk i l' = i := by
  conv_lhs => rw [show l' = Fin.last k by ext; exact h]
  unfold AzMatrix.bareissIdx
  rw [Fin.snoc_last]

/-! ### Gauss-block correspondence -/

/-- **Key lemma.** Running `gaussSteps` on the Bareiss block `M_{i,j}^{(k)}`
    produces the same entries as running `gaussSteps` on `M`, after mapping
    block indices `Fin (k+1) → Fin n` via `bareissIdx`. Holds for any step
    count `ℓ ≤ k`. -/
theorem AzMatrix.gaussSteps_bareissBlock_toFn [Field K]
    (M : AzMatrix K n n) (k : Nat) (hk : k ≤ n) (i j : Fin n)
    (hi : k ≤ i.val) (hj : k ≤ j.val) :
    ∀ ℓ : Nat, ℓ ≤ k → ∀ l' m' : Fin (k + 1),
      ((M.bareissBlock k hk i j).gaussSteps ℓ).toFn l' m' =
        (M.gaussSteps ℓ).toFn
          (AzMatrix.bareissIdx k hk i l')
          (AzMatrix.bareissIdx k hk j m') := by
  intro ℓ hℓ
  induction ℓ with
  | zero =>
    intro l' m'
    rw [AzMatrix.gaussSteps_zero, AzMatrix.gaussSteps_zero]
    show (M.bareissBlock k hk i j).toFn l' m' = _
    rw [AzMatrix.toFn_bareissBlock]
    rfl
  | succ ℓ ih =>
    intro l' m'
    have hℓ_lt_k : ℓ < k := by omega
    have hℓ_lt_succk : ℓ < k + 1 := by omega
    have hℓ_lt_n : ℓ < n := lt_of_lt_of_le hℓ_lt_k hk
    rw [AzMatrix.gaussSteps_succ _ _ hℓ_lt_succk]
    rw [AzMatrix.gaussSteps_succ _ _ hℓ_lt_n]
    rw [AzMatrix.toFn_eliminateBelow, AzMatrix.toFn_eliminateBelow]
    -- Now we have two big if-chains. Show they agree.
    have ih' := ih (by omega)
    -- The Fin-side pivot identities:
    have h_pivot_block : AzMatrix.bareissIdx k hk i ⟨ℓ, hℓ_lt_succk⟩ =
        ⟨ℓ, hℓ_lt_n⟩ := AzMatrix.bareissIdx_val_of_lt hk i ⟨ℓ, hℓ_lt_succk⟩ hℓ_lt_k
    have h_pivot_block_j : AzMatrix.bareissIdx k hk j ⟨ℓ, hℓ_lt_succk⟩ =
        ⟨ℓ, hℓ_lt_n⟩ := AzMatrix.bareissIdx_val_of_lt hk j ⟨ℓ, hℓ_lt_succk⟩ hℓ_lt_k
    -- Distinguish on l'.val and m'.val.
    have h_l'_le_iff : l'.val ≤ ℓ ↔
        (AzMatrix.bareissIdx k hk i l').val ≤ ℓ := by
      by_cases h_l' : l'.val < k
      · rw [AzMatrix.bareissIdx_val_of_lt hk i l' h_l']
      · have h_l'_eq : l'.val = k := by have := l'.isLt; omega
        rw [AzMatrix.bareissIdx_of_val_eq hk i l' h_l'_eq]
        constructor
        · intro h
          rw [h_l'_eq] at h
          omega
        · intro h
          have : i.val ≤ ℓ := h
          omega
    have h_m'_lt_iff : m'.val < ℓ ↔
        (AzMatrix.bareissIdx k hk j m').val < ℓ := by
      by_cases h_m' : m'.val < k
      · rw [AzMatrix.bareissIdx_val_of_lt hk j m' h_m']
      · have h_m'_eq : m'.val = k := by have := m'.isLt; omega
        rw [AzMatrix.bareissIdx_of_val_eq hk j m' h_m'_eq]
        constructor
        · intro h
          rw [h_m'_eq] at h
          omega
        · intro h
          have : j.val < ℓ := h
          omega
    have h_m'_eq_iff : m' = ⟨ℓ, hℓ_lt_succk⟩ ↔
        AzMatrix.bareissIdx k hk j m' = ⟨ℓ, hℓ_lt_n⟩ := by
      by_cases h_m' : m'.val < k
      · rw [AzMatrix.bareissIdx_val_of_lt hk j m' h_m']
        constructor
        · intro h
          have h_val : m'.val = ℓ := congrArg Fin.val h
          apply Fin.ext
          exact h_val
        · intro h
          have h_val : m'.val = ℓ := congrArg Fin.val h
          apply Fin.ext
          exact h_val
      · have h_m'_eq : m'.val = k := by have := m'.isLt; omega
        rw [AzMatrix.bareissIdx_of_val_eq hk j m' h_m'_eq]
        constructor
        · intro h
          have : m'.val = ℓ := congrArg Fin.val h
          omega
        · intro h
          have : j.val = ℓ := congrArg Fin.val h
          omega
    -- Use the iffs to split on the conditions
    by_cases h_l'_le : l'.val ≤ ℓ
    · rw [if_pos h_l'_le, if_pos (h_l'_le_iff.mp h_l'_le)]
      exact ih' l' m'
    · rw [if_neg h_l'_le, if_neg (fun h => h_l'_le ((h_l'_le_iff.mpr h)))]
      by_cases h_m'_lt : m'.val < ℓ
      · rw [if_pos h_m'_lt, if_pos (h_m'_lt_iff.mp h_m'_lt)]
        exact ih' l' m'
      · rw [if_neg h_m'_lt, if_neg (fun h => h_m'_lt (h_m'_lt_iff.mpr h))]
        by_cases h_m'_eq : m' = ⟨ℓ, hℓ_lt_succk⟩
        · rw [if_pos h_m'_eq, if_pos (h_m'_eq_iff.mp h_m'_eq)]
        · rw [if_neg h_m'_eq, if_neg (fun h => h_m'_eq (h_m'_eq_iff.mpr h))]
          -- Formula case: both sides have the same algebraic form
          rw [ih' l' m']
          rw [ih' l' ⟨ℓ, hℓ_lt_succk⟩]
          rw [ih' ⟨ℓ, hℓ_lt_succk⟩ ⟨ℓ, hℓ_lt_succk⟩]
          rw [ih' ⟨ℓ, hℓ_lt_succk⟩ m']
          rw [h_pivot_block, h_pivot_block_j]

/-! ### Partial-zero invariant for `gaussSteps` -/

/-- After `ℓ` Gauss steps, the matrix has zeros below the diagonal in
    columns `< ℓ`. Holds unconditionally (regardless of pivot values). -/
theorem AzMatrix.gaussSteps_partialZero [Field K] (M : AzMatrix K n n) (ℓ : Nat) :
    ∀ i j : Fin n, j.val < i.val → j.val < ℓ →
      (M.gaussSteps ℓ).toFn i j = 0 := by
  induction ℓ with
  | zero => intros _ _ _ h_bnd; omega
  | succ ℓ ih =>
    intro i j h_lt_ij h_bnd
    by_cases h_ℓ_lt : ℓ < n
    · rw [AzMatrix.gaussSteps_succ _ _ h_ℓ_lt]
      rw [AzMatrix.toFn_eliminateBelow]
      by_cases h_i_le : i.val ≤ ℓ
      · rw [if_pos h_i_le]
        exact ih i j h_lt_ij (by omega)
      · rw [if_neg h_i_le]
        by_cases h_j_lt : j.val < ℓ
        · rw [if_pos h_j_lt]
          exact ih i j h_lt_ij h_j_lt
        · rw [if_neg h_j_lt]
          have h_j_eq : j.val = ℓ := by omega
          have h_j_kp : j = ⟨ℓ, h_ℓ_lt⟩ := Fin.ext h_j_eq
          rw [if_pos h_j_kp]
    · rw [AzMatrix.gaussSteps_of_ge _ _ h_ℓ_lt]
      exact ih i j h_lt_ij (by omega)

/-! ### Row-stability across subsequent `gaussSteps` -/

/-- Row `ℓ` is unchanged by `gaussSteps` for step counts `≥ ℓ`. Each step `k'`
    with `k' ≥ ℓ` uses a pivot at row `k' ≥ ℓ`, so `eliminateBelow`'s
    "row above or at the pivot is unchanged" branch fires. -/
theorem AzMatrix.gaussSteps_row_unchanged [Field K] (M : AzMatrix K n n)
    (ℓ : Nat) (hℓ : ℓ < n) :
    ∀ k : Nat, ℓ ≤ k → ∀ j : Fin n,
      (M.gaussSteps k).toFn ⟨ℓ, hℓ⟩ j = (M.gaussSteps ℓ).toFn ⟨ℓ, hℓ⟩ j := by
  intro k
  induction k with
  | zero =>
    intro h_ge j
    have hℓ_eq : ℓ = 0 := Nat.le_zero.mp h_ge
    subst hℓ_eq
    rfl
  | succ k ih =>
    intro h_ge j
    by_cases h_eq : ℓ = k + 1
    · rw [← h_eq]
    · have h_le_k : ℓ ≤ k := by omega
      by_cases hk_lt : k < n
      · rw [AzMatrix.gaussSteps_succ _ _ hk_lt]
        rw [AzMatrix.toFn_eliminateBelow]
        have hle : (⟨ℓ, hℓ⟩ : Fin n).val ≤ k := h_le_k
        rw [if_pos hle]
        exact ih h_le_k j
      · rw [AzMatrix.gaussSteps_of_ge _ _ hk_lt]
        exact ih h_le_k j

/-- Diagonal stability: `(gaussSteps M k).toFn ⟨ℓ, _⟩ ⟨ℓ, _⟩` is fixed for
    all `k ≥ ℓ`. -/
theorem AzMatrix.gaussSteps_diag_stable [Field K] (M : AzMatrix K n n)
    (ℓ k : Nat) (hℓk : ℓ ≤ k) (hℓ : ℓ < n) :
    (M.gaussSteps k).toFn ⟨ℓ, hℓ⟩ ⟨ℓ, hℓ⟩ =
      (M.gaussSteps ℓ).toFn ⟨ℓ, hℓ⟩ ⟨ℓ, hℓ⟩ :=
  M.gaussSteps_row_unchanged ℓ hℓ k hℓk ⟨ℓ, hℓ⟩

/-! ### Det preservation by `gaussSteps` -/

/-- `gaussSteps` preserves `Matrix.det` as long as each pivot encountered is
    nonzero. -/
theorem AzMatrix.det_gaussSteps [Field K] (M : AzMatrix K n n) :
    ∀ ℓ : Nat,
      (∀ k' : Nat, k' < ℓ → (h : k' < n) →
        (M.gaussSteps k').toFn ⟨k', h⟩ ⟨k', h⟩ ≠ 0) →
      Matrix.det (M.gaussSteps ℓ).toFn = Matrix.det M.toFn := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _; rw [AzMatrix.gaussSteps_zero]
  | succ ℓ ih =>
    intro h_pivots
    by_cases h_ℓ_lt : ℓ < n
    · rw [AzMatrix.gaussSteps_succ _ _ h_ℓ_lt]
      have h_pivot_nz :
          (M.gaussSteps ℓ).toFn ⟨ℓ, h_ℓ_lt⟩ ⟨ℓ, h_ℓ_lt⟩ ≠ 0 :=
        h_pivots ℓ (Nat.lt_succ_self _) h_ℓ_lt
      have h_row_zeros : ∀ j' : Fin n, j'.val < (⟨ℓ, h_ℓ_lt⟩ : Fin n).val →
          (M.gaussSteps ℓ).toFn ⟨ℓ, h_ℓ_lt⟩ j' = 0 := by
        intro j' h_j_lt
        exact M.gaussSteps_partialZero ℓ ⟨ℓ, h_ℓ_lt⟩ j' h_j_lt h_j_lt
      rw [AzMatrix.det_eliminateBelow _ _ h_pivot_nz h_row_zeros]
      exact ih (fun k' hk' h => h_pivots k' (by omega) h)
    · rw [AzMatrix.gaussSteps_of_ge _ _ h_ℓ_lt]
      exact ih (fun k' hk' h => h_pivots k' (by omega) h)

/-! ### Block is upper triangular after `k` steps -/

/-- After `k` Gauss steps, a `(k+1) × (k+1)` matrix is upper triangular
    (block-triangular w.r.t. `id`). Holds unconditionally — the partial-zero
    invariant zeros each pivot column below the diagonal, and the last
    column has no entries below the diagonal in a `(k+1) × (k+1)` matrix. -/
theorem AzMatrix.gaussSteps_blockTriangular [Field K]
    (M : AzMatrix K (k + 1) (k + 1)) :
    Matrix.BlockTriangular (M.gaussSteps k).toFn id := by
  intro i j h_lt
  have h_j_lt : j.val < i.val := h_lt
  have h_j_lt_k : j.val < k := by
    have h_i_lt : i.val < k + 1 := i.isLt
    omega
  exact M.gaussSteps_partialZero k i j h_j_lt h_j_lt_k

/-! ### Main theorem: equation (8.5) -/

/-- **BPR equation (8.5).** When the first `k` Gauss pivots of `M` are
    nonzero, the Bareiss minor `b_{i, j}^{(k)} = det(M_{i, j}^{(k)})` factors
    as the product of those pivots times `g_{i, j}^{(k)}`, the `(i, j)` entry
    of `M` after `k` Gauss steps. -/
theorem AzMatrix.bareissMinor_eq_prod_pivots_times_gaussSteps
    [Field K] [DecidableEq K] (M : AzMatrix K n n)
    (k : Nat) (hk : k < n) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val)
    (h_pivots : ∀ ℓ : Nat, ℓ < k → (h : ℓ < n) →
      (M.gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0) :
    M.bareissMinor k (le_of_lt hk) i j =
      (∏ ℓ : Fin (k + 1),
        if hℓ : ℓ.val < k then
          (M.gaussSteps ℓ.val).toFn
            ⟨ℓ.val, lt_of_lt_of_le hℓ (le_of_lt hk)⟩
            ⟨ℓ.val, lt_of_lt_of_le hℓ (le_of_lt hk)⟩
        else
          (M.gaussSteps k).toFn i j) := by
  -- Strategy:
  -- 1. bareissMinor = det(block).
  -- 2. det(block) = det(gaussSteps block k) (by det preservation, under
  --    nonzero pivot hypothesis transferred via the correspondence).
  -- 3. det(gaussSteps block k) = ∏ diagonal (block is upper triangular).
  -- 4. By the correspondence, diagonal entries match M's gaussSteps.
  unfold AzMatrix.bareissMinor
  set B := M.bareissBlock k (le_of_lt hk) i j with hB
  -- Step 2: det(B) = det(gaussSteps B k).
  have h_block_pivots : ∀ ℓ : Nat, ℓ < k → (h : ℓ < k + 1) →
      (B.gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0 := by
    intro ℓ hℓk hℓ_succk
    have hℓ_n : ℓ < n := lt_of_lt_of_le hℓk (le_of_lt hk)
    have h_corr := M.gaussSteps_bareissBlock_toFn k (le_of_lt hk) i j hi hj
      ℓ (le_of_lt hℓk) ⟨ℓ, hℓ_succk⟩ ⟨ℓ, hℓ_succk⟩
    rw [hB.symm] at h_corr
    rw [h_corr]
    rw [AzMatrix.bareissIdx_val_of_lt (le_of_lt hk) i ⟨ℓ, hℓ_succk⟩ hℓk]
    rw [AzMatrix.bareissIdx_val_of_lt (le_of_lt hk) j ⟨ℓ, hℓ_succk⟩ hℓk]
    exact h_pivots ℓ hℓk hℓ_n
  have h_det_block : Matrix.det (B.gaussSteps k).toFn = Matrix.det B.toFn :=
    B.det_gaussSteps k h_block_pivots
  rw [← h_det_block]
  -- Step 3: det of upper triangular = ∏ diagonal.
  rw [Matrix.det_of_upperTriangular B.gaussSteps_blockTriangular]
  -- Step 4: identify each diagonal entry.
  apply Finset.prod_congr rfl
  intro ℓ _
  by_cases hℓ : ℓ.val < k
  · rw [dif_pos hℓ]
    have hℓ_n : ℓ.val < n := lt_of_lt_of_le hℓ (le_of_lt hk)
    have h_corr := M.gaussSteps_bareissBlock_toFn k (le_of_lt hk) i j hi hj
      k (le_refl k) ⟨ℓ.val, ℓ.isLt⟩ ⟨ℓ.val, ℓ.isLt⟩
    rw [hB.symm] at h_corr
    rw [h_corr]
    rw [AzMatrix.bareissIdx_val_of_lt (le_of_lt hk) i ⟨ℓ.val, ℓ.isLt⟩ hℓ]
    rw [AzMatrix.bareissIdx_val_of_lt (le_of_lt hk) j ⟨ℓ.val, ℓ.isLt⟩ hℓ]
    -- Need (gaussSteps M k).toFn ⟨ℓ, _⟩ ⟨ℓ, _⟩ = (gaussSteps M ℓ).toFn ⟨ℓ, _⟩ ⟨ℓ, _⟩.
    -- These are equal: row ℓ is unchanged by steps ℓ, ℓ+1, …, k-1.
    exact M.gaussSteps_diag_stable ℓ.val k hℓ.le hℓ_n
  · rw [dif_neg hℓ]
    have h_ℓ_eq : ℓ.val = k := by
      have := ℓ.isLt
      omega
    have h_corr := M.gaussSteps_bareissBlock_toFn k (le_of_lt hk) i j hi hj
      k (le_refl k) ⟨ℓ.val, ℓ.isLt⟩ ⟨ℓ.val, ℓ.isLt⟩
    rw [hB.symm] at h_corr
    rw [h_corr]
    rw [AzMatrix.bareissIdx_of_val_eq (le_of_lt hk) i ⟨ℓ.val, ℓ.isLt⟩ h_ℓ_eq]
    rw [AzMatrix.bareissIdx_of_val_eq (le_of_lt hk) j ⟨ℓ.val, ℓ.isLt⟩ h_ℓ_eq]

/-! ### `pivotProd`: product of the first `k` Gauss pivots -/

/-- Product of the first `k` Gauss pivots of `M`. -/
def AzMatrix.pivotProd [Field K] (M : AzMatrix K n n) (k : Nat) (hk : k ≤ n) : K :=
  ∏ ℓ : Fin k, (M.gaussSteps ℓ.val).toFn
    ⟨ℓ.val, lt_of_lt_of_le ℓ.isLt hk⟩
    ⟨ℓ.val, lt_of_lt_of_le ℓ.isLt hk⟩

@[simp]
theorem AzMatrix.pivotProd_zero [Field K] (M : AzMatrix K n n) :
    M.pivotProd 0 (Nat.zero_le n) = 1 := by
  simp [AzMatrix.pivotProd]

theorem AzMatrix.pivotProd_succ [Field K] (M : AzMatrix K n n)
    (k : Nat) (hk : k < n) :
    M.pivotProd (k + 1) hk =
      M.pivotProd k hk.le * (M.gaussSteps k).toFn ⟨k, hk⟩ ⟨k, hk⟩ := by
  unfold AzMatrix.pivotProd
  rw [Fin.prod_univ_castSucc]
  rfl

/-! ### Cleaner factored form of (8.5) -/

/-- **Factored form of equation (8.5).** -/
theorem AzMatrix.bareissMinor_eq_pivotProd_mul_gaussSteps
    [Field K] [DecidableEq K] (M : AzMatrix K n n)
    (k : Nat) (hk : k < n) (i j : Fin n) (hi : k ≤ i.val) (hj : k ≤ j.val)
    (h_pivots : ∀ ℓ : Nat, ℓ < k → (h : ℓ < n) →
      (M.gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0) :
    M.bareissMinor k (le_of_lt hk) i j =
      M.pivotProd k hk.le * (M.gaussSteps k).toFn i j := by
  rw [M.bareissMinor_eq_prod_pivots_times_gaussSteps k hk i j hi hj h_pivots]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro ℓ _
    have h_lt : ℓ.castSucc.val < k := ℓ.isLt
    rw [dif_pos h_lt]
    rfl
  · have h_not_lt : ¬ (Fin.last k).val < k := by simp
    rw [dif_neg h_not_lt]

/-- The principal `(k+1)`-th minor equals the product of the first `k+1`
    Gauss pivots (under the nonzero-pivot hypothesis). -/
theorem AzMatrix.principalMinor_eq_pivotProd
    [Field K] [DecidableEq K] (M : AzMatrix K n n)
    (k : Nat) (hk : k < n)
    (h_pivots : ∀ ℓ : Nat, ℓ < k → (h : ℓ < n) →
      (M.gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0) :
    M.principalMinor k hk = M.pivotProd (k + 1) hk := by
  unfold AzMatrix.principalMinor
  rw [M.bareissMinor_eq_pivotProd_mul_gaussSteps k hk ⟨k, hk⟩ ⟨k, hk⟩
      (le_refl k) (le_refl k) h_pivots]
  rw [M.pivotProd_succ k hk]

/-! ### Gauss elimination recurrence (BPR equation 8.3) -/

/-- For `i, j > k`, the `(i, j)` entry after `k + 1` Gauss steps equals the
    Gauss elimination formula applied to the `k`-step state. This is BPR's
    equation (8.3). -/
theorem AzMatrix.gaussSteps_succ_apply [Field K]
    (M : AzMatrix K n n) (k : Nat) (hk : k < n) (i j : Fin n)
    (hi : k < i.val) (hj : k < j.val) :
    (M.gaussSteps (k + 1)).toFn i j =
      (M.gaussSteps k).toFn i j -
        ((M.gaussSteps k).toFn i ⟨k, hk⟩ /
          (M.gaussSteps k).toFn ⟨k, hk⟩ ⟨k, hk⟩) *
        (M.gaussSteps k).toFn ⟨k, hk⟩ j := by
  rw [AzMatrix.gaussSteps_succ _ _ hk]
  rw [AzMatrix.toFn_eliminateBelow]
  have h_not_i_le : ¬ i.val ≤ k := by omega
  rw [if_neg h_not_i_le]
  have h_not_j_lt : ¬ j.val < k := by omega
  rw [if_neg h_not_j_lt]
  have h_j_ne : j ≠ ⟨k, hk⟩ := by
    intro heq
    have h : j.val = k := by rw [heq]
    omega
  rw [if_neg h_j_ne]

/-! ### BPR Proposition 8.20 (Sylvester-Bareiss recurrence) -/

/-- **BPR Proposition 8.20.** The Sylvester-style recurrence for Bareiss
    minors:

      `b_{i,j}^{(k+2)} · b_{k+1,k+1}^{(k)} =
         b_{k+2,k+2}^{(k+1)} · b_{i,j}^{(k+1)} −
         b_{i,k+2}^{(k+1)} · b_{k+2,j}^{(k+1)}`.

    (Equivalent to BPR's `b_{i,j}^{(k+1)}` form via the substitution
    `k ↦ k + 1` to avoid truncating natural subtraction.) Stated in
    multiplicative form — equivalent to BPR's fraction form when
    `b_{k+1,k+1}^{(k)} ≠ 0`, but the multiplicative shape works without
    division and is what's needed for the fraction-free Bareiss algorithm.

    The proof inserts (8.5) for each of the five minors, then uses BPR's
    elimination recurrence (8.3) on `(gaussSteps M (k+2)).toFn i j`. -/
theorem AzMatrix.bareissMinor_recurrence
    [Field K] [DecidableEq K] (M : AzMatrix K n n)
    (k : Nat) (i j : Fin n) (hi : k + 2 ≤ i.val) (hj : k + 2 ≤ j.val)
    (h_pivots : ∀ ℓ : Nat, ℓ ≤ k + 1 → (h : ℓ < n) →
      (M.gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0) :
    M.bareissMinor (k + 2) (by have := i.isLt; omega) i j *
        M.principalMinor k (by have := i.isLt; omega) =
      M.principalMinor (k + 1) (by have := i.isLt; omega) *
          M.bareissMinor (k + 1) (by have := i.isLt; omega) i j -
        M.bareissMinor (k + 1) (by have := i.isLt; omega) i
          ⟨k + 1, by have := i.isLt; omega⟩ *
          M.bareissMinor (k + 1) (by have := i.isLt; omega)
            ⟨k + 1, by have := i.isLt; omega⟩ j := by
  have hi_lt : i.val < n := i.isLt
  have hkp2_lt_n : k + 2 < n + 1 := by omega
  have hkp2_le_n : k + 2 ≤ n := by omega
  have hk1_lt_n : k + 1 < n := by omega
  have hk_lt_n : k < n := by omega
  -- Hypothesis bundling
  have h_piv_kp2 : ∀ ℓ : Nat, ℓ < k + 2 → (h : ℓ < n) →
      (M.gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0 :=
    fun ℓ hℓ h => h_pivots ℓ (Nat.lt_succ_iff.mp hℓ) h
  have h_piv_kp1 : ∀ ℓ : Nat, ℓ < k + 1 → (h : ℓ < n) →
      (M.gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0 :=
    fun ℓ hℓ h => h_pivots ℓ (by omega) h
  have h_piv_k : ∀ ℓ : Nat, ℓ < k → (h : ℓ < n) →
      (M.gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0 :=
    fun ℓ hℓ h => h_pivots ℓ (by omega) h
  have h_pivot_kp1 :
      (M.gaussSteps (k + 1)).toFn ⟨k + 1, hk1_lt_n⟩ ⟨k + 1, hk1_lt_n⟩ ≠ 0 :=
    h_pivots (k + 1) (le_refl _) hk1_lt_n
  -- Rewrite each minor via the factored (8.5).
  have hkp2_lt_n' : k + 2 < n := by omega
  rw [M.bareissMinor_eq_pivotProd_mul_gaussSteps (k + 2) hkp2_lt_n' i j
      (by omega) (by omega) h_piv_kp2]
  rw [M.principalMinor_eq_pivotProd k hk_lt_n h_piv_k]
  rw [M.principalMinor_eq_pivotProd (k + 1) hk1_lt_n h_piv_kp1]
  rw [M.bareissMinor_eq_pivotProd_mul_gaussSteps (k + 1) hk1_lt_n i j
      (by omega) (by omega) h_piv_kp1]
  rw [M.bareissMinor_eq_pivotProd_mul_gaussSteps (k + 1) hk1_lt_n i
      ⟨k + 1, hk1_lt_n⟩ (by omega) (Nat.le_refl _) h_piv_kp1]
  rw [M.bareissMinor_eq_pivotProd_mul_gaussSteps (k + 1) hk1_lt_n
      ⟨k + 1, hk1_lt_n⟩ j (Nat.le_refl _) (by omega) h_piv_kp1]
  -- Connect pivotProd levels: pivotProd (k+2) = pivotProd (k+1) * pivot_{k+1}.
  rw [show M.pivotProd (k + 2) hkp2_lt_n'.le =
      M.pivotProd ((k + 1) + 1) hkp2_lt_n'.le from rfl]
  rw [M.pivotProd_succ (k + 1) hk1_lt_n]
  -- Express g^{(k+2)} via g^{(k+1)} using BPR equation (8.3).
  rw [M.gaussSteps_succ_apply (k + 1) hk1_lt_n i j (by omega) (by omega)]
  -- Field arithmetic.
  field_simp

end Azurite
