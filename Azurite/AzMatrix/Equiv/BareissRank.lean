/-
  Correctness of `AzMatrix.bareissRank` over an integral domain.

  Mirrors the gauss-side correctness proof (`AzMatrix.Equiv.GaussRank`)
  with the Bareiss elimination matrix in place of `elimMatrix`. The
  Bareiss step (BPR Proposition 8.20) factors in a field as
    `bareissEliminate M k b = D · elimMatrix · M`
  where `D` is the diagonal matrix scaling rows `i > k` by
  `M[k][k] / b_prev`. Both factors are invertible (under the standing
  hypothesis that `M[k][k] ≠ 0` and `b_prev ≠ 0`), so rank is preserved.

  The Domain version lifts through `algebraMap D (FractionRing D)`,
  parallel to `AzMatrix.Equiv.BareissDet`.
-/
import Azurite.AzMatrix.BareissRank
import Azurite.AzMatrix.Equiv.GaussRank
import Azurite.AzMatrix.Equiv.BareissDet
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

set_option linter.unusedSectionVars false

namespace Azurite

/-! ### Field case: rank invariance of `bareissEliminate` -/

section FieldCase

variable {K : Type _} [Field K] [DecidableEq K] {n : Nat}

/-- The Bareiss elimination matrix in a field. Multiplying `M.toFn` on
    the left by this matrix produces `M.bareissEliminate k b_prev` whenever
    `M.toFn k k ≠ 0`, `b_prev ≠ 0`, and the first `k.val` columns of row
    `k` are zero (`PartialZero M k.val`).

    It factors as `bareissDiagScale · elimMatrix`, where `elimMatrix` is
    the gauss-style elementary matrix (from `Equiv.GaussRank`) and
    `bareissDiagScale` rescales rows `i > k` by `M[k][k] / b_prev`. -/
def AzMatrix.bareissElimMatrix (M : AzMatrix K n n) (k : Fin n) (b_prev : K) :
    Matrix (Fin n) (Fin n) K :=
  fun i l =>
    if i = l then
      (if k.val < i.val then M.toFn k k / b_prev else 1)
    else if k.val < i.val ∧ l = k then
      -(M.toFn i k / b_prev)
    else 0

theorem AzMatrix.bareissElimMatrix_apply_diag
    (M : AzMatrix K n n) (k : Fin n) (b_prev : K) (i : Fin n) :
    M.bareissElimMatrix k b_prev i i =
      (if k.val < i.val then M.toFn k k / b_prev else 1) := by
  unfold AzMatrix.bareissElimMatrix
  rw [if_pos rfl]

theorem AzMatrix.bareissElimMatrix_apply_of_ne
    (M : AzMatrix K n n) (k : Fin n) (b_prev : K) (i l : Fin n) (h : i ≠ l) :
    M.bareissElimMatrix k b_prev i l =
      (if k.val < i.val ∧ l = k then -(M.toFn i k / b_prev) else 0) := by
  unfold AzMatrix.bareissElimMatrix
  rw [if_neg h]

/-! ### `det` of the Bareiss elimination matrix is nonzero -/

/-- `bareissElimMatrix` is *lower* triangular: entries `(i, l)` with `i < l`
    (strictly above the diagonal) vanish. -/
theorem AzMatrix.bareissElimMatrix_blockTriangular
    (M : AzMatrix K n n) (k : Fin n) (b_prev : K) :
    (M.bareissElimMatrix k b_prev).BlockTriangular OrderDual.toDual := by
  intro i l h_lt
  -- h_lt : OrderDual.toDual l < OrderDual.toDual i, equivalently i.val < l.val.
  have h_lt' : i.val < l.val := h_lt
  unfold AzMatrix.bareissElimMatrix
  have h_neq : i ≠ l := fun h => by rw [h] at h_lt'; exact Nat.lt_irrefl _ h_lt'
  rw [if_neg h_neq]
  have h_neg : ¬ (k.val < i.val ∧ l = k) := by
    intro ⟨h_ki, h_lk⟩
    have h_l_val : l.val = k.val := by rw [h_lk]
    omega
  rw [if_neg h_neg]

theorem AzMatrix.det_bareissElimMatrix_ne_zero
    (M : AzMatrix K n n) (k : Fin n) (b_prev : K)
    (h_pivot : M.toFn k k ≠ 0) (h_b_prev : b_prev ≠ 0) :
    Matrix.det (M.bareissElimMatrix k b_prev) ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular _
        (M.bareissElimMatrix_blockTriangular k b_prev)]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [M.bareissElimMatrix_apply_diag k b_prev]
  by_cases h_ki : k.val < i.val
  · rw [if_pos h_ki]; exact div_ne_zero h_pivot h_b_prev
  · rw [if_neg h_ki]; exact one_ne_zero

theorem AzMatrix.isUnit_det_bareissElimMatrix
    (M : AzMatrix K n n) (k : Fin n) (b_prev : K)
    (h_pivot : M.toFn k k ≠ 0) (h_b_prev : b_prev ≠ 0) :
    IsUnit (Matrix.det (M.bareissElimMatrix k b_prev)) :=
  isUnit_iff_ne_zero.mpr
    (M.det_bareissElimMatrix_ne_zero k b_prev h_pivot h_b_prev)

/-! ### Factorization: `bareissEliminate = bareissElimMatrix * M` -/

/-- In a field, when the pivot `M[k][k]` and the divisor `b_prev` are
    both nonzero, and `M.PartialZero k.val` holds, `bareissEliminate M k
    b_prev` is exactly `(bareissElimMatrix M k b_prev) * M.toFn`. -/
theorem AzMatrix.toFn_bareissEliminate_eq_bareissElimMatrix_mul
    (M : AzMatrix K n n) (k : Fin n) (b_prev : K)
    (h_pivot : M.toFn k k ≠ 0) (h_b_prev : b_prev ≠ 0)
    (h_partial : M.PartialZero k.val) :
    Matrix.of (M.bareissEliminate k b_prev).toFn =
      M.bareissElimMatrix k b_prev * Matrix.of M.toFn := by
  funext i j
  rw [Matrix.of_apply, AzMatrix.toFn_bareissEliminate, Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases h_ile : i.val ≤ k.val
  · -- i ≤ k: row of bareissElimMatrix is the identity row.
    rw [if_pos h_ile]
    rw [Finset.sum_eq_single i]
    · rw [M.bareissElimMatrix_apply_diag k b_prev]
      have h_not_lt : ¬ k.val < i.val := by omega
      rw [if_neg h_not_lt, one_mul]
    · intro l _ h_li
      rw [M.bareissElimMatrix_apply_of_ne k b_prev i l (Ne.symm h_li)]
      have h_neg : ¬ (k.val < i.val ∧ l = k) := by
        intro ⟨h, _⟩; omega
      rw [if_neg h_neg, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- i > k: two contributions: `l = i` (diagonal) and `l = k` (column k).
    rw [if_neg h_ile]
    have h_ki : k.val < i.val := by omega
    have h_ik_ne : i ≠ k := by
      intro h; rw [h] at h_ki; exact Nat.lt_irrefl _ h_ki
    have h_sum :
        ∑ l, M.bareissElimMatrix k b_prev i l * M.toFn l j =
          (M.toFn k k / b_prev) * M.toFn i j +
            -(M.toFn i k / b_prev) * M.toFn k j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      rw [M.bareissElimMatrix_apply_diag k b_prev]
      rw [if_pos h_ki]
      rw [← Finset.add_sum_erase _ _
            (Finset.mem_erase.mpr ⟨Ne.symm h_ik_ne, Finset.mem_univ k⟩)]
      rw [M.bareissElimMatrix_apply_of_ne k b_prev i k h_ik_ne]
      have h_elim_k : (if k.val < i.val ∧ k = k then
            -(M.toFn i k / b_prev) else 0) = -(M.toFn i k / b_prev) :=
        if_pos ⟨h_ki, rfl⟩
      rw [h_elim_k]
      have h_rest :
          ∑ l ∈ (Finset.univ.erase i).erase k,
            M.bareissElimMatrix k b_prev i l * M.toFn l j = 0 := by
        apply Finset.sum_eq_zero
        intro l h_l
        rw [Finset.mem_erase, Finset.mem_erase] at h_l
        obtain ⟨h_lk, h_li, _⟩ := h_l
        rw [M.bareissElimMatrix_apply_of_ne k b_prev i l (Ne.symm h_li)]
        have h_neg : ¬ (k.val < i.val ∧ l = k) := fun ⟨_, h⟩ => h_lk h
        rw [if_neg h_neg, zero_mul]
      rw [h_rest, add_zero]
    rw [h_sum]
    by_cases h_jk_lt : j.val < k.val
    · -- j < k: under PartialZero, M[i][j] = 0 and M[k][j] = 0.
      rw [if_pos h_jk_lt]
      have h_M_i_j : M.toFn i j = 0 := h_partial i j (by omega) h_jk_lt
      have h_M_k_j : M.toFn k j = 0 := h_partial k j h_jk_lt h_jk_lt
      rw [h_M_i_j, h_M_k_j]
      ring
    · rw [if_neg h_jk_lt]
      by_cases h_jk : j = k
      · -- j = k: target is 0 (column k zeroed).
        rw [if_pos h_jk]
        subst h_jk
        show (0 : K) = M.toFn j j / b_prev * M.toFn i j +
          -(M.toFn i j / b_prev) * M.toFn j j
        field_simp; ring
      · -- j > k: full bareiss formula via ExactDiv.
        rw [if_neg h_jk]
        show Azurite.ExactDiv.exactDiv
              (M.toFn k k * M.toFn i j - M.toFn i k * M.toFn k j) b_prev =
            M.toFn k k / b_prev * M.toFn i j +
              -(M.toFn i k / b_prev) * M.toFn k j
        show (M.toFn k k * M.toFn i j - M.toFn i k * M.toFn k j) / b_prev = _
        field_simp; ring

theorem AzMatrix.rank_bareissEliminate
    (M : AzMatrix K n n) (k : Fin n) (b_prev : K)
    (h_pivot : M.toFn k k ≠ 0) (h_b_prev : b_prev ≠ 0)
    (h_partial : M.PartialZero k.val) :
    Matrix.rank (Matrix.of (M.bareissEliminate k b_prev).toFn) =
      Matrix.rank (Matrix.of M.toFn) := by
  rw [M.toFn_bareissEliminate_eq_bareissElimMatrix_mul k b_prev
        h_pivot h_b_prev h_partial]
  exact Matrix.rank_mul_eq_right_of_isUnit_det _ _
    (M.isUnit_det_bareissElimMatrix k b_prev h_pivot h_b_prev)

/-! ### Diagonal preservation under `bareissEliminate` -/

theorem AzMatrix.bareissEliminate_preservesDiag
    (M : AzMatrix K n n) (kp : Fin n) (b_prev : K)
    (i : Fin n) (h_i_lt : i.val < kp.val) :
    (M.bareissEliminate kp b_prev).toFn i i = M.toFn i i := by
  rw [AzMatrix.toFn_bareissEliminate]
  have h_i_le_kp : i.val ≤ kp.val := Nat.le_of_lt h_i_lt
  rw [if_pos h_i_le_kp]

/-! ### Field-case inductive correctness -/

theorem AzMatrix.bareissRankAux_eq_rank_field
    (M : AzMatrix K n n) (start : Nat) (b_prev : K)
    (h_start_le : start ≤ n)
    (h_partial : M.PartialZero start)
    (h_diag : ∀ i : Fin n, i.val < start → M.toFn i i ≠ 0)
    (h_b_prev : b_prev ≠ 0) :
    M.bareissRankAux start b_prev = Matrix.rank (Matrix.of M.toFn) := by
  induction h_k : n - start using Nat.strong_induction_on
    generalizing M start b_prev
  case _ k ih =>
    rw [AzMatrix.bareissRankAux.eq_def]
    split
    · rename_i h_lt
      set kp : Fin n := ⟨start, by omega⟩
      cases h_pivot : M.findFirstNonzero start start with
      | none =>
        simp only
        symm
        apply M.rank_eq_of_pivoted_zero_below start h_start_le h_partial h_diag
        intro i j h_i_ge h_j_ge
        exact M.findFirstNonzero_eq_none start start h_pivot i j h_i_ge h_j_ge
      | some ij =>
        obtain ⟨i_p, j_p⟩ := ij
        obtain ⟨h_i_ge, h_j_ge, h_pivot_nz⟩ :=
          M.findFirstNonzero_some_mem start start i_p j_p h_pivot
        set M_row := if i_p = kp then M else M.swapRows kp i_p with hM_row
        set M_swapped := if j_p = kp then M_row
          else M_row.swapCols kp j_p with hM_swapped
        set M_new := M_swapped.bareissEliminate kp b_prev with hM_new
        have h_rank_row :
            Matrix.rank (Matrix.of M_row.toFn) =
              Matrix.rank (Matrix.of M.toFn) := by
          by_cases h_eq : i_p = kp
          · rw [hM_row, if_pos h_eq]
          · rw [hM_row, if_neg h_eq]; exact M.rank_swapRows kp i_p
        have h_rank_swapped :
            Matrix.rank (Matrix.of M_swapped.toFn) =
              Matrix.rank (Matrix.of M.toFn) := by
          by_cases h_eq : j_p = kp
          · rw [hM_swapped, if_pos h_eq]; exact h_rank_row
          · rw [hM_swapped, if_neg h_eq]
            rw [M_row.rank_swapCols kp j_p]
            exact h_rank_row
        have h_partial_row : M_row.PartialZero start := by
          by_cases h_eq : i_p = kp
          · rw [hM_row, if_pos h_eq]; exact h_partial
          · rw [hM_row, if_neg h_eq]
            exact M.swapRows_preservesPartialZero start (by omega) h_partial
              i_p h_i_ge
        have h_partial_swapped : M_swapped.PartialZero start := by
          by_cases h_eq : j_p = kp
          · rw [hM_swapped, if_pos h_eq]; exact h_partial_row
          · rw [hM_swapped, if_neg h_eq]
            exact M_row.swapCols_preservesPartialZero start (by omega)
              h_partial_row j_p h_j_ge
        have h_M_swapped_kp_kp : M_swapped.toFn kp kp = M.toFn i_p j_p := by
          by_cases h_jp_kp : j_p = kp
          · rw [hM_swapped, if_pos h_jp_kp]
            by_cases h_ip_kp : i_p = kp
            · rw [hM_row, if_pos h_ip_kp, h_ip_kp, h_jp_kp]
            · rw [hM_row, if_neg h_ip_kp, AzMatrix.toFn_swapRows]
              rw [if_pos rfl, h_jp_kp]
          · rw [hM_swapped, if_neg h_jp_kp, AzMatrix.toFn_swapCols]
            rw [if_pos rfl]
            by_cases h_ip_kp : i_p = kp
            · rw [hM_row, if_pos h_ip_kp, h_ip_kp]
            · rw [hM_row, if_neg h_ip_kp, AzMatrix.toFn_swapRows]
              rw [if_pos rfl]
        have h_M_swapped_kp_kp_nz : M_swapped.toFn kp kp ≠ 0 := by
          rw [h_M_swapped_kp_kp]; exact h_pivot_nz
        have h_diag_swapped : ∀ i : Fin n, i.val < start →
            M_swapped.toFn i i ≠ 0 := by
          intro i h_i_lt
          have h_row_eq : M_row.toFn i i = M.toFn i i := by
            by_cases h_eq : i_p = kp
            · rw [hM_row, if_pos h_eq]
            · rw [hM_row, if_neg h_eq]
              exact M.swapRows_preservesDiag kp i_p h_i_ge i
                (by show i.val < kp.val; exact h_i_lt)
          have h_swapped_eq : M_swapped.toFn i i = M_row.toFn i i := by
            by_cases h_eq : j_p = kp
            · rw [hM_swapped, if_pos h_eq]
            · rw [hM_swapped, if_neg h_eq]
              exact M_row.swapCols_preservesDiag kp j_p h_j_ge i
                (by show i.val < kp.val; exact h_i_lt)
          rw [h_swapped_eq, h_row_eq]
          exact h_diag i h_i_lt
        -- The bareissEliminate step extends PartialZero and preserves rank.
        have h_partial_new : M_new.PartialZero (start + 1) := by
          rw [hM_new]
          exact M_swapped.bareissEliminate_preservesPartialZero start
            (by omega) b_prev h_partial_swapped
        have h_rank_new :
            Matrix.rank (Matrix.of M_new.toFn) =
              Matrix.rank (Matrix.of M.toFn) := by
          rw [hM_new]
          rw [M_swapped.rank_bareissEliminate kp b_prev h_M_swapped_kp_kp_nz
                h_b_prev h_partial_swapped]
          exact h_rank_swapped
        have h_M_new_kp_kp : M_new.toFn kp kp = M_swapped.toFn kp kp := by
          rw [hM_new, AzMatrix.toFn_bareissEliminate]
          rw [if_pos (le_refl _)]
        have h_diag_new : ∀ i : Fin n, i.val < start + 1 →
            M_new.toFn i i ≠ 0 := by
          intro i h_i_lt
          by_cases h_i_eq : i.val = start
          · have h_i_eq_kp : i = kp := Fin.ext h_i_eq
            rw [h_i_eq_kp, h_M_new_kp_kp]
            exact h_M_swapped_kp_kp_nz
          · have h_i_lt' : i.val < start := by omega
            rw [hM_new]
            rw [M_swapped.bareissEliminate_preservesDiag kp b_prev i
                  (by show i.val < kp.val; exact h_i_lt')]
            exact h_diag_swapped i h_i_lt'
        -- The new b_prev for the recursive call is M_swapped.get kp kp,
        -- which equals M.toFn i_p j_p ≠ 0.
        have h_new_b_prev_nz : M_swapped.get kp kp ≠ 0 := by
          show M_swapped.toFn kp kp ≠ 0
          exact h_M_swapped_kp_kp_nz
        have h_start_le' : start + 1 ≤ n := by omega
        have h_dec : n - (start + 1) < k := by omega
        change M_new.bareissRankAux (start + 1) (M_swapped.get kp kp) =
          (Matrix.of M.toFn).rank
        rw [ih (n - (start + 1)) h_dec M_new (start + 1) (M_swapped.get kp kp)
              h_start_le' h_partial_new h_diag_new h_new_b_prev_nz rfl]
        exact h_rank_new
    · rename_i h_ge
      split
      · rename_i hn
        set kp_last : Fin n := ⟨n - 1, by omega⟩
        cases h_pivot : M.findFirstNonzero (n - 1) (n - 1) with
        | none =>
          simp only
          symm
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
          have h_ip : i_p.val = n - 1 := by
            have : i_p.val < n := i_p.isLt; omega
          have h_jp : j_p.val = n - 1 := by
            have : j_p.val < n := j_p.isLt; omega
          have h_kp_last_eq_ip : kp_last = i_p := Fin.ext h_ip.symm
          have h_kp_last_eq_jp : kp_last = j_p := Fin.ext h_jp.symm
          simp only
          symm
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
                exact h_i_eq_ip.symm.trans h_i_eq_jp
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
      · rename_i h_zero_not
        push Not at h_zero_not
        have h_n_eq : n = 0 := Nat.le_zero.mp h_zero_not
        subst h_n_eq
        symm
        rw [show Matrix.of M.toFn = (0 : Matrix (Fin 0) (Fin 0) K) from ?_]
        · exact Matrix.rank_zero
        · funext i
          exact i.elim0

end FieldCase

/-! ### Domain case via FractionRing lifting

    Reduces to two clearly-stated lemmas, both deferred:
    * `bareissRank_map_algebraMap` — algorithm preservation under the
      injective ring homomorphism `algebraMap D (FractionRing D)`.
      Proof requires tracking the Sylvester divisibility invariant
      (mirroring `Azurite.AzMatrix.Equiv.BareissDet`) so that each
      `exactDiv` step in `D` commutes with the algebra map.
    * `rank_map_algebraMap` — `Matrix.rank` is preserved under the
      injective algebra map from `D` to its fraction field. This is the
      matrix-specific case of `IsBaseChange.finrank_eq` applied to the
      range of `mulVecLin`, viewed as an `IsLocalizedModule` instance at
      `nonZeroDivisors D`.

    With these two lemmas, `bareissRank_eq_rank` is a one-line
    composition with the Field case (`bareissRankAux_eq_rank_field`). -/

variable {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]
  [Azurite.ExactDiv D] {n : Nat}

/-! #### Helper: `algebraMap` commutes with `exactDiv` under divisibility -/

/-- When `b ∣ a` and `b ≠ 0` in `D`, the algebra map sends `exactDiv a b`
    to the field-division `(f a) / (f b)` in `FractionRing D`.
    This is the bridge between `D`'s `ExactDiv` structure and `K`'s
    field-division, used in the algorithm-preservation proof. -/
theorem AzMatrix.algebraMap_exactDiv (a b : D) (h_div : b ∣ a) (h_b_ne : b ≠ 0) :
    algebraMap D (FractionRing D) (Azurite.ExactDiv.exactDiv a b) =
      algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b := by
  have h_law : Azurite.ExactDiv.exactDiv a b * b = a :=
    Azurite.ExactDiv.exactDiv_mul_self a b h_div h_b_ne
  have h_b_K_ne : algebraMap D (FractionRing D) b ≠ 0 := by
    intro h
    have h_inj : Function.Injective (algebraMap D (FractionRing D)) :=
      IsFractionRing.injective D (FractionRing D)
    exact h_b_ne (h_inj (by rw [h, map_zero]))
  rw [eq_div_iff h_b_K_ne]
  rw [← map_mul, h_law]

/-! #### Helper: bareissEliminate commutes with `algebraMap` under Sylvester -/

/-- When the Sylvester divisibility condition holds (`b_prev` divides each
    2×2 minor of the lower-right block), `bareissEliminate` commutes
    with the algebra map: each entry of `(M.bareissEliminate kp b_prev).map f`
    equals the corresponding entry of `(M.map f).bareissEliminate kp (f b_prev)`. -/
theorem AzMatrix.bareissEliminate_map_algebraMap_of_sylvester
    (M : AzMatrix D n n) (kp : Fin n) (b_prev : D)
    (h_b_prev_ne : b_prev ≠ 0)
    (h_sylvester : ∀ i j : Fin n, kp.val < i.val → kp.val < j.val →
      b_prev ∣ (M.toFn kp kp * M.toFn i j - M.toFn i kp * M.toFn kp j)) :
    (M.bareissEliminate kp b_prev).map (algebraMap D (FractionRing D)) =
      (M.map (algebraMap D (FractionRing D))).bareissEliminate kp
        (algebraMap D (FractionRing D) b_prev) := by
  apply AzMatrix.toFn_injective
  funext i j
  rw [AzMatrix.toFn_map, AzMatrix.toFn_bareissEliminate,
      AzMatrix.toFn_bareissEliminate]
  simp only [AzMatrix.toFn_map]
  by_cases h_ile : i.val ≤ kp.val
  · rw [if_pos h_ile, if_pos h_ile]
  · rw [if_neg h_ile, if_neg h_ile]
    by_cases h_jlt : j.val < kp.val
    · rw [if_pos h_jlt, if_pos h_jlt]
    · rw [if_neg h_jlt, if_neg h_jlt]
      by_cases h_jeq : j = kp
      · rw [if_pos h_jeq, if_pos h_jeq, map_zero]
      · rw [if_neg h_jeq, if_neg h_jeq]
        -- Now we have the exactDiv case. Apply `algebraMap_exactDiv`.
        have h_ki : kp.val < i.val := by omega
        have h_kj : kp.val < j.val := by omega
        have h_div := h_sylvester i j h_ki h_kj
        rw [AzMatrix.algebraMap_exactDiv _ b_prev h_div h_b_prev_ne]
        show algebraMap D (FractionRing D) _ /
              algebraMap D (FractionRing D) b_prev = _
        congr 1
        rw [map_sub, map_mul, map_mul]

/-! #### Sylvester invariant for the bareissRank algorithm

    We package what's needed for the induction: at each step, the
    current D-matrix's lower-right block satisfies the Sylvester
    divisibility condition relative to `b_prev`. -/

/-- Sylvester divisibility invariant at step `start` with divisor `b_prev`:
    for every `(i, j)` in the lower-right `(n − start) × (n − start)` block,
    `b_prev` divides the 2×2 minor `M[start][start] · M[i][j] −
    M[i][start] · M[start][j]`. This is what `bareissEliminate` needs to
    commute with `algebraMap`. -/
def AzMatrix.SylvesterInv (M : AzMatrix D n n) (start : Nat) (b_prev : D) :
    Prop :=
  ∀ i j : Fin n, start < i.val → start < j.val →
    ∀ h : start < n, b_prev ∣
      (M.toFn ⟨start, h⟩ ⟨start, h⟩ * M.toFn i j -
       M.toFn i ⟨start, h⟩ * M.toFn ⟨start, h⟩ j)

/-! #### Initial Sylvester at `b_prev = 1` is trivial -/

theorem AzMatrix.SylvesterInv_one (M : AzMatrix D n n) :
    M.SylvesterInv 0 1 := by
  intro i j _ _ _
  exact one_dvd _

/-! #### Generic `swapRows` as `submatrix`

    The Field-only version in `Equiv.GaussRank` doesn't apply here. -/

private theorem AzMatrix.toFn_swapRows_eq_submatrix_gen
    (M : AzMatrix D n n) (i₁ i₂ : Fin n) :
    (M.swapRows i₁ i₂).toFn =
      Matrix.submatrix M.toFn (Equiv.swap i₁ i₂) id := by
  funext i j
  rw [AzMatrix.toFn_swapRows]
  show (if i = i₁ then M.toFn i₂ j
        else if i = i₂ then M.toFn i₁ j
        else M.toFn i j) = M.toFn ((Equiv.swap i₁ i₂) i) j
  by_cases h₁ : i = i₁
  · rw [if_pos h₁, h₁, Equiv.swap_apply_left]
  · by_cases h₂ : i = i₂
    · rw [if_neg h₁, if_pos h₂, h₂, Equiv.swap_apply_right]
    · rw [if_neg h₁, if_neg h₂, Equiv.swap_apply_of_ne_of_ne h₁ h₂]

/-! #### `bareissMinor` under row swap (analog of `bareissMinor_swapCols`)

    Swapping rows `k` and `i` (with `i > k`) of the reference matrix
    permutes the first row-index argument of `bareissMinor` by the same
    swap. Rows `0, …, k-1` of the Bareiss block are unaffected. -/

theorem AzMatrix.bareissMinor_swapRows
    (M : AzMatrix D n n) (k : Nat) (hk : k ≤ n) (i : Fin n) (h_i_gt : k < i.val)
    (i' j : Fin n) :
    (M.swapRows ⟨k, lt_trans h_i_gt i.isLt⟩ i).bareissMinor k hk i' j =
      M.bareissMinor k hk
        (Equiv.swap (⟨k, lt_trans h_i_gt i.isLt⟩ : Fin n) i i') j := by
  unfold AzMatrix.bareissMinor
  rw [AzMatrix.toFn_bareissBlock, AzMatrix.toFn_bareissBlock,
      AzMatrix.toFn_swapRows_eq_submatrix_gen]
  show Matrix.det (Matrix.submatrix M.toFn
      (Equiv.swap _ i ∘ AzMatrix.bareissIdx k hk i')
      (id ∘ AzMatrix.bareissIdx k hk j)) = _
  rw [Function.id_comp]
  rw [AzMatrix.bareissIdx_swap_comp hk i i' h_i_gt]

/-! #### `principalMinor` unchanged by row swap at high indices -/

theorem AzMatrix.principalMinor_swapRows_low_level
    (M : AzMatrix D n n) (k : Nat) (hk : k < n) (i : Fin n) (h_ik : k < i.val)
    (ℓ : Nat) (hℓ : ℓ < k) :
    (M.swapRows ⟨k, hk⟩ i).principalMinor ℓ (by omega) =
      M.principalMinor ℓ (by omega) := by
  rw [AzMatrix.principalMinor_eq_top_left_det,
      AzMatrix.principalMinor_eq_top_left_det]
  congr 1
  funext i' j'
  show (M.swapRows ⟨k, hk⟩ i).toFn
      (Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) i')
      (Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) j')
    = M.toFn (Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) i')
      (Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) j')
  rw [AzMatrix.toFn_swapRows]
  set i'_lift : Fin n := Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) i'
    with hi'_lift
  have h_i'_val : i'_lift.val = i'.val := rfl
  have h_neq_kp : i'_lift ≠ ⟨k, hk⟩ := by
    intro h_eq
    have : i'_lift.val = k := congrArg Fin.val h_eq
    rw [h_i'_val] at this; have := i'.isLt; omega
  have h_neq_i : i'_lift ≠ i := by
    intro h_eq
    have : i'_lift.val = i.val := congrArg Fin.val h_eq
    rw [h_i'_val] at this; have := i'.isLt; omega
  rw [if_neg h_neq_kp, if_neg h_neq_i]

/-! #### `swapRows` preserves `PartialZero` and `findFirstNonzero` semantics -/

theorem AzMatrix.swapRows_preservesPartialZero_gen
    (M : AzMatrix D n n) (start : Nat) (h_lt : start < n)
    (h_inv : M.PartialZero start) (i_p : Fin n) (h_i_ge : start ≤ i_p.val) :
    (M.swapRows ⟨start, h_lt⟩ i_p).PartialZero start := by
  intro i j h_lt_ij h_bnd
  rw [AzMatrix.toFn_swapRows]
  by_cases h_i_kp : i = ⟨start, h_lt⟩
  · rw [if_pos h_i_kp]
    apply h_inv i_p j
    · have h_j_lt : j.val < start := h_bnd
      omega
    · exact h_bnd
  · by_cases h_i_iₚ : i = i_p
    · rw [if_neg h_i_kp, if_pos h_i_iₚ]
      apply h_inv ⟨start, h_lt⟩ j h_bnd h_bnd
    · rw [if_neg h_i_kp, if_neg h_i_iₚ]
      exact h_inv i j h_lt_ij h_bnd

/-! #### `BareissInv` transitions: row-swap preservation -/

/-- Swapping rows `kp = ⟨start, _⟩` and `i_p` (with `i_p ≥ start`) in *both*
    `M_curr` and `M_ref` preserves `BareissInv` at the same level. The new
    `b_prev` is unchanged because principal minors at levels `< start` are
    unaffected by row swaps at rows `≥ start`. -/
theorem AzMatrix.BareissInv.swapRows_preserves
    {M_curr M_ref : AzMatrix D n n} {start : Nat} {b_prev : D}
    (h_inv : M_curr.BareissInv M_ref start b_prev)
    (h_lt : start < n) (i_p : Fin n) (h_i_ge : start ≤ i_p.val) :
    (M_curr.swapRows ⟨start, h_lt⟩ i_p).BareissInv
      (M_ref.swapRows ⟨start, h_lt⟩ i_p) start b_prev := by
  set kp : Fin n := ⟨start, h_lt⟩ with hkp
  by_cases h_eq : i_p = kp
  · subst h_eq
    show (M_curr.swapRows kp kp).BareissInv (M_ref.swapRows kp kp) start b_prev
    have h_id_curr : M_curr.swapRows kp kp = M_curr := by
      apply AzMatrix.toFn_injective
      funext i j
      rw [AzMatrix.toFn_swapRows]
      by_cases h : i = kp
      · rw [if_pos h, h]
      · rw [if_neg h, if_neg h]
    have h_id_ref : M_ref.swapRows kp kp = M_ref := by
      apply AzMatrix.toFn_injective
      funext i j
      rw [AzMatrix.toFn_swapRows]
      by_cases h : i = kp
      · rw [if_pos h, h]
      · rw [if_neg h, if_neg h]
    rw [h_id_curr, h_id_ref]
    exact h_inv
  · -- i_p ≠ kp, so i_p.val > start.
    have h_i_gt : start < i_p.val := by
      rcases lt_or_eq_of_le h_i_ge with h | h
      · exact h
      · exact absurd (Fin.ext h.symm : i_p = kp) h_eq
    refine ⟨h_inv.start_le_pred, ?_, ?_, ?_, ?_⟩
    · exact M_curr.swapRows_preservesPartialZero_gen start h_lt h_inv.partialZero
        i_p h_i_ge
    · intro i j hi hj
      rw [AzMatrix.toFn_swapRows]
      rw [M_ref.bareissMinor_swapRows start h_inv.start_le i_p h_i_gt i j]
      by_cases h_i_eq : i = kp
      · rw [if_pos h_i_eq, h_i_eq, Equiv.swap_apply_left]
        exact h_inv.bareiss i_p j h_i_ge hj
      · by_cases h_i_eq' : i = i_p
        · rw [if_neg h_i_eq, if_pos h_i_eq', h_i_eq', Equiv.swap_apply_right]
          exact h_inv.bareiss kp j (le_refl _) hj
        · rw [if_neg h_i_eq, if_neg h_i_eq']
          rw [Equiv.swap_apply_of_ne_of_ne h_i_eq h_i_eq']
          exact h_inv.bareiss i j hi hj
    · -- b_prev_eq: principal minor at start-1 unchanged.
      by_cases hs : 0 < start
      · simp only [dif_pos hs]
        have h_bp := h_inv.b_prev_eq
        simp only [dif_pos hs] at h_bp
        have h_pm_eq := M_ref.principalMinor_swapRows_low_level start h_lt i_p
          h_i_gt (start - 1) (by omega)
        exact h_bp.trans h_pm_eq.symm
      · simp only [dif_neg hs]
        have h_bp := h_inv.b_prev_eq
        simp only [dif_neg hs] at h_bp
        exact h_bp
    · intro ℓ hℓ h
      rw [M_ref.principalMinor_swapRows_low_level start h_lt i_p h_i_gt ℓ hℓ]
      exact h_inv.principalMinors_nz ℓ hℓ h

/-! #### `BareissInv` transitions: column-swap preservation (sans elimination) -/

/-- Swapping cols `kp = ⟨start, _⟩` and `j_p` (with `j_p ≥ start`) in *both*
    `M_curr` and `M_ref` preserves `BareissInv` at the same level. -/
theorem AzMatrix.BareissInv.swapCols_preserves
    {M_curr M_ref : AzMatrix D n n} {start : Nat} {b_prev : D}
    (h_inv : M_curr.BareissInv M_ref start b_prev)
    (h_lt : start < n) (j_p : Fin n) (h_j_ge : start ≤ j_p.val) :
    (M_curr.swapCols ⟨start, h_lt⟩ j_p).BareissInv
      (M_ref.swapCols ⟨start, h_lt⟩ j_p) start b_prev := by
  set kp : Fin n := ⟨start, h_lt⟩ with hkp
  by_cases h_eq : j_p = kp
  · subst h_eq
    have h_id_curr : M_curr.swapCols kp kp = M_curr := by
      apply AzMatrix.toFn_injective
      funext i j
      rw [AzMatrix.toFn_swapCols]
      by_cases h : j = kp
      · rw [if_pos h, h]
      · rw [if_neg h, if_neg h]
    have h_id_ref : M_ref.swapCols kp kp = M_ref := by
      apply AzMatrix.toFn_injective
      funext i j
      rw [AzMatrix.toFn_swapCols]
      by_cases h : j = kp
      · rw [if_pos h, h]
      · rw [if_neg h, if_neg h]
    rw [h_id_curr, h_id_ref]
    exact h_inv
  · -- j_p ≠ kp, so j_p.val > start.
    have h_j_gt : start < j_p.val := by
      rcases lt_or_eq_of_le h_j_ge with h | h
      · exact h
      · exact absurd (Fin.ext h.symm : j_p = kp) h_eq
    refine ⟨h_inv.start_le_pred, ?_, ?_, ?_, ?_⟩
    · exact M_curr.swapCols_preservesPartialZero start h_lt h_inv.partialZero
        j_p h_j_ge
    · intro i j hi hj
      rw [AzMatrix.toFn_swapCols]
      rw [M_ref.bareissMinor_swapCols start h_inv.start_le j_p h_j_gt i j]
      by_cases h_j_eq : j = kp
      · rw [if_pos h_j_eq, h_j_eq, Equiv.swap_apply_left]
        exact h_inv.bareiss i j_p hi h_j_ge
      · by_cases h_j_eq' : j = j_p
        · rw [if_neg h_j_eq, if_pos h_j_eq', h_j_eq', Equiv.swap_apply_right]
          exact h_inv.bareiss i kp hi (le_refl _)
        · rw [if_neg h_j_eq, if_neg h_j_eq']
          rw [Equiv.swap_apply_of_ne_of_ne h_j_eq h_j_eq']
          exact h_inv.bareiss i j hi hj
    · by_cases hs : 0 < start
      · simp only [dif_pos hs]
        have h_bp := h_inv.b_prev_eq
        simp only [dif_pos hs] at h_bp
        have h_pm_eq := M_ref.principalMinor_swapCols_low_level start h_lt j_p
          h_j_gt (start - 1) (by omega)
        exact h_bp.trans h_pm_eq.symm
      · simp only [dif_neg hs]
        have h_bp := h_inv.b_prev_eq
        simp only [dif_neg hs] at h_bp
        exact h_bp
    · intro ℓ hℓ h
      rw [M_ref.principalMinor_swapCols_low_level start h_lt j_p h_j_gt ℓ hℓ]
      exact h_inv.principalMinors_nz ℓ hℓ h

/-! #### `BareissInv` implies the Sylvester divisibility -/

/-- `BareissInv` plus a nonzero pivot at `(start, start)` (which the algorithm
    has just verified) derives the Sylvester divisibility condition needed by
    `bareissEliminate_map_algebraMap_of_sylvester`. -/
theorem AzMatrix.BareissInv.sylvester
    {M_curr M_ref : AzMatrix D n n} {start : Nat} {b_prev : D}
    (h_inv : M_curr.BareissInv M_ref start b_prev)
    (h_lt : start + 1 < n)
    (h_pivot_nz : M_curr.toFn ⟨start, by omega⟩ ⟨start, by omega⟩ ≠ 0) :
    ∀ i j : Fin n, start < i.val → start < j.val →
      b_prev ∣ M_curr.toFn ⟨start, by omega⟩ ⟨start, by omega⟩ *
                  M_curr.toFn i j -
                M_curr.toFn i ⟨start, by omega⟩ *
                  M_curr.toFn ⟨start, by omega⟩ j := by
  intro i j hi hj
  set kp : Fin n := ⟨start, by omega⟩ with hkp
  rw [h_inv.bareiss kp kp (le_refl _) (le_refl _),
      h_inv.bareiss i j (le_of_lt hi) (le_of_lt hj),
      h_inv.bareiss i kp (le_of_lt hi) (le_refl _),
      h_inv.bareiss kp j (le_refl _) (le_of_lt hj)]
  -- Now the expression is in terms of `M_ref.bareissMinor`.
  by_cases h_start_zero : start = 0
  · -- start = 0: b_prev = 1, divisibility trivial.
    have h_b_prev_one : b_prev = 1 := by
      have h_be := h_inv.b_prev_eq
      simp only [h_start_zero, Nat.lt_irrefl, dite_false] at h_be
      exact h_be
    subst h_b_prev_one
    exact one_dvd _
  · -- start = k + 1, apply Prop 8.20.
    have h_start_pos : 0 < start := Nat.pos_of_ne_zero h_start_zero
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h_start_zero
    have h_b_prev_eq : b_prev = M_ref.principalMinor k (by omega) := by
      have h_be := h_inv.b_prev_eq
      simp only [show 0 < k + 1 from by omega, dif_pos] at h_be
      have h_sub : (k + 1) - 1 = k := by omega
      have : b_prev = M_ref.principalMinor ((k + 1) - 1) (by omega) := h_be
      simp only [h_sub] at this
      exact this
    -- The level-(k+1) principal minor equals M_curr.toFn kp kp.
    have h_kp_pm : M_curr.toFn kp kp = M_ref.principalMinor (k + 1) (by omega) := by
      rw [h_inv.bareiss kp kp (le_refl _) (le_refl _)]
      rfl
    have h_pm_kp_nz : M_ref.principalMinor (k + 1) (by omega) ≠ 0 := by
      rw [← h_kp_pm]; exact h_pivot_nz
    have h_pms : ∀ ℓ : Nat, ℓ ≤ k + 1 → (h : ℓ < n) →
        M_ref.principalMinor ℓ h ≠ 0 := by
      intro ℓ hℓ h
      rcases lt_or_eq_of_le hℓ with hℓ' | hℓ'
      · exact h_inv.principalMinors_nz ℓ hℓ' h
      · subst hℓ'; exact h_pm_kp_nz
    have h_rec := M_ref.bareissMinor_recurrence_domain k i j
      (by omega) (by omega) h_pms
    -- Use h_rec: bareissMinor (k+2) i j * principalMinor k = (the 2x2 minor)
    use M_ref.bareissMinor (k + 2) (by omega) i j
    -- Target: M_ref.bareissMinor (k+1) _ kp kp * M_ref.bareissMinor (k+1) _ i j
    --   - M_ref.bareissMinor (k+1) _ i kp * M_ref.bareissMinor (k+1) _ kp j
    --   = b_prev * M_ref.bareissMinor (k+2) _ i j
    have h_target_eq :
        M_ref.bareissMinor (k + 1) h_inv.start_le kp kp =
          M_ref.principalMinor (k + 1) (by omega) := rfl
    rw [h_target_eq]
    have : b_prev * M_ref.bareissMinor (k + 2) (by omega) i j =
        M_ref.bareissMinor (k + 2) (by omega) i j * M_ref.principalMinor k (by omega) := by
      rw [h_b_prev_eq]; ring
    rw [this, h_rec]

/-! #### Map commutes with swaps -/

theorem AzMatrix.map_swapRows {E : Type _} (f : D → E)
    (M : AzMatrix D n n) (i j : Fin n) :
    (M.swapRows i j).map f = (M.map f).swapRows i j := by
  apply AzMatrix.toFn_injective
  funext r c
  rw [AzMatrix.toFn_map, AzMatrix.toFn_swapRows, AzMatrix.toFn_swapRows]
  by_cases h₁ : r = i
  · rw [if_pos h₁, if_pos h₁, AzMatrix.toFn_map]
  · by_cases h₂ : r = j
    · rw [if_neg h₁, if_pos h₂, if_neg h₁, if_pos h₂, AzMatrix.toFn_map]
    · rw [if_neg h₁, if_neg h₂, if_neg h₁, if_neg h₂, AzMatrix.toFn_map]

theorem AzMatrix.map_swapCols {E : Type _} (f : D → E)
    (M : AzMatrix D n n) (i j : Fin n) :
    (M.swapCols i j).map f = (M.map f).swapCols i j := by
  apply AzMatrix.toFn_injective
  funext r c
  rw [AzMatrix.toFn_map, AzMatrix.toFn_swapCols, AzMatrix.toFn_swapCols]
  by_cases h₁ : c = i
  · rw [if_pos h₁, if_pos h₁, AzMatrix.toFn_map]
  · by_cases h₂ : c = j
    · rw [if_neg h₁, if_pos h₂, if_neg h₁, if_pos h₂, AzMatrix.toFn_map]
    · rw [if_neg h₁, if_neg h₂, if_neg h₁, if_neg h₂, AzMatrix.toFn_map]

/-! #### Generic spec lemmas for `findFirstNonzero` (Field-free) -/

theorem AzMatrix.findFirstNonzeroAux_some_mem_gen
    (M : AzMatrix D n n) (c_start : Nat) :
    ∀ (i : Nat) (i' j' : Fin n),
      M.findFirstNonzeroAux i c_start = some (i', j') →
        i ≤ i'.val ∧ c_start ≤ j'.val ∧ M.toFn i' j' ≠ 0 := by
  intro i i' j'
  apply AzMatrix.findFirstNonzeroAux.induct M c_start
    (motive := fun i => ∀ i' j' : Fin n,
      M.findFirstNonzeroAux i c_start = some (i', j') →
        i ≤ i'.val ∧ c_start ≤ j'.val ∧ M.toFn i' j' ≠ 0)
  · intro i h_lt j h_match i' j' h_rec
    rw [AzMatrix.findFirstNonzeroAux.eq_def] at h_rec
    simp only [dif_pos h_lt, h_match, Option.some.injEq, Prod.mk.injEq] at h_rec
    obtain ⟨h_i', h_j'⟩ := h_rec
    refine ⟨?_, ?_, ?_⟩
    · rw [← h_i']
    · rw [← h_j']
      exact M.findPivotAux_some_le ⟨i, h_lt⟩ c_start j h_match
    · rw [← h_i', ← h_j']
      exact M.findPivotAux_some_nonzero ⟨i, h_lt⟩ c_start j h_match
  · intro i h_lt h_match ih i' j' h_rec
    have h_rec_eq : M.findFirstNonzeroAux (i + 1) c_start = some (i', j') := by
      rw [AzMatrix.findFirstNonzeroAux.eq_def] at h_rec
      simp only [dif_pos h_lt, h_match] at h_rec
      exact h_rec
    obtain ⟨h_a, h_b, h_c⟩ := ih i' j' h_rec_eq
    exact ⟨by omega, h_b, h_c⟩
  · intro i h_ge i' j' h_rec
    exfalso
    rw [AzMatrix.findFirstNonzeroAux.eq_def] at h_rec
    simp [h_ge] at h_rec

theorem AzMatrix.findFirstNonzero_some_mem_gen
    (M : AzMatrix D n n) (r_start c_start : Nat) (i' j' : Fin n)
    (h : M.findFirstNonzero r_start c_start = some (i', j')) :
    r_start ≤ i'.val ∧ c_start ≤ j'.val ∧ M.toFn i' j' ≠ 0 :=
  M.findFirstNonzeroAux_some_mem_gen c_start r_start i' j' h

/-! #### `findPivotAux` and `findFirstNonzero` agree under injective ring hom -/

theorem AzMatrix.findPivotAux_map_eq_of_injective
    {E : Type _} [CommRing E] [DecidableEq E] (M : AzMatrix D n n)
    (f : D →+* E) (h_inj : Function.Injective f) (k : Fin n) (j : Nat) :
    (M.map f).findPivotAux k j = M.findPivotAux k j := by
  apply AzMatrix.findPivotAux.induct M k
    (motive := fun j =>
      (M.map f).findPivotAux k j = M.findPivotAux k j)
  · intro j h_lt h_zero ih
    have h_map_zero : (M.map f).get k ⟨j, h_lt⟩ = 0 := by
      show (M.map f).toFn k ⟨j, h_lt⟩ = 0
      rw [AzMatrix.toFn_map]
      show f (M.get k ⟨j, h_lt⟩) = 0
      rw [h_zero, map_zero]
    conv_lhs => rw [AzMatrix.findPivotAux.eq_def]
    conv_rhs => rw [AzMatrix.findPivotAux.eq_def]
    simp only [dif_pos h_lt, if_pos h_map_zero, if_pos h_zero]
    exact ih
  · intro j h_lt h_nz
    have h_map_nz : (M.map f).get k ⟨j, h_lt⟩ ≠ 0 := by
      intro h
      apply h_nz
      have h' : (M.map f).toFn k ⟨j, h_lt⟩ = 0 := h
      rw [AzMatrix.toFn_map] at h'
      have h_inj_eq : M.toFn k ⟨j, h_lt⟩ = 0 := h_inj (by rw [h', map_zero])
      exact h_inj_eq
    conv_lhs => rw [AzMatrix.findPivotAux.eq_def]
    conv_rhs => rw [AzMatrix.findPivotAux.eq_def]
    simp only [dif_pos h_lt, if_neg h_map_nz, if_neg h_nz]
  · intro j h_ge
    conv_lhs => rw [AzMatrix.findPivotAux.eq_def]
    conv_rhs => rw [AzMatrix.findPivotAux.eq_def]
    simp only [dif_neg h_ge]

theorem AzMatrix.findFirstNonzeroAux_map_eq_of_injective
    {E : Type _} [CommRing E] [DecidableEq E] (M : AzMatrix D n n)
    (f : D →+* E) (h_inj : Function.Injective f) (c_start i : Nat) :
    (M.map f).findFirstNonzeroAux i c_start =
      M.findFirstNonzeroAux i c_start := by
  apply AzMatrix.findFirstNonzeroAux.induct M c_start
    (motive := fun i =>
      (M.map f).findFirstNonzeroAux i c_start =
        M.findFirstNonzeroAux i c_start)
  · intro i h_lt j h_match
    have h_map_match :
        (M.map f).findPivotAux ⟨i, h_lt⟩ c_start = some j := by
      rw [M.findPivotAux_map_eq_of_injective f h_inj]; exact h_match
    conv_lhs => rw [AzMatrix.findFirstNonzeroAux.eq_def]
    conv_rhs => rw [AzMatrix.findFirstNonzeroAux.eq_def]
    simp only [dif_pos h_lt, h_match, h_map_match]
  · intro i h_lt h_match ih
    have h_map_match :
        (M.map f).findPivotAux ⟨i, h_lt⟩ c_start = none := by
      rw [M.findPivotAux_map_eq_of_injective f h_inj]; exact h_match
    conv_lhs => rw [AzMatrix.findFirstNonzeroAux.eq_def]
    conv_rhs => rw [AzMatrix.findFirstNonzeroAux.eq_def]
    simp only [dif_pos h_lt, h_match, h_map_match]
    exact ih
  · intro i h_ge
    conv_lhs => rw [AzMatrix.findFirstNonzeroAux.eq_def]
    conv_rhs => rw [AzMatrix.findFirstNonzeroAux.eq_def]
    simp only [dif_neg h_ge]

theorem AzMatrix.findFirstNonzero_map_eq_of_injective
    {E : Type _} [CommRing E] [DecidableEq E] (M : AzMatrix D n n)
    (f : D →+* E) (h_inj : Function.Injective f) (r c : Nat) :
    (M.map f).findFirstNonzero r c = M.findFirstNonzero r c :=
  M.findFirstNonzeroAux_map_eq_of_injective f h_inj c r

/-! #### Initial `BareissInv` (start = 0, b_prev = 1) -/

theorem AzMatrix.BareissInv_zero (M : AzMatrix D n n) (_h_n : 0 < n) :
    M.BareissInv M 0 1 := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  · intro i j _ _
    rw [M.bareissMinor_zero (Nat.zero_le _) i j]
  · simp only [Nat.lt_irrefl, dite_false]
  · intro _ h; exact absurd h (Nat.not_lt_zero _)

/-! #### Main lemma: BareissInv ⇒ algorithm output preserved under algebraMap -/

theorem AzMatrix.bareissRankAux_map_algebraMap
    (M_curr M_ref : AzMatrix D n n) (start : Nat) (b_prev : D)
    (h_inv : M_curr.BareissInv M_ref start b_prev) :
    M_curr.bareissRankAux start b_prev =
      (M_curr.map (algebraMap D (FractionRing D))).bareissRankAux start
        (algebraMap D (FractionRing D) b_prev) := by
  classical
  set f : D →+* FractionRing D := algebraMap D (FractionRing D) with hf
  have h_inj : Function.Injective f := IsFractionRing.injective D _
  induction h_k : n - start using Nat.strong_induction_on
    generalizing M_curr M_ref b_prev start
  case _ k ih =>
    rw [AzMatrix.bareissRankAux.eq_def, AzMatrix.bareissRankAux.eq_def]
    split
    · rename_i h_lt
      set kp : Fin n := ⟨start, by omega⟩ with hkp
      have h_find_eq :
          (M_curr.map f).findFirstNonzero start start =
            M_curr.findFirstNonzero start start :=
        M_curr.findFirstNonzero_map_eq_of_injective f h_inj start start
      cases h_pivot : M_curr.findFirstNonzero start start with
      | none =>
        simp only [h_find_eq.trans h_pivot]
      | some ij =>
        obtain ⟨i_p, j_p⟩ := ij
        obtain ⟨h_i_ge, h_j_ge, h_pivot_nz⟩ :=
          M_curr.findFirstNonzero_some_mem_gen start start i_p j_p h_pivot
        have h_find_K : (M_curr.map f).findFirstNonzero start start =
            some (i_p, j_p) := h_find_eq.trans h_pivot
        simp only [h_find_K]
        -- Apply row swap to both sides.
        have h_inv_row :=
          h_inv.swapRows_preserves (by omega) i_p h_i_ge
        have h_eq_row : (if i_p = kp then M_curr else M_curr.swapRows kp i_p) =
            M_curr.swapRows kp i_p ∨
            (if i_p = kp then M_curr else M_curr.swapRows kp i_p) = M_curr := by
          by_cases h : i_p = kp
          · right; rw [if_pos h]
          · left; rw [if_neg h]
        set M_row := if i_p = kp then M_curr else M_curr.swapRows kp i_p
          with hM_row
        set M_ref_row := if i_p = kp then M_ref else M_ref.swapRows kp i_p
          with hM_ref_row
        have h_inv_row' : M_row.BareissInv M_ref_row start b_prev := by
          by_cases h : i_p = kp
          · rw [hM_row, hM_ref_row, if_pos h, if_pos h]; exact h_inv
          · rw [hM_row, hM_ref_row, if_neg h, if_neg h]; exact h_inv_row
        have h_map_row :
            ((if i_p = kp then M_curr else M_curr.swapRows kp i_p).map f) =
            (if i_p = kp then M_curr.map f else (M_curr.map f).swapRows kp i_p) := by
          by_cases h : i_p = kp
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h]; exact M_curr.map_swapRows f kp i_p
        -- Apply col swap to both sides.
        set M_swapped := if j_p = kp then M_row else M_row.swapCols kp j_p
          with hM_swapped
        set M_ref_swapped :=
          if j_p = kp then M_ref_row else M_ref_row.swapCols kp j_p
          with hM_ref_swapped
        have h_inv_swapped' : M_swapped.BareissInv M_ref_swapped start b_prev := by
          by_cases h : j_p = kp
          · rw [hM_swapped, hM_ref_swapped, if_pos h, if_pos h]; exact h_inv_row'
          · rw [hM_swapped, hM_ref_swapped, if_neg h, if_neg h]
            exact h_inv_row'.swapCols_preserves (by omega) j_p h_j_ge
        have h_map_swapped :
            (M_swapped.map f) =
              if j_p = kp then M_row.map f else (M_row.map f).swapCols kp j_p := by
          by_cases h : j_p = kp
          · rw [hM_swapped, if_pos h, if_pos h]
          · rw [hM_swapped, if_neg h, if_neg h]; exact M_row.map_swapCols f kp j_p
        -- M_swapped[kp][kp] ≠ 0.
        have h_pivot_swapped : M_swapped.toFn kp kp ≠ 0 := by
          have h_M_swapped_kp_kp : M_swapped.toFn kp kp = M_curr.toFn i_p j_p := by
            by_cases h_jp_kp : j_p = kp
            · rw [hM_swapped, if_pos h_jp_kp]
              by_cases h_ip_kp : i_p = kp
              · rw [hM_row, if_pos h_ip_kp, h_ip_kp, h_jp_kp]
              · rw [hM_row, if_neg h_ip_kp, AzMatrix.toFn_swapRows]
                rw [if_pos rfl, h_jp_kp]
            · rw [hM_swapped, if_neg h_jp_kp, AzMatrix.toFn_swapCols]
              rw [if_pos rfl]
              by_cases h_ip_kp : i_p = kp
              · rw [hM_row, if_pos h_ip_kp, h_ip_kp]
              · rw [hM_row, if_neg h_ip_kp, AzMatrix.toFn_swapRows]
                rw [if_pos rfl]
          rw [h_M_swapped_kp_kp]; exact h_pivot_nz
        -- findPivot M_swapped kp = some kp.
        have h_findPivot_swapped : M_swapped.findPivot kp = some kp := by
          show M_swapped.findPivotAux kp kp.val = some kp
          rw [AzMatrix.findPivotAux.eq_def]
          have h_kp_lt : kp.val < n := kp.isLt
          rw [dif_pos h_kp_lt]
          have h_get_nz : M_swapped.get kp ⟨kp.val, h_kp_lt⟩ ≠ 0 := by
            show M_swapped.toFn kp ⟨kp.val, h_kp_lt⟩ ≠ 0
            have h_eq : (⟨kp.val, h_kp_lt⟩ : Fin n) = kp := Fin.ext rfl
            rw [h_eq]; exact h_pivot_swapped
          rw [if_neg h_get_nz]
        -- Apply step_no_swap to get BareissInv at start + 1.
        have h_inv_new := h_inv_swapped'.step_no_swap h_lt h_findPivot_swapped
        -- The map version: (M_swapped.bareissEliminate kp b_prev).map f =
        --   (M_swapped.map f).bareissEliminate kp (f b_prev).
        have h_sylv := h_inv_swapped'.sylvester h_lt h_pivot_swapped
        have h_b_prev_ne : b_prev ≠ 0 := by
          rcases Nat.eq_zero_or_pos start with hs | hs
          · subst hs
            have h_be := h_inv.b_prev_eq
            simp only [Nat.lt_irrefl, dite_false] at h_be
            rw [h_be]; exact one_ne_zero
          · have h_be := h_inv.b_prev_eq
            simp only [dif_pos hs] at h_be
            rw [h_be]
            exact h_inv.principalMinors_nz (start - 1) (by omega) (by omega)
        have h_bareiss_map :
            (M_swapped.bareissEliminate kp b_prev).map f =
              (M_swapped.map f).bareissEliminate kp (f b_prev) :=
          M_swapped.bareissEliminate_map_algebraMap_of_sylvester kp b_prev
            h_b_prev_ne h_sylv
        -- The new b_prev (= M_swapped.get kp kp) under algebraMap.
        have h_new_b_prev_map :
            (M_swapped.map f).get kp kp = f (M_swapped.get kp kp) := by
          show (M_swapped.map f).toFn kp kp = f (M_swapped.toFn kp kp)
          rw [AzMatrix.toFn_map]
        -- Decrement step.
        have h_dec : n - (start + 1) < k := by omega
        -- Apply IH to (M_swapped.bareissEliminate kp b_prev, M_ref_swapped,
        -- start + 1, M_swapped.get kp kp).
        have h_rec := ih (n - (start + 1)) h_dec
          (M_swapped.bareissEliminate kp b_prev) M_ref_swapped (start + 1)
          (M_swapped.get kp kp) h_inv_new rfl
        -- Combine: at this point the goal is
        --   (M_swapped_D .bareissEliminate kp b_prev).bareissRankAux ... =
        --     (M_swapped_K .bareissEliminate kp (f b_prev)).bareissRankAux ...
        -- where M_swapped_D = (let-bound D-side) and M_swapped_K = (let-bound K-side).
        -- We collapse both let-binds into M_swapped and M_swapped.map f.
        have h_rhs_M_row :
            (if i_p = kp then M_curr.map f else (M_curr.map f).swapRows kp i_p) =
              M_row.map f := h_map_row.symm
        have h_rhs_M_swapped :
            (if j_p = kp then
                if i_p = kp then M_curr.map f else (M_curr.map f).swapRows kp i_p
              else
                (if i_p = kp then M_curr.map f else
                  (M_curr.map f).swapRows kp i_p).swapCols kp j_p) =
              M_swapped.map f := by
          rw [h_rhs_M_row]; exact h_map_swapped.symm
        rw [h_rhs_M_swapped]
        rw [h_rec, h_bareiss_map]
        congr 1
        exact h_new_b_prev_map.symm
    · rename_i h_ge
      split
      · rename_i hn
        have h_find_eq : (M_curr.map f).findFirstNonzero (n - 1) (n - 1) =
            M_curr.findFirstNonzero (n - 1) (n - 1) :=
          M_curr.findFirstNonzero_map_eq_of_injective f h_inj (n - 1) (n - 1)
        cases h_pivot : M_curr.findFirstNonzero (n - 1) (n - 1) with
        | none =>
          simp only [h_find_eq.trans h_pivot]
        | some ij =>
          simp only [h_find_eq.trans h_pivot]
      · rename_i hn
        rfl

/-- The bareiss algorithm's rank output commutes with the algebra map
    into the fraction field. (Algorithm preservation.) -/
theorem AzMatrix.bareissRank_map_algebraMap (M : AzMatrix D n n) :
    M.bareissRank =
      (M.map (algebraMap D (FractionRing D))).bareissRank := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- n = 0: both return 0.
    subst hn
    unfold AzMatrix.bareissRank AzMatrix.bareissRankAux
    rfl
  · unfold AzMatrix.bareissRank
    have h := M.bareissRankAux_map_algebraMap M 0 1 (M.BareissInv_zero hn)
    rw [h, map_one]

/-! #### `Matrix.rank` base change under `algebraMap D (FractionRing D)`

    Strategy: use `Matrix.rank_eq_finrank_span_cols` to reduce to a
    comparison of column-span finranks. Recognize the K-span as the
    `Submodule.localized'` of the D-span, then chain
    `IsLocalizedModule.lift_rank_eq` (which gives D-rank equality of the
    submodule and its localization) with `IsLocalization.rank_eq`
    (which converts D-rank of a K-module to K-rank). -/

/-- `Matrix.rank` is preserved under the injective algebra map from `D`
    to `FractionRing D`. (Matrix-specific base change.) -/
theorem AzMatrix.rank_map_algebraMap (M : AzMatrix D n n) :
    Matrix.rank (Matrix.of (M.map (algebraMap D (FractionRing D))).toFn) =
      Matrix.rank (Matrix.of M.toFn) := by
  classical
  set K := FractionRing D with hK
  set f : D →+* K := algebraMap D K with hf
  set p : Submonoid D := nonZeroDivisors D with hp
  set A : Matrix (Fin n) (Fin n) D := Matrix.of M.toFn with hA
  set B : Matrix (Fin n) (Fin n) K := Matrix.of (M.map f).toFn with hB
  -- The entrywise algebra map as a D-linear map, built from the
  -- per-coordinate algebra map via `IsLocalizedModule.pi`. The result
  -- has the form `LinearMap.pi (fun i => (Algebra.linearMap D K) ∘ proj i)`.
  haveI : IsLocalizedModule p
      (LinearMap.pi (fun i : Fin n =>
        (Algebra.linearMap D K).comp
          (LinearMap.proj (R := D) (φ := fun _ : Fin n => D) i))) :=
    IsLocalizedModule.pi p (fun _ : Fin n => Algebra.linearMap D K)
  set ψ : (Fin n → D) →ₗ[D] (Fin n → K) :=
    LinearMap.pi (fun i =>
      (Algebra.linearMap D K).comp (LinearMap.proj (R := D) (φ := fun _ => D) i))
    with hψ
  -- Express B in terms of A and the algebra map.
  have hBA : B = A.map f := by
    funext i j
    show (M.map f).toFn i j = f (M.toFn i j)
    rw [AzMatrix.toFn_map]
  -- Convert ranks to column-span finranks.
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  -- Identify Set.range B.col = ψ '' Set.range A.col.
  have h_cols : Set.range B.col = ψ '' Set.range A.col := by
    ext c
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨A.col j, ⟨j, rfl⟩, ?_⟩
      funext i
      show (Algebra.linearMap D K) (A.col j i) = B.col j i
      rw [hBA]
      show f (A i j) = (A.map f) i j
      simp [Matrix.map]
    · rintro ⟨c', ⟨j, rfl⟩, rfl⟩
      refine ⟨j, ?_⟩
      funext i
      show B.col j i = (Algebra.linearMap D K) (A.col j i)
      rw [hBA]
      show (A.map f) i j = f (A i j)
      simp [Matrix.map]
  rw [h_cols]
  -- Recognize span K (ψ '' s) as the K-localization of span D s.
  rw [← Submodule.localized'_span K p ψ (Set.range A.col)]
  -- Apply the rank chain.
  -- First: finrank K (M'.localized' K p ψ) = finrank D (M'.localized' K p ψ) via IsLocalization.
  -- Then: finrank D (M'.localized' K p ψ) = finrank D M' via IsLocalizedModule.
  set M' : Submodule D (Fin n → D) := Submodule.span D (Set.range A.col) with hM'
  rw [show Module.finrank K (M'.localized' K p ψ) =
        Module.finrank D (M'.localized' K p ψ) from ?_]
  · exact IsLocalizedModule.finrank_eq p (M'.toLocalized' K p ψ) le_rfl
  · -- finrank K (X) = finrank D (X) where X is a K-module: this is
    -- `IsLocalization.rank_eq` (rank equality), then `Cardinal.toNat`
    -- (or unfolding `finrank`).
    show Module.finrank K (M'.localized' K p ψ) =
      Module.finrank D (M'.localized' K p ψ)
    unfold Module.finrank
    rw [IsLocalization.rank_eq K p le_rfl]

/-- The rank of `M : AzMatrix D n n` computed by the fraction-free
    Dodgson–Jordan–Bareiss algorithm agrees with Mathlib's `Matrix.rank`
    over the integral domain `D`. -/
theorem AzMatrix.bareissRank_eq_rank (M : AzMatrix D n n) :
    M.bareissRank = Matrix.rank (Matrix.of M.toFn) := by
  classical
  rw [M.bareissRank_map_algebraMap]
  have h_lift :=
    (M.map (algebraMap D (FractionRing D))).bareissRankAux_eq_rank_field
      0 1 (Nat.zero_le _)
      (by intro _ _ _ h; exact absurd h (Nat.not_lt_zero _))
      (by intro _ h; exact absurd h (Nat.not_lt_zero _))
      one_ne_zero
  exact h_lift.trans M.rank_map_algebraMap

end Azurite
