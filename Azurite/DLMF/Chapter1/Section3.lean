/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# DLMF §1.3: Determinants, Linear Operators, and Spectral Expansions

Formalizations of the equations of the NIST Digital Library of Mathematical Functions,
<https://dlmf.nist.gov/1.3>, one theorem per equation, named `dlmf_1_3_N`; statements made in
the prose between equations are named `dlmf_1_3_i_<topic>` after their subsection.  Each is
either a thin restatement of a Mathlib lemma (named in the docstring) or proven here.  The
ledger `docs/dlmf_plan.md` maps every equation to its theorem.

## §1.3(i) Determinants: elementary properties

* 1.3.1–1.3.2 `dlmf_1_3_1`, `dlmf_1_3_2`: the `2 × 2` and `3 × 3` determinants
  (`Matrix.det_fin_two`, `Matrix.det_fin_three`).
* 1.3.3–1.3.4 `minor`, `cofactor` (`dlmf_1_3_3`, `dlmf_1_3_3_adjugate`: the cofactors are the
  transpose of `Matrix.adjugate`), `dlmf_1_3_4` (expansion by a row, `Matrix.det_succ_row`).
* The row and column operations `dlmf_1_3_i_swap_rows`, `dlmf_1_3_i_swap_cols`,
  `dlmf_1_3_i_row_eq`, `dlmf_1_3_i_col_eq`, `dlmf_1_3_i_smul_row`, `dlmf_1_3_i_smul_col`,
  `dlmf_1_3_i_add_smul_row`, `dlmf_1_3_i_add_smul_col` (`Matrix.det_permute`,
  `det_zero_of_row_eq`, `det_updateRow_smul`, `det_updateRow_add_smul_self` and the column
  versions).
* 1.3.5–1.3.7 `dlmf_1_3_5`–`dlmf_1_3_7`: `det Aᵀ = det A`, `det A⁻¹ = 1 / det A`,
  `det(AB) = det A det B` (`Matrix.det_transpose`, `det_nonsing_inv`, `det_mul`).
* `dlmf_1_3_i_isUpperTriangular`, `dlmf_1_3_i_isLowerTriangular` (Mathlib's
  `Matrix.IsUpperTriangular`, `IsLowerTriangular`), `dlmf_1_3_i_det_upperTriangular`,
  `dlmf_1_3_i_det_lowerTriangular`, `dlmf_1_3_i_det_diagonal`: the determinant of a triangular
  or diagonal matrix is the product of the diagonal elements (`Matrix.det_of_isUpperTriangular`,
  `det_of_isLowerTriangular`, `det_diagonal`).
-/

namespace Azurite.DLMF

open Finset Matrix

/-! ### §1.3(i) Determinants: elementary properties -/

/-! #### Formal calculation of determinants -/

/-- **DLMF 1.3.1**: for `n = 2`, `det [aⱼₖ] = a₁₁ a₂₂ − a₁₂ a₂₁` (`Matrix.det_fin_two`). -/
theorem dlmf_1_3_1 (A : Matrix (Fin 2) (Fin 2) ℂ) : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 :=
  det_fin_two A

/-- **DLMF 1.3.2**: for `n = 3`, the expansion by the first row in `2 × 2` determinants and the
full expansion (`Matrix.det_fin_three`). -/
theorem dlmf_1_3_2 (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.det = A 0 0 * !![A 1 1, A 1 2; A 2 1, A 2 2].det - A 0 1 * !![A 1 0, A 1 2; A 2 0, A 2 2].det
        + A 0 2 * !![A 1 0, A 1 1; A 2 0, A 2 1].det ∧
      A.det = A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
        A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 := by
  refine ⟨?_, det_fin_three A⟩
  rw [det_fin_two_of, det_fin_two_of, det_fin_two_of, det_fin_three]
  ring

/-- The minor `Mⱼₖ` of the entry `aⱼₖ` of an `(n + 1)`-th order determinant: the `n`-th order
determinant obtained by deleting the `j`-th row and the `k`-th column
(`Matrix.submatrix` along `Fin.succAbove`). -/
noncomputable def minor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j k : Fin (n + 1)) :
    ℂ :=
  (A.submatrix j.succAbove k.succAbove).det

/-- **DLMF 1.3.3**: the cofactor `Aⱼₖ = (−1)^(j + k) Mⱼₖ`. -/
noncomputable def cofactor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (j k : Fin (n + 1)) : ℂ :=
  (-1) ^ ((j : ℕ) + k) * minor A j k

theorem dlmf_1_3_3 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j k : Fin (n + 1)) :
    cofactor A j k = (-1) ^ ((j : ℕ) + k) * minor A j k :=
  rfl

/-- **DLMF 1.3.3**, the cofactors form the transpose of Mathlib's adjugate
(`Matrix.adjugate_fin_succ_eq_det_submatrix`). -/
theorem dlmf_1_3_3_adjugate {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (j k : Fin (n + 1)) : A.adjugate k j = cofactor A j k := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  rfl

/-- **DLMF 1.3.4**: expansion of an `(n + 1)`-th order determinant by its `j`-th row,
`det [aⱼₖ] = ∑ₗ aⱼₗ Aⱼₗ` (`Matrix.det_succ_row`). -/
theorem dlmf_1_3_4 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
    A.det = ∑ l, A j l * cofactor A j l := by
  rw [det_succ_row A j]
  refine sum_congr rfl fun l _ => ?_
  unfold cofactor minor
  ring

/-- **DLMF §1.3(i)**, row operations: interchanging two rows changes the sign of the determinant
(`Matrix.det_permute`, `Equiv.Perm.sign_swap`). -/
theorem dlmf_1_3_i_swap_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j) :
    (A.submatrix (Equiv.swap i j) id).det = -A.det := by
  rw [det_permute, Equiv.Perm.sign_swap h]
  simp

/-- **DLMF §1.3(i)**: interchanging two columns changes the sign (`Matrix.det_permute'`). -/
theorem dlmf_1_3_i_swap_cols {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j) :
    (A.submatrix id (Equiv.swap i j)).det = -A.det := by
  rw [det_permute', Equiv.Perm.sign_swap h]
  simp

/-- **DLMF §1.3(i)**: two identical rows give a zero determinant
(`Matrix.det_zero_of_row_eq`). -/
theorem dlmf_1_3_i_row_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {i j : Fin n} (h : i ≠ j)
    (hA : A i = A j) : A.det = 0 :=
  det_zero_of_row_eq h hA

/-- **DLMF §1.3(i)**: two identical columns give a zero determinant
(`Matrix.det_zero_of_column_eq`). -/
theorem dlmf_1_3_i_col_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {i j : Fin n} (h : i ≠ j)
    (hA : ∀ k, A k i = A k j) : A.det = 0 :=
  det_zero_of_column_eq h hA

/-- **DLMF §1.3(i)**: multiplying a row by `μ` multiplies the determinant by `μ`
(`Matrix.det_updateRow_smul`). -/
theorem dlmf_1_3_i_smul_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (μ : ℂ) :
    (A.updateRow j (μ • A j)).det = μ * A.det := by
  rw [det_updateRow_smul, updateRow_eq_self]

/-- **DLMF §1.3(i)**: multiplying a column by `μ` multiplies the determinant by `μ`
(`Matrix.det_updateCol_smul`). -/
theorem dlmf_1_3_i_smul_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (μ : ℂ) :
    (A.updateCol j (μ • fun k => A k j)).det = μ * A.det := by
  rw [det_updateCol_smul, updateCol_eq_self]

/-- **DLMF §1.3(i)**: adding `μ` times a row to another row leaves the determinant unchanged
(`Matrix.det_updateRow_add_smul_self`). -/
theorem dlmf_1_3_i_add_smul_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j)
    (μ : ℂ) : (A.updateRow i (A i + μ • A j)).det = A.det :=
  det_updateRow_add_smul_self A h μ

/-- **DLMF §1.3(i)**: adding `μ` times a column to another column leaves the determinant
unchanged (`Matrix.det_updateCol_add_smul_self`). -/
theorem dlmf_1_3_i_add_smul_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j)
    (μ : ℂ) : (A.updateCol i fun k => A k i + μ • A k j).det = A.det :=
  det_updateCol_add_smul_self A h μ

/-! #### Relationships between determinants -/

/-- **DLMF 1.3.5**: `det(Aᵀ) = det A` (`Matrix.det_transpose`). -/
theorem dlmf_1_3_5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Aᵀ.det = A.det :=
  det_transpose A

/-- **DLMF 1.3.6**: `det(A⁻¹) = 1 / det A` (`Matrix.det_nonsing_inv`; with Mathlib's inverse
and `1 / 0 = 0` this holds for every `A`, not only for `det A ≠ 0`). -/
theorem dlmf_1_3_6 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : A⁻¹.det = 1 / A.det := by
  rw [det_nonsing_inv, Ring.inverse_eq_inv', one_div]

/-- **DLMF 1.3.7**: `det(AB) = det A det B` (`Matrix.det_mul`). -/
theorem dlmf_1_3_7 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : (A * B).det = A.det * B.det :=
  det_mul A B

/-! #### Determinants of upper/lower triangular and diagonal matrices -/

/-- **DLMF §1.3(i)**: `A` is upper triangular if `aᵢⱼ = 0` for `i > j`
(Mathlib's `Matrix.IsUpperTriangular`). -/
theorem dlmf_1_3_i_isUpperTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.IsUpperTriangular ↔ ∀ i j, j < i → A i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

/-- **DLMF §1.3(i)**: `A` is lower triangular if `aᵢⱼ = 0` for `i < j`
(Mathlib's `Matrix.IsLowerTriangular`). -/
theorem dlmf_1_3_i_isLowerTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.IsLowerTriangular ↔ ∀ i j, i < j → A i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

/-- **DLMF §1.3(i)**: the determinant of an upper triangular matrix is the product of the
diagonal elements (`Matrix.det_of_isUpperTriangular`). -/
theorem dlmf_1_3_i_det_upperTriangular {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (h : A.IsUpperTriangular) : A.det = ∏ i, A i i :=
  det_of_isUpperTriangular h

/-- **DLMF §1.3(i)**: the determinant of a lower triangular matrix is the product of the
diagonal elements (`Matrix.det_of_isLowerTriangular`). -/
theorem dlmf_1_3_i_det_lowerTriangular {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (h : A.IsLowerTriangular) : A.det = ∏ i, A i i :=
  det_of_isLowerTriangular A h

/-- **DLMF §1.3(i)**: the determinant of a diagonal matrix is the product of the diagonal
elements (`Matrix.det_diagonal`). -/
theorem dlmf_1_3_i_det_diagonal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : A.IsDiag) :
    A.det = ∏ i, A i i := by
  rw [← h.diagonal_diag, det_diagonal]
  exact prod_congr rfl fun i _ => (diagonal_apply_eq _ i).symm

end Azurite.DLMF
