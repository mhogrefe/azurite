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
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

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
* 1.3.8–1.3.10 Hadamard's inequality `dlmf_1_3_8` (`n = 2`, Lagrange's identity), `dlmf_1_3_9`
  (`det A² ≤ ∏ⱼ ∑ₖ aⱼₖ²` for real entries, by Gram–Schmidt: `rowE`, `exists_det_eq_prod_inner`,
  `inner_sq_le_sum_sq`), `dlmf_1_3_10` (equality iff the rows are orthogonal or one vanishes).

## §1.3(ii) Special determinants

* 1.3.11–1.3.12 `dlmf_1_3_11`, `dlmf_1_3_12`: the alternants `det [fₖ(xⱼ)]`, `det [f(xⱼ, yₖ)]`.
* 1.3.13 `dlmf_1_3_13`: the Vandermonde determinant (`Matrix.det_vandermonde`).
* 1.3.14 `dlmf_1_3_14`: the Cauchy determinant `det [1/(aⱼ − bₖ)]`, proven by row and column
  operations (`cauchyMatrix`, `det_cauchyMatrix_succ`, `det_cauchyMatrix_mul`).
* 1.3.15 `dlmf_1_3_15`: the circulant, `∏ₖ (a₁ + a₂ ωₖ + ⋯ + aₙ ωₖ^(n−1))` over the `n`-th
  roots of unity (`circ`, `circ_mul_eq`: the columns `(ωₖ^i)` are eigenvectors,
  `det_circ_of_isPrimitiveRoot`).
* 1.3.16–1.3.17 `krat` (`dlmf_1_3_16`), `dlmf_1_3_17`: Krattenthaler's formula, by induction on
  `n` through the polynomial in `xₙ` (`kratOnes`, `det_kratOnes`, `kratPoly`, `det_krat_succ`,
  `det_krat`).

## §1.3(iii) Infinite determinants

* 1.3.18 `infDet` (`dlmf_1_3_18`): the `(2n + 1) × (2n + 1)` determinants `Dₙ[a]`;
  `InfDetConverges`: `D_∞[a] = L` when `Dₙ[a] → L`.
* 1.3.19 `IsHillType` (`dlmf_1_3_19`): `∑_{j,k} |a_{j,k} − δ_{j,k}| < ∞`;
  `dlmf_1_3_iii_hill_converges`: Hill-type determinants always converge (von Koch), by the
  principal-minor expansion `det (1 + B) = ∑_S det B_S` (`det_one_add_eq_sum_compl`), the bound
  `|det M| ≤ ∏ⱼ ∑ᵢ |Mᵢⱼ|` (`norm_det_le_prod_sum`) and the summability of `∏_{j ∈ S} rⱼ` over
  the finite subsets of `ℤ` (`summable_prod_finset`).
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

/-! #### Hadamard's inequality

For real entries, `det A² ≤ ∏ⱼ ∑ₖ aⱼₖ²`.  Proof: Gram–Schmidt on the rows `aᵢ` gives an orthonormal
basis `e` with `det A = ± ∏ ⟪eᵢ, aᵢ⟫` (`InnerProductSpace.gramSchmidtOrthonormalBasis_det`), and
`|⟪eᵢ, aᵢ⟫| ≤ ‖aᵢ‖` by Cauchy–Schwarz. -/

open InnerProductSpace

/-- The rows of a real matrix as vectors of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def rowE {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (A i)

theorem norm_rowE_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ‖rowE A i‖ ^ 2 = ∑ k, A i k ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [rowE]

theorem inner_rowE {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    inner ℝ (rowE A i) (rowE A j) = ∑ k, A i k * A j k := by
  rw [PiLp.inner_apply]
  simp [rowE, mul_comm]

/-- `det A` is the determinant of the rows of `A` with respect to the standard orthonormal
basis of `EuclideanSpace ℝ (Fin n)`. -/
theorem det_eq_basisFun_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det (rowE A) = A.det := by
  rw [Module.Basis.det_apply, ← det_transpose]
  congr 1

/-- Gram–Schmidt form of the determinant: `det A = ± ∏ᵢ ⟪eᵢ, aᵢ⟫` for the orthonormal basis `e`
obtained from the rows `aᵢ`, with `⟪eⱼ, aᵢ⟫ = 0` for `i < j`
(`InnerProductSpace.gramSchmidtOrthonormalBasis_det`). -/
theorem exists_det_eq_prod_inner {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (A.det = ∏ i, inner ℝ (e i) (rowE A i) ∨ A.det = -∏ i, inner ℝ (e i) (rowE A i)) ∧
        ∀ i j, i < j → inner ℝ (e j) (rowE A i) = 0 := by
  have h : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  refine ⟨gramSchmidtOrthonormalBasis h (rowE A), ?_,
    fun i j hij => gramSchmidtOrthonormalBasis_inv_triangular h (rowE A) hij⟩
  have key : (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det (rowE A) =
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det
          (gramSchmidtOrthonormalBasis h (rowE A)).toBasis *
        (gramSchmidtOrthonormalBasis h (rowE A)).toBasis.det (rowE A) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  rw [← gramSchmidtOrthonormalBasis_det h (rowE A), ← det_eq_basisFun_det, key,
    OrthonormalBasis.coe_toBasis]
  rcases OrthonormalBasis.det_to_matrix_orthonormalBasis_real (EuclideanSpace.basisFun (Fin n) ℝ)
    (gramSchmidtOrthonormalBasis h (rowE A)) with h1 | h1
  · left; rw [h1, one_mul]
  · right; rw [h1, neg_one_mul]

/-- Each Gram–Schmidt factor is bounded by the row norm: `⟪eᵢ, aᵢ⟫ ^ 2 ≤ ∑ₖ aᵢₖ ^ 2`
(Cauchy–Schwarz, `abs_real_inner_le_norm`). -/
theorem inner_sq_le_sum_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    inner ℝ (e i) (rowE A i) ^ 2 ≤ ∑ k, A i k ^ 2 := by
  rw [← norm_rowE_sq, ← sq_abs]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  calc |inner ℝ (e i) (rowE A i)| ≤ ‖e i‖ * ‖rowE A i‖ := abs_real_inner_le_norm _ _
    _ = ‖rowE A i‖ := by rw [e.orthonormal.1 i, one_mul]

theorem det_sq_eq_prod_inner_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))}
    (hdet : A.det = ∏ i, inner ℝ (e i) (rowE A i) ∨ A.det = -∏ i, inner ℝ (e i) (rowE A i)) :
    A.det ^ 2 = ∏ i, inner ℝ (e i) (rowE A i) ^ 2 := by
  rw [prod_pow]
  rcases hdet with h | h <;> rw [h]
  rw [neg_sq]

/-- **DLMF 1.3.8**, Hadamard's inequality for `n = 2`: for real entries,
`(a₁₁ a₂₂ − a₁₂ a₂₁)² ≤ (a₁₁² + a₁₂²)(a₂₁² + a₂₂²)` (Lagrange's identity). -/
theorem dlmf_1_3_8 (a b c d : ℝ) :
    !![a, b; c, d].det ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  rw [det_fin_two_of]
  nlinarith [sq_nonneg (a * c + b * d)]

/-- **DLMF 1.3.9**, Hadamard's inequality: for real entries,
`det [aⱼₖ]² ≤ ∏ⱼ ∑ₖ aⱼₖ²` (Gram–Schmidt: `det A = ± ∏ ⟪eᵢ, aᵢ⟫` and Cauchy–Schwarz). -/
theorem dlmf_1_3_9 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det ^ 2 ≤ ∏ j, ∑ k, A j k ^ 2 := by
  obtain ⟨e, hdet, -⟩ := exists_det_eq_prod_inner A
  rw [det_sq_eq_prod_inner_sq A hdet]
  exact prod_le_prod₀ (fun i _ => sq_nonneg _) fun i _ => inner_sq_le_sum_sq A e i

/-- **DLMF 1.3.10**, the equality case of Hadamard's inequality: equality holds iff
`∑ₗ aⱼₗ aₖₗ = 0` for every distinct pair `j, k` (the rows are orthogonal), or one of the factors
`∑ₖ aⱼₖ²` vanishes. -/
theorem dlmf_1_3_10 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det ^ 2 = ∏ j, ∑ k, A j k ^ 2 ↔
      (∀ j k, j ≠ k → ∑ l, A j l * A k l = 0) ∨ ∃ j, ∑ k, A j k ^ 2 = 0 := by
  constructor
  · intro heq
    by_cases hz : ∃ j, ∑ k, A j k ^ 2 = 0
    · exact Or.inr hz
    left
    push Not at hz
    have hpos : ∀ j, 0 < ∑ k, A j k ^ 2 := fun j =>
      lt_of_le_of_ne (sum_nonneg fun k _ => sq_nonneg _) (hz j).symm
    obtain ⟨e, hdet, -⟩ := exists_det_eq_prod_inner A
    have hsq := det_sq_eq_prod_inner_sq A hdet
    have hfac : ∀ i, inner ℝ (e i) (rowE A i) ^ 2 = ∑ k, A i k ^ 2 := by
      intro i
      by_contra hne
      have hlt : inner ℝ (e i) (rowE A i) ^ 2 < ∑ k, A i k ^ 2 :=
        lt_of_le_of_ne (inner_sq_le_sum_sq A e i) hne
      have : ∏ j, inner ℝ (e j) (rowE A j) ^ 2 < ∏ j, ∑ k, A j k ^ 2 := by
        rw [← mul_prod_erase univ _ (mem_univ i),
          ← mul_prod_erase univ (fun j => ∑ k, A j k ^ 2) (mem_univ i)]
        calc inner ℝ (e i) (rowE A i) ^ 2 * ∏ j ∈ univ.erase i, inner ℝ (e j) (rowE A j) ^ 2
            ≤ inner ℝ (e i) (rowE A i) ^ 2 * ∏ j ∈ univ.erase i, ∑ k, A j k ^ 2 :=
              mul_le_mul_of_nonneg_left
                (prod_le_prod₀ (fun j _ => sq_nonneg _) fun j _ => inner_sq_le_sum_sq A e j)
                (sq_nonneg _)
          _ < (∑ k, A i k ^ 2) * ∏ j ∈ univ.erase i, ∑ k, A j k ^ 2 :=
              mul_lt_mul_of_pos_right hlt (prod_pos fun j _ => hpos j)
      rw [← hsq, heq] at this
      exact lt_irrefl _ this
    have hrow : ∀ i, ∃ r : ℝ, rowE A i = r • e i := by
      intro i
      have h1 : ‖inner ℝ (e i) (rowE A i)‖ = ‖e i‖ * ‖rowE A i‖ := by
        rw [Real.norm_eq_abs, e.orthonormal.1 i, one_mul]
        have := hfac i
        rw [← norm_rowE_sq, ← sq_abs] at this
        exact (sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).mp this
      have hei : e i ≠ 0 := e.orthonormal.ne_zero i
      have hai : rowE A i ≠ 0 := by
        intro h0
        apply hz i
        rw [← norm_rowE_sq, h0, norm_zero, zero_pow two_ne_zero]
      obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hei hai).mp h1
      exact ⟨r, hr⟩
    intro j k hjk
    obtain ⟨r, hr⟩ := hrow j
    obtain ⟨s, hs⟩ := hrow k
    rw [← inner_rowE, hr, hs, inner_smul_left, inner_smul_right, e.orthonormal.2 hjk]
    simp
  · rintro (horth | ⟨j, hj⟩)
    · have hAA : A * Aᵀ = diagonal fun j => ∑ k, A j k ^ 2 := by
        ext j k
        rw [mul_apply, diagonal_apply]
        by_cases hjk : j = k
        · subst hjk
          simp [sq]
        · simp [hjk, horth j k hjk]
      calc A.det ^ 2 = (A * Aᵀ).det := by rw [det_mul, det_transpose, sq]
        _ = ∏ j, ∑ k, A j k ^ 2 := by rw [hAA, det_diagonal]
    · have hrow0 : ∀ k, A j k = 0 := fun k =>
        pow_eq_zero_iff two_ne_zero |>.mp
          ((sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (A j k)).mp hj k (mem_univ k))
      rw [det_eq_zero_of_row_eq_zero j hrow0, prod_eq_zero (mem_univ j) hj, zero_pow two_ne_zero]

/-! ### §1.3(ii) Special determinants

An alternant is a determinant function of `n` variables which changes sign when two of the
variables are interchanged (1.3.11–1.3.12); the Vandermonde (1.3.13) and Cauchy (1.3.14)
determinants are the classical examples. -/

/-- **DLMF 1.3.11**: `det [fₖ(xⱼ)]` is an alternant: interchanging two of the variables
`xᵢ, xᵢ'` changes its sign (an interchange of two rows). -/
theorem dlmf_1_3_11 {n : ℕ} (f : Fin n → ℂ → ℂ) (x : Fin n → ℂ) {i i' : Fin n} (h : i ≠ i') :
    (Matrix.of fun j k => f k (x (Equiv.swap i i' j))).det =
      -(Matrix.of fun j k => f k (x j)).det := by
  have := dlmf_1_3_i_swap_rows (Matrix.of fun j k => f k (x j)) h
  rw [← this]
  rfl

/-- **DLMF 1.3.12**: `det [f(xⱼ, yₖ)]` is an alternant in the `xⱼ` (rows) and in the `yₖ`
(columns). -/
theorem dlmf_1_3_12 {n : ℕ} (f : ℂ → ℂ → ℂ) (x y : Fin n → ℂ) {i i' : Fin n} (h : i ≠ i') :
    (Matrix.of fun j k => f (x (Equiv.swap i i' j)) (y k)).det =
        -(Matrix.of fun j k => f (x j) (y k)).det ∧
      (Matrix.of fun j k => f (x j) (y (Equiv.swap i i' k))).det =
        -(Matrix.of fun j k => f (x j) (y k)).det := by
  constructor
  · rw [← dlmf_1_3_i_swap_rows (Matrix.of fun j k => f (x j) (y k)) h]
    rfl
  · rw [← dlmf_1_3_i_swap_cols (Matrix.of fun j k => f (x j) (y k)) h]
    rfl

/-- **DLMF 1.3.13**, the Vandermonde determinant `det [xⱼ^(k−1)] = ∏_{j<k} (xₖ − xⱼ)`
(`Matrix.det_vandermonde`). -/
theorem dlmf_1_3_13 {n : ℕ} (x : Fin n → ℂ) :
    (Matrix.of fun j k : Fin n => x j ^ (k : ℕ)).det = ∏ j, ∏ k ∈ Ioi j, (x k - x j) :=
  det_vandermonde x

/-- The Cauchy matrix `[1/(aⱼ − bₖ)]`. -/
noncomputable def cauchyMatrix {n : ℕ} (a b : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => (a j - b k)⁻¹

/-- Column version of `Matrix.det_eq_of_forall_row_eq_smul_add_const`. -/
theorem det_eq_of_forall_col_eq_smul_add_const {m : Type*} [DecidableEq m] [Fintype m]
    {A B : Matrix m m ℂ} (c : m → ℂ) (k : m) (hk : c k = 0)
    (A_eq : ∀ i j, A i j = B i j + c j * B i k) : A.det = B.det := by
  rw [← det_transpose A, ← det_transpose B]
  exact det_eq_of_forall_row_eq_smul_add_const c k hk fun i j => A_eq j i

/-- Peeling off the first row and column of a Cauchy determinant by row and column operations:
subtract the first column from the others, factor the row and column multipliers, subtract the
first row from the others, factor again, and expand along the first column. -/
theorem det_cauchyMatrix_succ {n : ℕ} (a b : Fin (n + 1) → ℂ) (hab : ∀ j k, a j ≠ b k) :
    (cauchyMatrix a b).det =
      (∏ i, (a i - b 0)⁻¹) * (∏ j : Fin n, (b j.succ - b 0)) * (∏ i : Fin n, (a 0 - a i.succ)) *
        (∏ j : Fin n, (a 0 - b j.succ)⁻¹) *
        (cauchyMatrix (fun i => a i.succ) (fun j => b j.succ)).det := by
  have hab' : ∀ j k, a j - b k ≠ 0 := fun j k => sub_ne_zero.mpr (hab j k)
  -- Step A: subtract the first column from every other column.
  set N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun i j =>
    Fin.cases ((a i - b 0)⁻¹)
      (fun j' => (b j'.succ - b 0) * ((a i - b 0)⁻¹ * (a i - b j'.succ)⁻¹)) j with hN
  have hA : (cauchyMatrix a b).det = N.det := by
    refine det_eq_of_forall_col_eq_smul_add_const (Fin.cons 0 fun _ => 1) 0 (Fin.cons_zero _ _)
      fun i j => ?_
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp [cauchyMatrix, hN]
    · simp only [cauchyMatrix, hN, Matrix.of_apply, Fin.cases_succ, Fin.cons_succ, Fin.cases_zero,
        one_mul]
      have h1 := hab' i 0
      have h2 := hab' i j'.succ
      field_simp
      ring
  -- Step B: factor the row multipliers `(aᵢ − b₀)⁻¹` and the column multipliers `bⱼ − b₀`.
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun i j =>
    Fin.cases 1 (fun j' => (a i - b j'.succ)⁻¹) j with hM
  have hB : N = diagonal (fun i => (a i - b 0)⁻¹) * M *
      diagonal (Fin.cons 1 fun j' => b j'.succ - b 0) := by
    ext i j
    rw [mul_diagonal, diagonal_mul]
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp [hN, hM]
    · simp only [hN, hM, Matrix.of_apply, Fin.cases_succ, Fin.cons_succ]
      ring
  -- Step C: subtract the first row from every other row.
  set M' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun i j =>
    Fin.cases (M 0 j)
      (fun i' => Fin.cases 0
        (fun j' => (a 0 - a i'.succ) * ((a i'.succ - b j'.succ)⁻¹ * (a 0 - b j'.succ)⁻¹)) j) i
      with hM'
  have hC : M.det = M'.det := by
    refine det_eq_of_forall_row_eq_smul_add_const (Fin.cons 0 fun _ => 1) 0 (Fin.cons_zero _ _)
      fun i j => ?_
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [hM']
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [hM, hM']
      · simp only [hM, hM', Matrix.of_apply, Fin.cases_succ, Fin.cons_succ, Fin.cases_zero,
          one_mul]
        have h1 := hab' i'.succ j'.succ
        have h2 := hab' 0 j'.succ
        field_simp
        ring
  -- Step D: factor the row multipliers `a₀ − aᵢ` and the column multipliers `(a₀ − bⱼ)⁻¹`.
  set Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun i j =>
    Fin.cases 1 (fun i' => Fin.cases 0 (fun j' => (a i'.succ - b j'.succ)⁻¹) j) i with hQ
  have hD : M' = diagonal (Fin.cons 1 fun i' => a 0 - a i'.succ) * Q *
      diagonal (Fin.cons 1 fun j' => (a 0 - b j'.succ)⁻¹) := by
    ext i j
    rw [mul_diagonal, diagonal_mul]
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [hM', hM, hQ]
      · simp [hM', hM, hQ]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [hM', hQ]
      · simp only [hM', hQ, Matrix.of_apply, Fin.cases_succ, Fin.cons_succ]
        ring
  -- Step E: expand along the first column.
  have hE : Q.det = (cauchyMatrix (fun i => a i.succ) (fun j => b j.succ)).det := by
    rw [det_succ_column_zero, Finset.sum_eq_single 0]
    · simp only [hQ, Fin.val_zero, pow_zero, Matrix.of_apply, Fin.cases_zero, one_mul,
        Fin.succAbove_zero]
      congr 1
    · intro i _ hi
      obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
      simp [hQ]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hA, hB, det_mul, det_mul, det_diagonal, det_diagonal, hC, hD, det_mul, det_mul,
    det_diagonal, det_diagonal, hE, Fin.prod_univ_succ (Fin.cons 1 fun j' => b j'.succ - b 0),
    Fin.prod_univ_succ (Fin.cons 1 fun i' => a 0 - a i'.succ),
    Fin.prod_univ_succ (Fin.cons 1 fun j' => (a 0 - b j'.succ)⁻¹)]
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul]
  ring

/-- The Cauchy determinant times its denominator, by induction on `n`
(`det_cauchyMatrix_succ`). -/
theorem det_cauchyMatrix_mul {n : ℕ} (a b : Fin n → ℂ) (hab : ∀ j k, a j ≠ b k) :
    (cauchyMatrix a b).det * ∏ j, ∏ k, (a j - b k) =
      (-1) ^ (n * (n - 1) / 2) * ∏ j, ∏ k ∈ Ioi j, (a k - a j) * (b k - b j) := by
  induction n with
  | zero => simp [cauchyMatrix]
  | succ n ih =>
    have hab' : ∀ j k, a j - b k ≠ 0 := fun j k => sub_ne_zero.mpr (hab j k)
    have key := ih (fun i => a i.succ) (fun j => b j.succ) fun j k => hab _ _
    have hD : ∏ j, ∏ k, (a j - b k) = (a 0 - b 0) * (∏ k : Fin n, (a 0 - b k.succ)) *
        (∏ j : Fin n, (a j.succ - b 0)) * ∏ j : Fin n, ∏ k : Fin n, (a j.succ - b k.succ) := by
      simp only [Fin.prod_univ_succ, prod_mul_distrib]
      ring
    have hS : ∏ j, ∏ k ∈ Ioi j, (a k - a j) * (b k - b j) =
        (∏ k : Fin n, (a k.succ - a 0) * (b k.succ - b 0)) *
          ∏ j : Fin n, ∏ k ∈ Ioi j, (a k.succ - a j.succ) * (b k.succ - b j.succ) := by
      rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
      congr 1
      exact prod_congr rfl fun j _ => Fin.prod_Ioi_succ _ j
    have hsign : (-1 : ℂ) ^ ((n + 1) * (n + 1 - 1) / 2) = (-1) ^ (n * (n - 1) / 2) * (-1) ^ n := by
      rw [Nat.triangle_succ, pow_add]
    have hneg : ∏ i : Fin n, (a 0 - a i.succ) = (-1) ^ n * ∏ i : Fin n, (a i.succ - a 0) := by
      rw [show ∏ i : Fin n, (a 0 - a i.succ) = ∏ i : Fin n, -(a i.succ - a 0) from
        prod_congr rfl fun i _ => (neg_sub _ _).symm, Finset.prod_neg, card_univ, Fintype.card_fin]
    have h1 : a 0 - b 0 ≠ 0 := hab' 0 0
    have h2 : ∏ i : Fin n, (a i.succ - b 0) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hab' _ _
    have h3 : ∏ j : Fin n, (a 0 - b j.succ) ≠ 0 := prod_ne_zero_iff.mpr fun j _ => hab' _ _
    rw [det_cauchyMatrix_succ a b hab]
    calc _ = (∏ j : Fin n, (b j.succ - b 0)) * ((-1) ^ n * ∏ i : Fin n, (a i.succ - a 0)) *
          ((cauchyMatrix (fun i => a i.succ) (fun j => b j.succ)).det *
            ∏ j : Fin n, ∏ k : Fin n, (a j.succ - b k.succ)) := by
          rw [hD, hneg, Fin.prod_univ_succ (fun i => (a i - b 0)⁻¹), prod_inv_distrib,
            prod_inv_distrib]
          field_simp
      _ = _ := by
          rw [key, hS, hsign, prod_mul_distrib]
          ring

/-- **DLMF 1.3.14**, the Cauchy determinant: for `aⱼ ≠ bₖ`,
`det [1 / (aⱼ − bₖ)] = (−1)^(n(n−1)/2) ∏_{j<k} (aₖ − aⱼ)(bₖ − bⱼ) / ∏_{j,k} (aⱼ − bₖ)`
(proven by row and column operations, `det_cauchyMatrix_mul`). -/
theorem dlmf_1_3_14 {n : ℕ} (a b : Fin n → ℂ) (hab : ∀ j k, a j ≠ b k) :
    (Matrix.of fun j k => 1 / (a j - b k)).det =
      (-1) ^ (n * (n - 1) / 2) * (∏ j, ∏ k ∈ Ioi j, (a k - a j) * (b k - b j)) /
        ∏ j, ∏ k, (a j - b k) := by
  rw [eq_div_iff (prod_ne_zero_iff.mpr fun j _ =>
    prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hab j k))]
  simp_rw [one_div]
  exact det_cauchyMatrix_mul a b hab

/-! #### Circulant -/

/-- The DLMF circulant with first row `(a₀, …, aₙ₋₁)`: row `j` is the cyclic shift by `j`, so
the entry `(j, k)` is `a (k − j)` (indices mod `n`; the transpose of Mathlib's
`Matrix.circulant`). -/
def circ {n : ℕ} [NeZero n] (a : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => a (k - j)

theorem pow_val_add {n : ℕ} [NeZero n] {ω : ℂ} (hω : ω ^ n = 1) (i j : Fin n) :
    ω ^ ((i + j : Fin n) : ℕ) = ω ^ (i : ℕ) * ω ^ (j : ℕ) := by
  rw [Fin.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div ((i : ℕ) + j) n, pow_add, pow_mul, hω, one_pow, mul_one]

/-- `C F = F diag(λ)`: the columns `(ωₖ^i)ᵢ` of `F` are eigenvectors of the circulant for the
eigenvalues `λₖ = ∑ₘ aₘ ωₖ^m`, whenever `ωₖⁿ = 1`. -/
theorem circ_mul_eq {n : ℕ} [NeZero n] (a : Fin n → ℂ) (ω : Fin n → ℂ) (hω : ∀ k, ω k ^ n = 1) :
    circ a * (Matrix.of fun i k : Fin n => ω k ^ (i : ℕ)) =
      (Matrix.of fun i k : Fin n => ω k ^ (i : ℕ)) *
        diagonal fun k => ∑ m, a m * ω k ^ (m : ℕ) := by
  ext i k
  rw [mul_diagonal, Matrix.mul_apply, Matrix.of_apply, mul_sum]
  simp only [circ, Matrix.of_apply]
  refine Fintype.sum_equiv (Equiv.subRight i) _ _ fun j => ?_
  simp only [Equiv.subRight_apply]
  have : ω k ^ (j : ℕ) = ω k ^ (i : ℕ) * ω k ^ ((j - i : Fin n) : ℕ) := by
    rw [← pow_val_add (hω k), add_sub_cancel]
  rw [this]
  ring

/-- The circulant determinant for any primitive `n`-th root of unity `ζ`, with
`ωₖ = ζ^k`: the Vandermonde matrix of the `ωₖ` is invertible. -/
theorem det_circ_of_isPrimitiveRoot {n : ℕ} [NeZero n] (a : Fin n → ℂ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) :
    (circ a).det = ∏ k : Fin n, ∑ m : Fin n, a m * (ζ ^ (k : ℕ)) ^ (m : ℕ) := by
  set ω : Fin n → ℂ := fun k => ζ ^ (k : ℕ) with hωdef
  have hω : ∀ k, ω k ^ n = 1 := fun k => by
    rw [hωdef]
    simp only
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hF : (Matrix.of fun i k : Fin n => ω k ^ (i : ℕ)).det ≠ 0 := by
    have : (Matrix.of fun i k : Fin n => ω k ^ (i : ℕ)) = (vandermonde ω)ᵀ := by
      ext i k
      rfl
    rw [this, det_transpose]
    exact det_vandermonde_ne_zero_iff.mpr fun i j h => Fin.ext (hζ.pow_inj i.isLt j.isLt h)
  have := congrArg Matrix.det (circ_mul_eq a ω hω)
  rw [det_mul, det_mul, det_diagonal] at this
  exact mul_right_cancel₀ hF (this.trans (mul_comm _ _))

/-- **DLMF 1.3.15**, the circulant: with first row `(a₁, …, aₙ)` and each further row the
cyclic shift of the previous one, the determinant is `∏ₖ (a₁ + a₂ ωₖ + ⋯ + aₙ ωₖ^(n−1))` over the
`n`-th roots of unity `ωₖ = exp(2πik/n)` (`det_circ_of_isPrimitiveRoot`). -/
theorem dlmf_1_3_15 {n : ℕ} [NeZero n] (a : Fin n → ℂ) :
    (Matrix.of fun j k : Fin n => a (k - j)).det =
      ∏ k : Fin n, ∑ m : Fin n,
        a m * Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / n) ^ (m : ℕ) := by
  rw [show (Matrix.of fun j k : Fin n => a (k - j)) = circ a from rfl,
    det_circ_of_isPrimitiveRoot a (Complex.isPrimitiveRoot_exp n (NeZero.ne n))]
  refine prod_congr rfl fun k _ => sum_congr rfl fun m _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 3
  ring

/-! #### Krattenthaler's formula -/

section Krattenthaler

open Polynomial

/-- Krattenthaler's matrix `t j k = ∏_{m > k} (x j + a m) · ∏_{m < k} (x j + b m)` (DLMF 1.3.16
with the indices shifted to start at `0`: `a m` is DLMF's `a_{m+1}` and `b m` is DLMF's
`b_{m+2}`, so `a 0` and `b (n−1)` do not occur). -/
def krat {R : Type*} [CommRing R] {n : ℕ} (x a b : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun j k => (∏ m ∈ Ioi k, (x j + a m)) * ∏ m ∈ Iio k, (x j + b m)

theorem krat_apply {R : Type*} [CommRing R] {n : ℕ} (x a b : Fin n → R) (j k : Fin n) :
    krat x a b j k = (∏ m ∈ Ioi k, (x j + a m)) * ∏ m ∈ Iio k, (x j + b m) :=
  rfl

/-- `∏_{m > castSucc k} f m = f (succ k) · ∏_{m > succ k} f m`. -/
theorem prod_Ioi_castSucc_eq {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin (n + 1) → M)
    (k : Fin n) : ∏ m ∈ Ioi k.castSucc, f m = f k.succ * ∏ m ∈ Ioi k.succ, f m := by
  rw [← Finset.mul_prod_erase (Ioi k.castSucc) f (show k.succ ∈ Ioi k.castSucc by simp)]
  congr 2
  ext m
  simp only [mem_erase, mem_Ioi, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Ne, Fin.ext_iff]
  omega

/-- `∏_{m < succ k} f m = (∏_{m < castSucc k} f m) · f (castSucc k)`. -/
theorem prod_Iio_succ_eq {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin (n + 1) → M) (k : Fin n) :
    ∏ m ∈ Iio k.succ, f m = (∏ m ∈ Iio k.castSucc, f m) * f k.castSucc := by
  rw [mul_comm, ← Finset.mul_prod_erase (Iio k.succ) f (show k.castSucc ∈ Iio k.succ by simp)]
  congr 2
  ext m
  simp only [mem_erase, mem_Iio, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Ne, Fin.ext_iff]
  omega

/-- `∏_{m > castSucc j} f m = (∏_{m' > j} f (castSucc m')) · f (last n)`. -/
theorem prod_Ioi_castSucc_eq' {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin (n + 1) → M)
    (j : Fin n) : ∏ m ∈ Ioi j.castSucc, f m = (∏ m ∈ Ioi j, f m.castSucc) * f (Fin.last n) := by
  rw [mul_comm, ← Finset.mul_prod_erase (Ioi j.castSucc) f
    (show Fin.last n ∈ Ioi j.castSucc by simp [Fin.castSucc_lt_last])]
  congr 1
  rw [show (∏ m ∈ Ioi j, f m.castSucc) = ∏ m ∈ (Ioi j).map Fin.castSuccEmb, f m by
    rw [Finset.prod_map]; rfl, Fin.map_castSuccEmb_Ioi]
  congr 1
  ext m
  simp only [mem_erase, mem_Ioi, mem_Ioo, Fin.lt_def, Fin.val_castSucc, Fin.val_last, Ne,
    Fin.ext_iff]
  omega

/-- The matrix with the rows `krat x a b (castSucc i')` and a last row of ones: the coefficient
of `xₙⁿ` in the Krattenthaler determinant of order `n + 1`. -/
def kratOnes {R : Type*} [CommRing R] {n : ℕ} (x a b : Fin (n + 1) → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.snoc (fun i' => krat x a b i'.castSucc) fun _ => 1)

/-- Column operations on `kratOnes`: subtracting each column from the next one, factoring
`b_k − a_{k+1}` from column `k + 1`, and expanding along the last row `(1, 0, …, 0)` leaves the
Krattenthaler determinant of order `n` in the parameters `x ∘ castSucc`, `a ∘ succ`,
`b ∘ castSucc`. -/
theorem det_kratOnes {R : Type*} [CommRing R] {n : ℕ} (x a b : Fin (n + 1) → R) :
    (kratOnes x a b).det = (-1) ^ n * (∏ k : Fin n, (b k.castSucc - a k.succ)) *
      (krat (x ∘ Fin.castSucc) (a ∘ Fin.succ) (b ∘ Fin.castSucc)).det := by
  set Q : Fin (n + 1) → Fin n → R := fun i k' =>
    (∏ m ∈ Ioi k'.succ, (x i + a m)) * ∏ m ∈ Iio k'.castSucc, (x i + b m) with hQ
  set B' : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of
    (Fin.snoc (fun i' => Fin.cons (krat x a b i'.castSucc 0) (Q i'.castSucc))
      (Fin.cons 1 fun _ => 0)) with hB'
  set d : Fin (n + 1) → R := Fin.cons 1 fun k' => b k'.castSucc - a k'.succ with hd
  have hcol : (kratOnes x a b).det = (B' * diagonal d).det := by
    refine det_eq_of_forall_col_eq_smul_add_pred (fun _ => 1) ?_ ?_
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [kratOnes, hB', hd]
      · simp [kratOnes, hB', hd]
    · intro i k'
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [kratOnes, hB', hd]
      · simp only [kratOnes, hB', hd, hQ, Matrix.of_apply, Fin.snoc_castSucc, mul_diagonal,
          Fin.cons_succ, one_mul, krat_apply]
        rw [prod_Ioi_castSucc_eq (fun m => x i'.castSucc + a m) k',
          prod_Iio_succ_eq (fun m => x i'.castSucc + b m) k']
        ring
  have hexp : B'.det =
      (-1) ^ n * (krat (x ∘ Fin.castSucc) (a ∘ Fin.succ) (b ∘ Fin.castSucc)).det := by
    rw [det_succ_row B' (Fin.last n), Finset.sum_eq_single 0]
    · simp only [hB', Matrix.of_apply, Fin.snoc_last, Fin.cons_zero, Fin.val_last, Fin.val_zero,
        add_zero, mul_one, Fin.succAbove_last, Fin.succAbove_zero]
      congr 2
      ext i' k'
      simp only [submatrix_apply, Matrix.of_apply, Fin.snoc_castSucc, Fin.cons_succ, hQ,
        krat_apply, Function.comp]
      rw [Fin.prod_Ioi_succ, Fin.prod_Iio_castSucc]
    · intro k _ hk
      obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.mpr hk
      simp [hB']
    · intro h
      exact absurd (mem_univ _) h
  rw [hcol, det_mul, det_diagonal, hexp, hd, Fin.prod_univ_succ, Fin.cons_zero, one_mul]
  simp only [Fin.cons_succ]
  ring

theorem eval_snoc_C_X {n : ℕ} (x : Fin n → ℂ) (y : ℂ) (i : Fin (n + 1)) :
    eval y ((Fin.snoc (fun i' => C (x i')) X : Fin (n + 1) → ℂ[X]) i) =
      (Fin.snoc x y : Fin (n + 1) → ℂ) i := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp
  · simp

/-- The Krattenthaler matrix over `ℂ[X]` whose last row has the variable `X` in place of `xₙ`. -/
noncomputable def kratPoly {n : ℕ} (x : Fin n → ℂ) (a b : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ[X] :=
  krat (Fin.snoc (fun i' => C (x i')) X) (fun m => C (a m)) (fun m => C (b m))

theorem eval_det_kratPoly {n : ℕ} (x : Fin n → ℂ) (a b : Fin (n + 1) → ℂ) (y : ℂ) :
    eval y (kratPoly x a b).det = (krat (Fin.snoc x y) a b).det := by
  rw [← coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i k
  simp only [Matrix.map_apply, kratPoly, krat_apply, coe_evalRingHom, eval_mul, eval_prod,
    eval_add, eval_C, eval_snoc_C_X]

theorem kratPoly_last_monic {n : ℕ} (x : Fin n → ℂ) (a b : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    (kratPoly x a b (Fin.last n) k).Monic ∧ (kratPoly x a b (Fin.last n) k).natDegree = n := by
  simp only [kratPoly, krat_apply, Fin.snoc_last]
  have h1 : ∀ m ∈ Ioi k, (X + C (a m)).Monic := fun m _ => monic_X_add_C _
  have h2 : ∀ m ∈ Iio k, (X + C (b m)).Monic := fun m _ => monic_X_add_C _
  refine ⟨(monic_prod_of_monic _ _ h1).mul (monic_prod_of_monic _ _ h2), ?_⟩
  rw [(monic_prod_of_monic _ _ h1).natDegree_mul (monic_prod_of_monic _ _ h2),
    natDegree_prod_of_monic _ _ h1, natDegree_prod_of_monic _ _ h2]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one, Fin.card_Ioi, Fin.card_Iio]
  omega

/-- The rows of `kratPoly` other than the last are constant: the cofactors of the last row are
the constants `d k`. -/
theorem det_kratPoly_expand {n : ℕ} (x : Fin n → ℂ) (a b : Fin (n + 1) → ℂ) :
    (kratPoly x a b).det = ∑ k : Fin (n + 1),
      (-1) ^ ((Fin.last n : ℕ) + k) * kratPoly x a b (Fin.last n) k *
      C ((krat (Fin.snoc x 0) a b).submatrix Fin.castSucc k.succAbove).det := by
  rw [det_succ_row _ (Fin.last n)]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i' k''
  simp only [submatrix_apply, Fin.succAbove_last, Matrix.map_apply, kratPoly, krat_apply,
    Fin.snoc_castSucc, map_mul, map_prod, map_add]

theorem det_kratOnes_expand {n : ℕ} (x : Fin n → ℂ) (a b : Fin (n + 1) → ℂ) :
    (kratOnes (Fin.snoc x 0) a b).det = ∑ k : Fin (n + 1), (-1) ^ ((Fin.last n : ℕ) + k) *
      ((krat (Fin.snoc x 0) a b).submatrix Fin.castSucc k.succAbove).det := by
  rw [det_succ_row _ (Fin.last n)]
  refine sum_congr rfl fun k _ => ?_
  simp only [kratOnes, Matrix.of_apply, Fin.snoc_last, mul_one, Fin.succAbove_last]
  congr 2
  ext i' k''
  simp [submatrix_apply, Fin.snoc_castSucc]

theorem det_kratPoly_natDegree_le {n : ℕ} (x : Fin n → ℂ) (a b : Fin (n + 1) → ℂ) :
    (kratPoly x a b).det.natDegree ≤ n := by
  rw [det_kratPoly_expand]
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_mul_C_le _ _).trans ?_
  rw [show ((-1 : ℂ[X]) ^ ((Fin.last n : ℕ) + k)) = C ((-1) ^ ((Fin.last n : ℕ) + k)) by simp]
  exact (natDegree_C_mul_le _ _).trans (kratPoly_last_monic x a b k).2.le

theorem det_kratPoly_coeff {n : ℕ} (x : Fin n → ℂ) (a b : Fin (n + 1) → ℂ) :
    (kratPoly x a b).det.coeff n = (kratOnes (Fin.snoc x 0) a b).det := by
  rw [det_kratPoly_expand, det_kratOnes_expand, finsetSum_coeff]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_mul_C, show ((-1 : ℂ[X]) ^ ((Fin.last n : ℕ) + k)) = C ((-1) ^ ((Fin.last n : ℕ) + k))
    by simp, coeff_C_mul]
  obtain ⟨hm, hd⟩ := kratPoly_last_monic x a b k
  have h1 := hm.coeff_natDegree
  rw [hd] at h1
  rw [h1, mul_one]

/-- The inductive step: for distinct `x₀, …, xₙ₋₁`, the Krattenthaler determinant of order `n + 1`
is a polynomial of degree `n` in `xₙ` vanishing at `x₀, …, xₙ₋₁`, with leading coefficient
`det (kratOnes x a b)`. -/
theorem det_krat_succ {n : ℕ} (x a b : Fin (n + 1) → ℂ)
    (hinj : Function.Injective (x ∘ Fin.castSucc)) :
    (krat x a b).det = (kratOnes x a b).det * ∏ j' : Fin n, (x (Fin.last n) - x j'.castSucc) := by
  set x' : Fin n → ℂ := x ∘ Fin.castSucc with hx'
  have hones : kratOnes (Fin.snoc x' 0) a b = kratOnes x a b := by
    ext i k
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp [kratOnes]
    · simp [kratOnes, krat_apply, Fin.snoc_castSucc, hx']
  set c := (kratOnes (Fin.snoc x' 0) a b).det with hc
  set P : ℂ[X] := (kratPoly x' a b).det - C c * ∏ j' : Fin n, (X - C (x' j')) with hP
  have hmon : (∏ j' : Fin n, (X - C (x' j'))).Monic :=
    monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hdeg' : (∏ j' : Fin n, (X - C (x' j'))).natDegree = n := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  have hdeg : P.natDegree ≤ n :=
    (natDegree_sub_le _ _).trans (max_le (det_kratPoly_natDegree_le x' a b)
      ((natDegree_C_mul_le _ _).trans hdeg'.le))
  have hcoeff : P.coeff n = 0 := by
    have h1 := hmon.coeff_natDegree
    rw [hdeg'] at h1
    rw [hP, coeff_sub, det_kratPoly_coeff, coeff_C_mul, h1, mul_one, hc, sub_self]
  have hP0 : P = 0 := by
    by_contra hne
    have hlt : P.natDegree < n := by
      refine lt_of_le_of_ne hdeg fun h => hne ?_
      rw [← h] at hcoeff
      exact leadingCoeff_eq_zero.mp hcoeff
    refine hne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj (fun j' => ?_)
      (by simpa using hlt))
    rw [hP, eval_sub, eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [prod_eq_zero (mem_univ j') (sub_self _), mul_zero, sub_zero, eval_det_kratPoly]
    refine det_zero_of_row_eq (Fin.castSucc_lt_last j').ne (funext fun k => ?_)
    simp [krat_apply, Fin.snoc_castSucc, Fin.snoc_last, hx']
  have := congrArg (eval (x (Fin.last n))) hP0
  rw [hP, eval_sub, eval_mul, eval_C, eval_prod, eval_zero, sub_eq_zero, eval_det_kratPoly]
    at this
  simp only [eval_sub, eval_X, eval_C] at this
  rw [hc, hones, show Fin.snoc x' (x (Fin.last n)) = x from Fin.snoc_init_self x] at this
  exact this

/-- Krattenthaler's determinant evaluation (DLMF 1.3.17, shifted indices):
`det (krat x a b) = ∏_{j<k} (xⱼ − xₖ) · ∏_k ∏_{j<k} (bⱼ − aₖ)`. -/
theorem det_krat {n : ℕ} (x a b : Fin n → ℂ) :
    (krat x a b).det = (∏ j, ∏ k ∈ Ioi j, (x j - x k)) * ∏ k, ∏ j ∈ Iio k, (b j - a k) := by
  induction n with
  | zero => simp [krat]
  | succ n ih =>
    by_cases hinj : Function.Injective (x ∘ Fin.castSucc)
    · rw [det_krat_succ x a b hinj, det_kratOnes, ih]
      rw [Fin.prod_univ_castSucc (fun j => ∏ k ∈ Ioi j, (x j - x k)),
        Fin.prod_univ_succ (fun k => ∏ j ∈ Iio k, (b j - a k)),
        prod_eq_one (s := Ioi (Fin.last n))
          (fun k hk => absurd (mem_Ioi.mp hk) (not_lt.mpr (Fin.le_last k))),
        prod_eq_one (s := Iio (0 : Fin (n + 1)))
          (fun j hj => absurd (mem_Iio.mp hj) (Fin.not_lt_zero j))]
      simp only [prod_Ioi_castSucc_eq', prod_Iio_succ_eq, Fin.prod_Iio_castSucc, prod_mul_distrib,
        Function.comp]
      have hsgn : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      have hW : ∏ j' : Fin n, (x (Fin.last n) - x j'.castSucc) =
          (-1) ^ n * ∏ j' : Fin n, (x j'.castSucc - x (Fin.last n)) := by
        rw [show ∏ j' : Fin n, (x (Fin.last n) - x j'.castSucc) =
          ∏ j' : Fin n, -(x j'.castSucc - x (Fin.last n)) from
            prod_congr rfl fun j _ => (neg_sub _ _).symm, prod_neg, card_univ, Fintype.card_fin]
      rw [hW]
      linear_combination ((∏ k : Fin n, (b k.castSucc - a k.succ)) *
        (∏ j : Fin n, ∏ k ∈ Ioi j, (x j.castSucc - x k.castSucc)) *
        (∏ k : Fin n, ∏ j ∈ Iio k, (b j.castSucc - a k.succ)) *
        ∏ j' : Fin n, (x j'.castSucc - x (Fin.last n))) * hsgn
    · obtain ⟨j, k, hjk, hne⟩ := Function.not_injective_iff.mp hinj
      simp only [Function.comp_apply] at hjk
      rw [det_zero_of_row_eq ((Fin.castSucc_injective n).ne hne)
        (funext fun m => by simp [krat_apply, hjk])]
      rcases lt_or_gt_of_ne hne with h | h
      · rw [prod_eq_zero (mem_univ j.castSucc) (prod_eq_zero
          (mem_Ioi.mpr (Fin.castSucc_lt_castSucc_iff.mpr h)) (sub_eq_zero.mpr hjk)), zero_mul]
      · rw [prod_eq_zero (mem_univ k.castSucc) (prod_eq_zero
          (mem_Ioi.mpr (Fin.castSucc_lt_castSucc_iff.mpr h)) (sub_eq_zero.mpr hjk.symm)), zero_mul]

/-- **DLMF 1.3.16**: Krattenthaler's entries
`tⱼₖ = (xⱼ + aₙ)(xⱼ + aₙ₋₁)⋯(xⱼ + aₖ₊₁) · (xⱼ + bₖ)(xⱼ + bₖ₋₁)⋯(xⱼ + b₂)`; with the indices shifted
to start at `0` (`a m` is DLMF's `a_{m+1}`, `b m` is DLMF's `b_{m+2}`) this is `krat x a b j k`. -/
theorem dlmf_1_3_16 {n : ℕ} (x a b : Fin n → ℂ) (j k : Fin n) :
    krat x a b j k = (∏ m ∈ Ioi k, (x j + a m)) * ∏ m ∈ Iio k, (x j + b m) :=
  rfl

/-- **DLMF 1.3.17**, Krattenthaler's formula:
`det [tⱼₖ] = ∏_{1≤j<k≤n} (xⱼ − xₖ) ∏_{2≤j≤k≤n} (bⱼ − aₖ)` (in the shifted indices, the second
product is over `j < k`).  Proven by induction on `n`: the determinant is a polynomial of degree
`n − 1` in `xₙ` vanishing at `x₁, …, xₙ₋₁`, whose leading coefficient is computed by column
operations (`det_kratOnes`, `det_krat_succ`, `det_krat`). -/
theorem dlmf_1_3_17 {n : ℕ} (x a b : Fin n → ℂ) :
    (krat x a b).det = (∏ j, ∏ k ∈ Ioi j, (x j - x k)) * ∏ k, ∏ j ∈ Iio k, (b j - a k) :=
  det_krat x a b

end Krattenthaler

/-! ### §1.3(iii) Infinite determinants -/

open Filter Topology

/-- **DLMF 1.3.18**: for `a : ℤ → ℤ → ℂ`, `Dₙ[a]` is the `(2n + 1) × (2n + 1)` determinant of the
entries `a_{j,k}`, `−n ≤ j, k ≤ n`. -/
noncomputable def infDet (a : ℤ → ℤ → ℂ) (n : ℕ) : ℂ :=
  (Matrix.of fun j k : Fin (2 * n + 1) => a ((j : ℕ) - n : ℤ) ((k : ℕ) - n : ℤ)).det

theorem dlmf_1_3_18 (a : ℤ → ℤ → ℂ) (n : ℕ) :
    infDet a n =
      (Matrix.of fun j k : Fin (2 * n + 1) => a ((j : ℕ) - n : ℤ) ((k : ℕ) - n : ℤ)).det :=
  rfl

/-- The infinite determinant `D_∞[a]` converges to `L` if `Dₙ[a] → L` as `n → ∞`. -/
def InfDetConverges (a : ℤ → ℤ → ℂ) (L : ℂ) : Prop :=
  Tendsto (infDet a) atTop (𝓝 L)

/-- **DLMF 1.3.19**: `a` is of Hill's type if the double series `∑_{j,k} |a_{j,k} − δ_{j,k}|`
converges. -/
def IsHillType (a : ℤ → ℤ → ℂ) : Prop :=
  Summable fun p : ℤ × ℤ => ‖a p.1 p.2 - if p.1 = p.2 then 1 else 0‖

theorem dlmf_1_3_19 (a : ℤ → ℤ → ℂ) :
    IsHillType a ↔ Summable fun p : ℤ × ℤ => ‖a p.1 p.2 - if p.1 = p.2 then 1 else 0‖ :=
  Iff.rfl

/-- A matrix whose rows indexed by `T` are unit rows has the determinant of its principal
submatrix on the complement of `T` (block triangularity). -/
theorem det_eq_det_submatrix_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (T : Finset ι) (hT : ∀ i ∈ T, ∀ j, M i j = if i = j then 1 else 0) :
    M.det = (M.submatrix (Subtype.val : {i // i ∉ T} → ι) Subtype.val).det := by
  let b : ι → Fin 2 := fun i => if i ∈ T then 1 else 0
  have hbt : M.BlockTriangular b := by
    intro i j hij
    simp only [b] at hij
    by_cases hi : i ∈ T
    · by_cases hj : j ∈ T
      · simp [hi, hj] at hij
      · rw [hT i hi j]
        exact ite_eq_right_iff.mpr fun h => absurd (h ▸ hi) hj
    · simp [hi] at hij
  rw [hbt.det_fintype, Fin.prod_univ_two]
  have h1 : (M.toSquareBlock b 1).det = 1 := by
    rw [← det_one (n := {a // b a = 1})]
    congr 1
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i ∈ T := by simpa [b] using hi
    rw [toSquareBlock_def, of_apply, hT i hi', one_apply]
    simp only [Subtype.mk.injEq]
  rw [h1, mul_one]
  let e : {a // b a = 0} ≃ {i // i ∉ T} :=
    Equiv.subtypeEquivRight fun i => by simp [b]
  rw [← det_submatrix_equiv_self e.symm]
  rfl

/-- The principal-minor expansion `det (1 + B) = ∑_T det B_{Tᶜ}` over all subsets `T` of the
index set (multilinearity in the rows, `MultilinearMap.map_add_univ`). -/
theorem det_one_add_eq_sum_compl {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) :
    (1 + B).det =
      ∑ T : Finset ι, (B.submatrix (Subtype.val : {i // i ∉ T} → ι) Subtype.val).det := by
  have h := MultilinearMap.map_add_univ
    (detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap (1 : Matrix ι ι ℂ) B
  change (1 + B).det = _ at h
  rw [h]
  refine sum_congr rfl fun T _ => ?_
  change (Matrix.of (T.piecewise (1 : Matrix ι ι ℂ) B)).det = _
  rw [det_eq_det_submatrix_compl (Matrix.of (T.piecewise (1 : Matrix ι ι ℂ) B)) T
    fun i hi j => by simp [Finset.piecewise, hi, one_apply]]
  congr 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp [Finset.piecewise, hi]

/-- `|det M| ≤ ∏ⱼ ∑ᵢ |Mᵢⱼ|` (the Leibniz sum over permutations is dominated by the sum over all
maps `ι → ι`, which factors as the product of the column sums). -/
theorem norm_det_le_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    ‖M.det‖ ≤ ∏ j, ∑ i, ‖M i j‖ := by
  rw [det_apply']
  calc ‖∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖
      ≤ ∑ σ : Equiv.Perm ι, ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖M (σ i) i‖ := by
        refine sum_congr rfl fun σ _ => ?_
        rw [norm_mul, norm_prod]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    _ ≤ ∑ f : ι → ι, ∏ i, ‖M (f i) i‖ := by
        rw [← sum_image (s := univ) (g := fun σ : Equiv.Perm ι => (⇑σ : ι → ι))
          (f := fun f : ι → ι => ∏ i, ‖M (f i) i‖) fun σ _ τ _ h => Equiv.coe_fn_injective h]
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun f _ _ => prod_nonneg fun i _ => norm_nonneg _
    _ = ∏ j, ∑ i, ‖M i j‖ := by
        rw [prod_univ_sum fun _ => (univ : Finset ι), Fintype.piFinset_univ]

/-- The principal minor of `b : ℤ → ℤ → ℂ` on the finite set `S`. -/
noncomputable def hillMinor (b : ℤ → ℤ → ℂ) (S : Finset ℤ) : ℂ :=
  (Matrix.of fun i j : S => b i j).det

/-- `|det b_S| ≤ ∏_{j ∈ S} rⱼ` with `rⱼ = ∑ᵢ |bᵢⱼ|`. -/
theorem norm_hillMinor_le (b : ℤ → ℤ → ℂ) (hb : ∀ j, Summable fun i => ‖b i j‖) (S : Finset ℤ) :
    ‖hillMinor b S‖ ≤ ∏ j ∈ S, ∑' i, ‖b i j‖ := by
  refine (norm_det_le_prod_sum _).trans ?_
  rw [← prod_coe_sort S]
  refine prod_le_prod₀ (fun j _ => sum_nonneg fun i _ => norm_nonneg _) fun j _ => ?_
  simp only [Matrix.of_apply]
  rw [sum_coe_sort S fun i => ‖b i j‖]
  exact (hb j).sum_le_tsum S fun i _ => norm_nonneg _

/-- `∑_S ∏_{j ∈ S} rⱼ` over all finite `S ⊆ ℤ` converges when `∑ rⱼ` does: the partial sums are
bounded by `∏ (1 + rⱼ) ≤ exp (∑ rⱼ)`. -/
theorem summable_prod_finset {r : ℤ → ℝ} (hr0 : ∀ j, 0 ≤ r j) (hr : Summable r) :
    Summable fun S : Finset ℤ => ∏ j ∈ S, r j := by
  refine summable_of_sum_le (c := Real.exp (∑' j, r j)) (fun S => prod_nonneg fun j _ => hr0 j)
    fun u => ?_
  set U : Finset ℤ := u.sup id with hU
  calc ∑ S ∈ u, ∏ j ∈ S, r j ≤ ∑ S ∈ U.powerset, ∏ j ∈ S, r j := by
        refine sum_le_sum_of_subset_of_nonneg (fun S hS => mem_powerset.mpr (le_sup (f := id) hS))
          fun S _ _ => prod_nonneg fun j _ => hr0 j
    _ = ∏ j ∈ U, (r j + 1) := by
        rw [prod_add]
        simp
    _ ≤ ∏ j ∈ U, Real.exp (r j) :=
        prod_le_prod₀ (fun j _ => by linarith [hr0 j]) fun j _ => Real.add_one_le_exp (r j)
    _ = Real.exp (∑ j ∈ U, r j) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' j, r j) := Real.exp_le_exp.mpr (hr.sum_le_tsum U fun j _ => hr0 j)

/-- The shift `j ↦ j − n` from `Fin (2n + 1)` onto `[−n, n]`. -/
def shiftZ (n : ℕ) (j : Fin (2 * n + 1)) : ℤ := ((j : ℕ) : ℤ) - n

theorem shiftZ_injective (n : ℕ) : Function.Injective (shiftZ n) := fun j k h => by
  simp only [shiftZ] at h
  exact Fin.ext (by omega)

theorem shiftZ_mem_Icc (n : ℕ) (j : Fin (2 * n + 1)) : shiftZ n j ∈ Icc (-(n : ℤ)) n := by
  simp only [mem_Icc, shiftZ]
  omega

theorem exists_shiftZ_eq (n : ℕ) {z : ℤ} (hz : z ∈ Icc (-(n : ℤ)) n) : ∃ j, shiftZ n j = z := by
  rw [mem_Icc] at hz
  refine ⟨⟨(z + n).toNat, by omega⟩, ?_⟩
  simp only [shiftZ]
  omega

/-- `Dₙ[a]` as the sum of the principal minors of `b = a − δ` over the subsets of `[−n, n]`. -/
theorem infDet_eq_sum_hillMinor (a : ℤ → ℤ → ℂ) (n : ℕ) :
    infDet a n = ∑ S ∈ (Icc (-(n : ℤ)) n).powerset,
      hillMinor (fun i j => a i j - if i = j then 1 else 0) S := by
  set b : ℤ → ℤ → ℂ := fun i j => a i j - if i = j then 1 else 0 with hb
  have h1 : (Matrix.of fun j k : Fin (2 * n + 1) => a ((j : ℕ) - n : ℤ) ((k : ℕ) - n : ℤ)) =
      1 + Matrix.of fun j k : Fin (2 * n + 1) => b (shiftZ n j) (shiftZ n k) := by
    ext j k
    simp only [Matrix.add_apply, Matrix.of_apply, one_apply, hb, shiftZ]
    by_cases hjk : j = k
    · subst hjk
      simp
    · have : ((j : ℕ) : ℤ) - n ≠ ((k : ℕ) : ℤ) - n := fun h => hjk (Fin.ext (by omega))
      simp [hjk, this]
  rw [infDet, h1, det_one_add_eq_sum_compl]
  refine sum_nbij' (fun T => Tᶜ.image (shiftZ n)) (fun S => (univ.filter fun j => shiftZ n j ∈ S)ᶜ)
    ?_ ?_ ?_ ?_ ?_
  · intro T _
    exact mem_powerset.mpr fun z hz => by
      obtain ⟨j, -, rfl⟩ := mem_image.mp hz
      exact shiftZ_mem_Icc n j
  · intro S _
    exact mem_univ _
  · intro T _
    ext j
    simp [shiftZ_injective n |>.eq_iff]
  · intro S hS
    rw [mem_powerset] at hS
    ext z
    simp only [compl_compl, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hz
      obtain ⟨j, rfl⟩ := exists_shiftZ_eq n (hS hz)
      exact ⟨j, hz, rfl⟩
  · intro T _
    simp only [hillMinor]
    let e : {i : Fin (2 * n + 1) // i ∉ T} ≃ {z // z ∈ Tᶜ.image (shiftZ n)} :=
      Equiv.ofBijective (fun i => ⟨shiftZ n i, mem_image_of_mem _ (mem_compl.mpr i.2)⟩)
        ⟨fun i i' h => Subtype.ext (shiftZ_injective n (Subtype.ext_iff.mp h)),
          fun z => by
            obtain ⟨j, hj, hjz⟩ := mem_image.mp z.2
            exact ⟨⟨j, mem_compl.mp hj⟩, Subtype.ext hjz⟩⟩
    rw [← det_submatrix_equiv_self e]
    rfl

/-- The powersets of `[−n, n]` exhaust the finite subsets of `ℤ`. -/
theorem tendsto_powerset_Icc :
    Tendsto (fun n : ℕ => (Icc (-(n : ℤ)) n).powerset) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun u => ⟨u.sup fun S => S.sup Int.natAbs, fun n hn => ?_⟩
  intro S hS
  rw [mem_powerset]
  intro z hz
  have h1 : z.natAbs ≤ S.sup Int.natAbs := le_sup (f := Int.natAbs) hz
  have h2 : S.sup Int.natAbs ≤ u.sup fun S => S.sup Int.natAbs :=
    le_sup (f := fun S => S.sup Int.natAbs) hS
  rw [mem_Icc]
  omega

/-- **DLMF §1.3(iii)**: Hill-type determinants always converge (von Koch): `Dₙ[a]` is the sum of
the principal minors of `b = a − δ` over the subsets of `[−n, n]`, and these minors are absolutely
summable over all finite subsets of `ℤ`, being bounded by `∏_{j ∈ S} ∑ᵢ |bᵢⱼ|`. -/
theorem dlmf_1_3_iii_hill_converges {a : ℤ → ℤ → ℂ} (ha : IsHillType a) :
    ∃ L, InfDetConverges a L := by
  set b : ℤ → ℤ → ℂ := fun i j => a i j - if i = j then 1 else 0 with hb
  have hsymm : Summable fun p : ℤ × ℤ => ‖b p.2 p.1‖ := ha.prod_symm
  have hcol : ∀ j, Summable fun i => ‖b i j‖ := fun j => hsymm.prod_factor j
  have hr : Summable fun j => ∑' i, ‖b i j‖ :=
    (HasSum.prod_fiberwise hsymm.hasSum fun j => (hcol j).hasSum).summable
  have hm : Summable (hillMinor b) :=
    Summable.of_norm_bounded (summable_prod_finset (fun j => tsum_nonneg fun i => norm_nonneg _) hr)
      (norm_hillMinor_le b hcol)
  refine ⟨∑' S, hillMinor b S, ?_⟩
  have := hm.hasSum.comp tendsto_powerset_Icc
  refine this.congr fun n => ?_
  exact (infDet_eq_sum_hillMinor a n).symm

end Azurite.DLMF
