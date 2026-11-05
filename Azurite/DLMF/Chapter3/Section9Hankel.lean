/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.LinearCombination

/-!
# Hankel determinants and the Desnanot–Jacobi identity (for DLMF §3.9(iv))

* `desnanot_jacobi`: for an `(k + 2) × (k + 2)` matrix `M` whose leading `k × k` block `A` has
  `det A ≠ 0`, `det M · det A = B₀₀ B₁₁ − B₀₁ B₁₀`, where `B_{pq}` is `A` bordered by row `k + p`
  and column `k + q` (via Schur complements).
* `hankel u m n = det (u_{n+i+j})_{i,j<m}` (DLMF 3.9.10).
* Row and column differences: `det_rowDiff`, `det_onesRow`.
* The Hankel identities behind Wynn's epsilon algorithm (`hankel_J1`, `hankel_J2`):
  `H_{k+1}^{n+1}(u) H_k^n(Δ²u) − H_{k+1}^n(u) H_k^{n+1}(Δ²u) = H_{k+1}^n(Δu) H_k^{n+1}(Δu)`,
  `H_{k+2}^n(u) H_k^{n+1}(Δ²u) − H_{k+1}^{n+1}(u) H_{k+1}^n(Δ²u)
  = −H_{k+1}^n(Δu) H_{k+1}^{n+1}(Δu)`,
  for `H_k^{n+1}(Δu) ≠ 0`.
-/

open Matrix Finset

namespace Azurite.DLMF

variable {𝕜 : Type*} [Field 𝕜]

/-! ### Desnanot–Jacobi -/

/-- The rows/columns `0, …, k − 1` and then `k + p`. -/
def djSel (k : ℕ) (p : Fin 2) : Fin (k + 1) → Fin (k + 2) :=
  Fin.lastCases (Fin.natAdd k p) fun i => Fin.castAdd 2 i

/-- Schur complement for a matrix over `Fin k ⊕ ι` with invertible leading block. -/
theorem det_schur {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix (Fin k ⊕ ι) (Fin k ⊕ ι) 𝕜) (hA : N.toBlocks₁₁.det ≠ 0) :
    N.det = N.toBlocks₁₁.det * (Matrix.of fun p q => N (Sum.inr p) (Sum.inr q) -
      ∑ i, ∑ j, N (Sum.inr p) (Sum.inl i) * N.toBlocks₁₁⁻¹ i j *
        N (Sum.inl j) (Sum.inr q)).det := by
  have : Invertible N.toBlocks₁₁.det := invertibleOfNonzero hA
  have : Invertible N.toBlocks₁₁ := N.toBlocks₁₁.invertibleOfDetInvertible
  conv_lhs => rw [← fromBlocks_toBlocks N]
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 2
  ext p q
  simp only [Matrix.sub_apply, Matrix.mul_apply, of_apply, toBlocks₂₂, toBlocks₂₁, toBlocks₁₂,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **Desnanot–Jacobi identity**: for `M` of size `k + 2` with leading `k × k` block `A`,
`det A ≠ 0`, `det M · det A = B₀₀ B₁₁ − B₀₁ B₁₀`, `B_{pq}` the block `A` bordered by row `k + p`
and column `k + q`. -/
theorem desnanot_jacobi {k : ℕ} (M : Matrix (Fin (k + 2)) (Fin (k + 2)) 𝕜)
    (hA : (M.submatrix (Fin.castAdd 2) (Fin.castAdd 2)).det ≠ 0) :
    M.det * (M.submatrix (Fin.castAdd 2) (Fin.castAdd 2)).det =
      (M.submatrix (djSel k 0) (djSel k 0)).det * (M.submatrix (djSel k 1) (djSel k 1)).det -
        (M.submatrix (djSel k 0) (djSel k 1)).det * (M.submatrix (djSel k 1) (djSel k 0)).det := by
  set A := M.submatrix (Fin.castAdd 2) (Fin.castAdd 2)
  set S : Fin 2 → Fin 2 → 𝕜 := fun p q => M (Fin.natAdd k p) (Fin.natAdd k q) -
    ∑ i, ∑ j, M (Fin.natAdd k p) (Fin.castAdd 2 i) * A⁻¹ i j * M (Fin.castAdd 2 j) (Fin.natAdd k q)
  have h2 : M.det = A.det * (Matrix.of S).det := by
    rw [← det_submatrix_equiv_self finSumFinEquiv M]
    have hb : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ = A := by
      ext i j; simp [toBlocks₁₁, A]
    rw [det_schur _ (by rw [hb]; exact hA), hb]
    congr 2
  have hc : ∀ i : Fin k, Fin.castAdd 1 i = Fin.castSucc i := fun _ => rfl
  have hl : Fin.natAdd k (0 : Fin 1) = Fin.last k := rfl
  have h1 : ∀ p q, (M.submatrix (djSel k p) (djSel k q)).det = A.det * S p q := by
    intro p q
    rw [← det_submatrix_equiv_self (finSumFinEquiv (m := k) (n := 1))]
    have hb : ((M.submatrix (djSel k p) (djSel k q)).submatrix finSumFinEquiv
        finSumFinEquiv).toBlocks₁₁ = A := by
      ext i j
      simp only [toBlocks₁₁, of_apply, submatrix_apply, finSumFinEquiv_apply_left, A]
      simp [djSel, hc]
    rw [det_schur _ (by rw [hb]; exact hA), hb, det_unique (n := Fin 1)]
    congr 1
    simp [S, djSel, hc, hl]
  rw [h2, h1, h1, h1, h1, det_fin_two]
  simp only [of_apply]
  ring

/-! ### Hankel determinants and bordered matrices -/

/-- **DLMF 3.9.10**: the Hankel determinant `H_m(u_n) = det (u_{n+i+j})_{i,j<m}`. -/
def hankel (u : ℕ → 𝕜) (m n : ℕ) : 𝕜 := (Matrix.of fun i j : Fin m => u (n + i + j)).det

/-- The `(m + 1) × (m + 1)` matrix with rows `g i j` (`i < m`) and last row `r j`. -/
def bordMat (m : ℕ) (g : ℕ → ℕ → 𝕜) (r : ℕ → 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) < m then g i j else r j

theorem sum_fin_ite_val {m : ℕ} (f : Fin (m + 1) → 𝕜) {a : ℕ} (ha : a < m + 1) :
    ∑ l : Fin (m + 1), (if (l : ℕ) = a then f l else 0) = f ⟨a, ha⟩ := by
  rw [Finset.sum_eq_single ⟨a, ha⟩]
  · simp
  · intro b _ hb
    rw [ite_eq_right_iff]
    intro h; exact absurd (Fin.ext h) hb
  · simp

/-- Row differences: `det (bordMat m (Δu_{a+i+j}) (u_{a+m+j})) = (−1)^m H_{m+1}(u_a)`. -/
theorem det_rowDiff (u : ℕ → 𝕜) (m a : ℕ) :
    (bordMat m (fun i j => fwdDiff 1 u (a + i + j)) (fun j => u (a + m + j))).det =
      (-1) ^ m * hankel u (m + 1) a := by
  set T : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 := Matrix.of fun i l =>
    if (i : ℕ) < m then (if (l : ℕ) = i + 1 then 1 else 0) - (if (l : ℕ) = i then 1 else 0)
    else (if (l : ℕ) = i then 1 else 0)
  have hT : T.det = (-1) ^ m := by
    rw [det_of_isUpperTriangular]
    · rw [Fin.prod_univ_castSucc]
      simp [T]
    · intro i l hli
      have : (l : ℕ) < i := hli
      simp only [T, of_apply]
      split_ifs <;> first | (exfalso; omega) | rfl | simp
  have hmul : bordMat m (fun i j => fwdDiff 1 u (a + i + j)) (fun j => u (a + m + j)) =
      T * Matrix.of fun i j : Fin (m + 1) => u (a + i + j) := by
    ext i j
    simp only [bordMat, T, of_apply, mul_apply]
    split_ifs with hi
    · simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
      rw [sum_fin_ite_val (fun l : Fin (m + 1) => u (a + l + j)) (by omega),
        sum_fin_ite_val (fun l : Fin (m + 1) => u (a + l + j)) (by omega)]
      simp only [fwdDiff]
      ring_nf
    · simp only [ite_mul, one_mul, zero_mul]
      rw [sum_fin_ite_val (fun l : Fin (m + 1) => u (a + l + j)) (by omega)]
      have : (i : ℕ) = m := by omega
      simp [this]
  rw [hmul, det_mul, hT, hankel]

/-- Column differences against a last row of ones:
`det (bordMat m g 1) = (−1)^m det (g i (j + 1) − g i j)`. -/
theorem det_onesRow (m : ℕ) (g : ℕ → ℕ → 𝕜) :
    (bordMat m g fun _ => 1).det =
      (-1) ^ m * (Matrix.of fun i j : Fin m => g i (j + 1) - g i j).det := by
  set U : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 := Matrix.of fun l j =>
    (if (l : ℕ) = j then 1 else 0) - (if (l : ℕ) + 1 = j then 1 else 0)
  have hU : U.det = 1 := by
    rw [det_of_isUpperTriangular]
    · simp [U]
    · intro i l hli
      have : (l : ℕ) < i := hli
      simp only [U, of_apply]
      split_ifs <;> first | (exfalso; omega) | rfl | simp
  set B := bordMat m g fun _ => 1
  have hmul : ∀ i j, (B * U) i j =
      B i j - (if h : (j : ℕ) = 0 then 0 else B i ⟨(j : ℕ) - 1, by omega⟩) := by
    intro i j
    simp only [U, of_apply, mul_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
      mul_zero]
    rw [sum_fin_ite_val (fun l => B i l) j.isLt]
    congr 1
    split_ifs with hj
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [ite_eq_right_iff]; omega
    · have hlt : (j : ℕ) - 1 < m + 1 := by omega
      rw [Finset.sum_eq_single ⟨(j : ℕ) - 1, hlt⟩ (fun b _ hb => by
        rw [ite_eq_right_iff]; intro h; exact absurd (Fin.ext (by simp; omega)) hb) (by simp)]
      rw [ite_eq_left_iff.mpr (fun h => absurd (show (j : ℕ) - 1 + 1 = j by omega) h)]
  have hdet : B.det = (B * U).det := by
    rw [det_mul, hU, mul_one]
  rw [hdet, det_succ_row _ (Fin.last m), Finset.sum_eq_single 0]
  · have e0 : (B * U) (Fin.last m) 0 = 1 := by rw [hmul]; simp [B, bordMat]
    have esub : (B * U).submatrix (Fin.last m).succAbove (0 : Fin (m + 1)).succAbove =
        Matrix.of fun i j : Fin m => g i (j + 1) - g i j := by
      ext i j
      simp only [submatrix_apply, Fin.succAbove_last, Fin.succAbove_zero]
      rw [hmul]
      simp [B, bordMat, Fin.val_succ]
    rw [e0, esub]
    simp
  · intro b _ hb
    rw [hmul]
    have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
    simp [B, bordMat, this]
  · simp

/-! ### Sylvester's identity for Hankel-bordered matrices -/

/-- `F₂(r₁, r₂)`: rows `Δu_{n+i+j}` (`i < k`), `r₁ j`, `r₂ j` (`j ≤ k + 1`). -/
def sylv2 (u : ℕ → 𝕜) (n k : ℕ) (r₁ r₂ : ℕ → 𝕜) : 𝕜 :=
  (Matrix.of fun i j : Fin (k + 2) =>
    if (i : ℕ) < k then fwdDiff 1 u (n + i + j) else if (i : ℕ) = k then r₁ j else r₂ j).det

/-- `F₁(r, c)`: rows `Δu_{n+c+i+j}` (`i < k`) and `r (c + j)` (`j ≤ k`). -/
def sylv1 (u : ℕ → 𝕜) (n k : ℕ) (r : ℕ → 𝕜) (c : ℕ) : 𝕜 :=
  (bordMat k (fun i j => fwdDiff 1 u (n + c + i + j)) (fun j => r (c + j))).det

theorem val_djSel (k : ℕ) (p : Fin 2) (i : Fin (k + 1)) :
    ((djSel k p i : Fin (k + 2)) : ℕ) = if (i : ℕ) < k then (i : ℕ) else k + p := by
  induction i using Fin.lastCases with
  | last => simp [djSel]
  | cast i => simp [djSel, i.isLt]

theorem sign_finRotate_cast (m : ℕ) :
    ((Equiv.Perm.sign (finRotate (m + 1)) : ℤ) : 𝕜) = (-1) ^ m := by
  rw [sign_finRotate]
  simp

theorem val_finRotate_djSel0 (k : ℕ) (j : Fin (k + 1)) :
    ((finRotate (k + 2) (djSel k 0 j) : Fin (k + 2)) : ℕ) = j + 1 := by
  rw [coe_finRotate, ite_eq_right, val_djSel]
  · split_ifs with h
    · rfl
    · have := j.isLt; simp; omega
  · intro h
    have := congrArg Fin.val h
    rw [val_djSel] at this
    simp at this
    split_ifs at this <;> omega

theorem val_finRotate_djSel1 (k : ℕ) (j : Fin (k + 1)) :
    ((finRotate (k + 2) (djSel k 1 j) : Fin (k + 2)) : ℕ) =
      ((finRotate (k + 1) j : Fin (k + 1)) : ℕ) := by
  induction j using Fin.lastCases with
  | last =>
    have : djSel k 1 (Fin.last k) = Fin.last (k + 1) := by
      apply Fin.ext; rw [val_djSel]; simp
    rw [this, finRotate_last, finRotate_last]
    simp
  | cast j =>
    have h1 : djSel k 1 (Fin.castSucc j) ≠ Fin.last (k + 1) := by
      intro h; have := congrArg Fin.val h; rw [val_djSel] at this; simp at this; omega
    rw [coe_finRotate, coe_finRotate, ite_eq_right h1, ite_eq_right (Fin.castSucc_ne_last j),
      val_djSel]
    simp

theorem val_finRotate_castAdd (k : ℕ) (j : Fin k) :
    ((finRotate (k + 2) (Fin.castAdd 2 j) : Fin (k + 2)) : ℕ) = j + 1 := by
  rw [coe_finRotate, ite_eq_right]
  · simp
  · intro h; have := congrArg Fin.val h; simp at this; omega

/-- Sylvester's identity for the bordered Hankel matrices `F₁`, `F₂`:
`F₂(r₁, r₂) H_k^{n+1}(Δu) = F₁(r₁, 0) F₁(r₂, 1) − F₁(r₁, 1) F₁(r₂, 0)`. -/
theorem sylvester_hankel (u : ℕ → 𝕜) (n k : ℕ) (r₁ r₂ : ℕ → 𝕜)
    (hI : hankel (fwdDiff 1 u) k (n + 1) ≠ 0) :
    sylv2 u n k r₁ r₂ * hankel (fwdDiff 1 u) k (n + 1) =
      sylv1 u n k r₁ 0 * sylv1 u n k r₂ 1 - sylv1 u n k r₁ 1 * sylv1 u n k r₂ 0 := by
  set E : ℕ → ℕ → 𝕜 := fun a b =>
    if a < k then fwdDiff 1 u (n + a + b) else if a = k then r₁ b else r₂ b
  set Mn : Matrix (Fin (k + 2)) (Fin (k + 2)) 𝕜 := Matrix.of fun i j => E i j
  set M' := Mn.submatrix id (finRotate (k + 2))
  have hM' : M'.det = (-1) ^ (k + 1) * sylv2 u n k r₁ r₂ := by
    rw [det_permute', sign_finRotate_cast]
    rfl
  have hA : M'.submatrix (Fin.castAdd 2) (Fin.castAdd 2) =
      Matrix.of fun i j : Fin k => fwdDiff 1 u (n + 1 + i + j) := by
    ext i j
    simp only [M', Mn, submatrix_apply, id, of_apply, val_finRotate_castAdd, E,
      Fin.val_castAdd, i.isLt, ↓reduceIte]
    congr 1; ring
  have hdetA : (M'.submatrix (Fin.castAdd 2) (Fin.castAdd 2)).det =
      hankel (fwdDiff 1 u) k (n + 1) := by
    rw [hA, hankel]
  have hE : ∀ (p : Fin 2) (i : Fin (k + 1)) (b : ℕ), E (djSel k p i) b =
      if (i : ℕ) < k then fwdDiff 1 u (n + i + b) else (if p = 0 then r₁ else r₂) b := by
    intro p i b
    simp only [E, val_djSel]
    by_cases hi : (i : ℕ) < k
    · simp [hi]
    · fin_cases p <;> simp [hi]
  have hB0 : ∀ p : Fin 2, (M'.submatrix (djSel k p) (djSel k 0)).det =
      sylv1 u n k (if p = 0 then r₁ else r₂) 1 := by
    intro p
    rw [sylv1]
    congr 1
    ext i j
    simp only [M', Mn, submatrix_apply, id, of_apply, val_finRotate_djSel0, hE, bordMat]
    split_ifs <;> (congr 1; ring)
  have hB1 : ∀ p : Fin 2, (M'.submatrix (djSel k p) (djSel k 1)).det =
      (-1) ^ k * sylv1 u n k (if p = 0 then r₁ else r₂) 0 := by
    intro p
    rw [sylv1, ← sign_finRotate_cast, ← det_permute']
    congr 1
    ext i j
    simp only [M', Mn, submatrix_apply, id, of_apply, val_finRotate_djSel1, hE, bordMat,
      add_zero, zero_add]
  have hDJ := desnanot_jacobi M' (by rw [hdetA]; exact hI)
  rw [hM', hdetA, hB0, hB0, hB1, hB1] at hDJ
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero] at hDJ
  have hs : ((-1 : 𝕜) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  set F := sylv2 u n k r₁ r₂
  set H := hankel (fwdDiff 1 u) k (n + 1)
  set a₀ := sylv1 u n k r₁ 0
  set a₁ := sylv1 u n k r₁ 1
  set b₀ := sylv1 u n k r₂ 0
  set b₁ := sylv1 u n k r₂ 1
  rw [pow_succ] at hDJ
  linear_combination (-(-1 : 𝕜) ^ k) * hDJ - (F * H - (a₀ * b₁ - a₁ * b₀)) * hs

/-! ### The bordered determinants as Hankel determinants -/

theorem det_bordMat_congr {m : ℕ} {g g' : ℕ → ℕ → 𝕜} {r r' : ℕ → 𝕜}
    (hg : ∀ i j, i < m → g i j = g' i j) (hr : ∀ j, r j = r' j) :
    (bordMat m g r).det = (bordMat m g' r').det := by
  congr 1
  ext i j
  simp only [bordMat, of_apply]
  split_ifs with h
  · exact hg _ _ h
  · exact hr _

/-- `F₁(u_{n+k+·}, c) = (−1)^k H_{k+1}(u_{n+c})`. -/
theorem sylv1_u (u : ℕ → 𝕜) (n k c : ℕ) :
    sylv1 u n k (fun j => u (n + k + j)) c = (-1) ^ k * hankel u (k + 1) (n + c) := by
  rw [sylv1, ← det_rowDiff]
  exact det_bordMat_congr (fun _ _ _ => rfl) (fun j => by congr 1; ring)

/-- `F₁(1, c) = (−1)^k H_k(Δ²u_{n+c})`. -/
theorem sylv1_one (u : ℕ → 𝕜) (n k c : ℕ) :
    sylv1 u n k (fun _ => 1) c = (-1) ^ k * hankel (fwdDiff 1 (fwdDiff 1 u)) k (n + c) := by
  rw [sylv1, det_onesRow, hankel]
  congr 2

/-- `F₁(Δu_{n+k+·}, c) = H_{k+1}(Δu_{n+c})`. -/
theorem sylv1_du (u : ℕ → 𝕜) (n k c : ℕ) :
    sylv1 u n k (fun j => fwdDiff 1 u (n + k + j)) c = hankel (fwdDiff 1 u) (k + 1) (n + c) := by
  rw [sylv1, hankel]
  congr 1
  ext i j
  simp only [bordMat, of_apply]
  split_ifs with h
  · rfl
  · have : (i : ℕ) = k := by have := i.isLt; omega
    rw [this]; congr 1; ring

theorem sylv2_eq_bordMat (u : ℕ → 𝕜) (n k : ℕ) (r₁ r₂ : ℕ → 𝕜) :
    sylv2 u n k r₁ r₂ = (bordMat (k + 1)
      (fun i j => if i < k then fwdDiff 1 u (n + i + j) else r₁ j) r₂).det := by
  rw [sylv2]
  congr 1
  ext i j
  simp only [bordMat, of_apply]
  by_cases h : (i : ℕ) < k
  · simp [h, show (i : ℕ) < k + 1 by omega]
  · by_cases h' : (i : ℕ) = k
    · simp [h']
    · have : ¬ (i : ℕ) < k + 1 := by omega
      simp [h, h', this]

/-- `F₂(u_{n+k+·}, 1) = −H_{k+1}(Δu_n)`. -/
theorem sylv2_u_one (u : ℕ → 𝕜) (n k : ℕ) :
    sylv2 u n k (fun j => u (n + k + j)) (fun _ => 1) = -hankel (fwdDiff 1 u) (k + 1) n := by
  rw [sylv2_eq_bordMat, det_onesRow]
  have h := det_rowDiff (fwdDiff 1 u) k n
  have e : (Matrix.of fun i j : Fin (k + 1) =>
      (if (i : ℕ) < k then fwdDiff 1 u (n + i + (j + 1)) else u (n + k + (j + 1))) -
        (if (i : ℕ) < k then fwdDiff 1 u (n + i + j) else u (n + k + j))) =
      bordMat k (fun i j => fwdDiff 1 (fwdDiff 1 u) (n + i + j))
        (fun j => fwdDiff 1 u (n + k + j)) := by
    ext i j
    simp only [bordMat, of_apply]
    split_ifs <;> simp only [fwdDiff] <;> ring_nf
  rw [e, h]
  have hs : ((-1 : 𝕜) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [pow_succ]
  linear_combination (-hankel (fwdDiff 1 u) (k + 1) n) * hs

/-- `F₂(Δu_{n+k+·}, 1) = (−1)^{k+1} H_{k+1}(Δ²u_n)`. -/
theorem sylv2_du_one (u : ℕ → 𝕜) (n k : ℕ) :
    sylv2 u n k (fun j => fwdDiff 1 u (n + k + j)) (fun _ => 1) =
      (-1) ^ (k + 1) * hankel (fwdDiff 1 (fwdDiff 1 u)) (k + 1) n := by
  have e := sylv1_one u n (k + 1) 0
  rw [add_zero] at e
  rw [sylv2_eq_bordMat, ← e, sylv1]
  refine det_bordMat_congr (fun i j hi => ?_) (fun _ => rfl)
  split_ifs with h
  · simp
  · have : i = k := by omega
    subst this; simp

/-- `F₂(Δu_{n+k+·}, u_{n+k+·}) = (−1)^{k+1} H_{k+2}(u_n)`. -/
theorem sylv2_du_u (u : ℕ → 𝕜) (n k : ℕ) :
    sylv2 u n k (fun j => fwdDiff 1 u (n + k + j)) (fun j => u (n + k + j)) =
      (-1) ^ (k + 1) * hankel u (k + 2) n := by
  rw [← det_rowDiff, sylv2_eq_bordMat]
  set X := bordMat (k + 1) (fun i j => if i < k then fwdDiff 1 u (n + i + j)
    else fwdDiff 1 u (n + k + j)) (fun j => u (n + k + j))
  have hne : (Fin.last (k + 1)) ≠ (Fin.castSucc (Fin.last k)) := by
    intro h; have := congrArg Fin.val h; simp at this
  rw [← det_updateRow_add_self X hne]
  congr 1
  ext i j
  by_cases hi : i = Fin.last (k + 1)
  · subst hi
    simp only [updateRow_self, Pi.add_apply, X, bordMat, of_apply, Fin.val_last, lt_irrefl,
      ↓reduceIte, Fin.val_castSucc, lt_add_one, fwdDiff]
    ring_nf
  · rw [updateRow_ne hi]
    have hlt : (i : ℕ) < k + 1 := by
      have := i.isLt
      have : (i : ℕ) ≠ k + 1 := fun h => hi (Fin.ext h)
      omega
    simp only [X, bordMat, of_apply, hlt, ↓reduceIte]
    split_ifs with h
    · rfl
    · have : (i : ℕ) = k := by omega
      rw [this]

/-! ### The identities -/

/-- `H_{k+1}^{n+1}(u) H_k^n(Δ²u) − H_{k+1}^n(u) H_k^{n+1}(Δ²u) = H_{k+1}^n(Δu) H_k^{n+1}(Δu)`
(for `H_k^{n+1}(Δu) ≠ 0`). -/
theorem hankel_J1 (u : ℕ → 𝕜) (n k : ℕ) (hI : hankel (fwdDiff 1 u) k (n + 1) ≠ 0) :
    hankel u (k + 1) (n + 1) * hankel (fwdDiff 1 (fwdDiff 1 u)) k n -
      hankel u (k + 1) n * hankel (fwdDiff 1 (fwdDiff 1 u)) k (n + 1) =
      hankel (fwdDiff 1 u) (k + 1) n * hankel (fwdDiff 1 u) k (n + 1) := by
  have h := sylvester_hankel u n k (fun j => u (n + k + j)) (fun _ => 1) hI
  rw [sylv2_u_one, sylv1_u, sylv1_u, sylv1_one, sylv1_one, add_zero] at h
  have hs : ((-1 : 𝕜) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination h + (hankel u (k + 1) n * hankel (fwdDiff 1 (fwdDiff 1 u)) k (n + 1) -
    hankel u (k + 1) (n + 1) * hankel (fwdDiff 1 (fwdDiff 1 u)) k n) * hs

/-- `H_{k+2}^n(u) H_k^{n+1}(Δ²u) − H_{k+1}^{n+1}(u) H_{k+1}^n(Δ²u)
= −H_{k+1}^n(Δu) H_{k+1}^{n+1}(Δu)` (for `H_k^{n+1}(Δu) ≠ 0`). -/
theorem hankel_J2 (u : ℕ → 𝕜) (n k : ℕ) (hI : hankel (fwdDiff 1 u) k (n + 1) ≠ 0) :
    hankel u (k + 2) n * hankel (fwdDiff 1 (fwdDiff 1 u)) k (n + 1) -
      hankel u (k + 1) (n + 1) * hankel (fwdDiff 1 (fwdDiff 1 u)) (k + 1) n =
      -(hankel (fwdDiff 1 u) (k + 1) n * hankel (fwdDiff 1 u) (k + 1) (n + 1)) := by
  have hJ1 := hankel_J1 u n k hI
  have hK1 := sylvester_hankel u n k (fun j => fwdDiff 1 u (n + k + j)) (fun _ => 1) hI
  have hK2 := sylvester_hankel u n k (fun j => fwdDiff 1 u (n + k + j))
    (fun j => u (n + k + j)) hI
  rw [sylv2_du_one, sylv1_du, sylv1_du, sylv1_one, sylv1_one, add_zero] at hK1
  rw [sylv2_du_u, sylv1_du, sylv1_du, sylv1_u, sylv1_u, add_zero] at hK2
  rw [pow_succ] at hK1 hK2
  set q := hankel (fwdDiff 1 u) k (n + 1)
  set a0 := hankel u (k + 1) n
  set a1 := hankel u (k + 1) (n + 1)
  set A := hankel u (k + 2) n
  set d0 := hankel (fwdDiff 1 (fwdDiff 1 u)) k n
  set d1 := hankel (fwdDiff 1 (fwdDiff 1 u)) k (n + 1)
  set D := hankel (fwdDiff 1 (fwdDiff 1 u)) (k + 1) n
  set Q0 := hankel (fwdDiff 1 u) (k + 1) n
  set Q1 := hankel (fwdDiff 1 u) (k + 1) (n + 1)
  set y : 𝕜 := (-1) ^ k
  have hy : y ^ 2 = 1 := by simp only [y]; rw [← pow_mul, mul_comm, pow_mul]; simp
  -- `D q = −Q0 d1 + Q1 d0`, `A q = −Q0 a1 + Q1 a0`
  have eD : D * q = -(Q0 * d1) + Q1 * d0 := by
    linear_combination (-y) * hK1 - (D * q + Q0 * d1 - Q1 * d0) * hy
  have eA : A * q = -(Q0 * a1) + Q1 * a0 := by
    linear_combination (-y) * hK2 - (A * q + Q0 * a1 - Q1 * a0) * hy
  have key : (A * d1 - a1 * D + Q0 * Q1) * q = 0 := by
    linear_combination d1 * eA - a1 * eD - Q1 * hJ1
  rcases mul_eq_zero.mp key with h | h
  · linear_combination h
  · exact absurd h hI

end Azurite.DLMF
