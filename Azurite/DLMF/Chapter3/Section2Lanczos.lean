/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter3.Section2Eigen

/-!
# DLMF §3.2(vi): Lanczos tridiagonalization of a symmetric matrix

`A` is a real symmetric `n × n` matrix.

* **3.2.21 / 3.2.24**: the general recursion with a Gram matrix `S = LᵀL` (`lzStep`, `lzState`,
  `lzV`, `lzα`, `lzβ`, `dlmf_3_2_24`). Here `u = (A − α_j S)v_j − β_j S v_{j−1}`,
  `β_{j+1} = ‖L⁻ᵀu‖₂`, `v_{j+1} = L⁻¹L⁻ᵀu/β_{j+1}` and `α_{j+1} = v_{j+1}ᵀAv_{j+1}`, from `v₀ = 0`,
  `v₁`, `α₁ = v₁ᵀAv₁`, `β₁ = 0` (`lzV_one`, `lzα_one`, `lzβ_one`). The plain Lanczos recursion
  3.2.21 is the case `S = I`, `L = I`.
* **Orthonormality** (`dlmf_3_2_21_orthonormal`, `dlmf_3_2_24_orthonormal`):
  `v_jᵀv_k = δ_{jk}`, respectively `v_jᵀSv_k = δ_{jk}`.
  * The proof is a three-term induction (`lanczos_orthonormal_aux`) using only the recursion, the
    symmetry of `A` and `S`, and the normalizations.
  * It needs `β_{j+1} ≠ 0` for `j < n` (no breakdown), which the DLMF leaves implicit; see
    `docs/dlmf_errata.md`.
* **3.2.22**: `B` (`lanczosB`) equals `VᵀAV` for the orthogonal `V` with columns `v_j`
  (`lanczosV_spec`, `lz_entry`). Hence `B` has the same characteristic polynomial, and the same
  eigenvalues, as `A` (`dlmf_3_2_22`).
* **3.2.23**: `p_{k+1}(λ) = (λ − α_{k+1})p_k(λ) − β_{k+1}² p_{k−1}(λ)` for the leading blocks
  (`lanczosP`, `dlmf_3_2_23`). This rests on the three-term recurrence for tridiagonal
  determinants (`det_tridiag`, Laplace expansion along the last row and column).

The relation to Gauss quadrature (§3.5(v)) and the numerical remarks are not formalized.
-/

namespace Azurite.DLMF

open scoped Matrix
open Matrix Polynomial WithLp

variable {n : ℕ}

/-! ### Orthonormality of a three-term recursion -/

theorem dot_mulVec_symm {S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ = S) (x y : Fin n → ℝ) :
    x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]

/-- **Orthonormality** for any sequence obeying the Lanczos relations: if
`β_{j+1} S v_{j+1} = A v_j − α_j S v_j − β_j S v_{j−1}` (`v₀ = 0`), `α_j = v_jᵀ A v_j`,
`v_jᵀ S v_j = 1` and `β_{j+1} ≠ 0`, then `v_jᵀ S v_k = δ_{jk}`, `j, k = 1, …, N`. -/
theorem lanczos_orthonormal_aux {A S : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (hS : Sᵀ = S)
    (V : ℕ → Fin n → ℝ) (α β : ℕ → ℝ) (N : ℕ) (h0 : V 0 = 0)
    (hα : ∀ j, 1 ≤ j → j ≤ N → α j = V j ⬝ᵥ (A *ᵥ V j))
    (hrel : ∀ j, 1 ≤ j → j < N →
      β (j + 1) • (S *ᵥ V (j + 1)) = A *ᵥ V j - α j • (S *ᵥ V j) - β j • (S *ᵥ V (j - 1)))
    (hnorm : ∀ j, 1 ≤ j → j ≤ N → V j ⬝ᵥ (S *ᵥ V j) = 1)
    (hβ : ∀ j, 1 ≤ j → j < N → β (j + 1) ≠ 0) :
    ∀ m, m ≤ N → ∀ j k, 1 ≤ j → j ≤ m → 1 ≤ k → k ≤ m →
      V j ⬝ᵥ (S *ᵥ V k) = if j = k then 1 else 0 := by
  -- the inner product with `v₀ = 0` vanishes
  have hz : ∀ x, x ⬝ᵥ (S *ᵥ V 0) = 0 := fun x => by rw [h0, mulVec_zero, dotProduct_zero]
  -- `A v_k` expanded, for `1 ≤ k < N`
  have hAv : ∀ k, 1 ≤ k → k < N → ∀ x, x ⬝ᵥ (A *ᵥ V k) =
      β (k + 1) * (x ⬝ᵥ (S *ᵥ V (k + 1))) + α k * (x ⬝ᵥ (S *ᵥ V k)) +
        β k * (x ⬝ᵥ (S *ᵥ V (k - 1))) := by
    intro k hk1 hkN x
    have h := congrArg (fun w => x ⬝ᵥ w) (hrel k hk1 hkN)
    simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul] at h
    linarith
  intro m
  induction m with
  | zero => intro _ j k hj hjm; omega
  | succ m ih =>
    intro hm j k hj hjm hk hkm
    -- the new orthogonality relations `v_kᵀ S v_{m+1} = 0` for `k ≤ m`
    have hnew : ∀ k, 1 ≤ k → k ≤ m → V k ⬝ᵥ (S *ᵥ V (m + 1)) = 0 := by
      intro k hk1 hkm'
      have hm1 : 1 ≤ m := le_trans hk1 hkm'
      have hrelm := congrArg (fun w => V k ⬝ᵥ w) (hrel m hm1 (by omega))
      simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul] at hrelm
      have hsym : V k ⬝ᵥ (A *ᵥ V m) = V m ⬝ᵥ (A *ᵥ V k) := dot_mulVec_symm hA _ _
      have hIH := ih (by omega)
      have hkey : V k ⬝ᵥ (A *ᵥ V m) - α m * (V k ⬝ᵥ (S *ᵥ V m)) -
          β m * (V k ⬝ᵥ (S *ᵥ V (m - 1))) = 0 := by
        rcases (by omega : k = m ∨ k + 1 = m ∨ k + 2 ≤ m) with h | h | h
        · subst h
          rw [hIH k k hk1 le_rfl hk1 le_rfl, ← hα k hk1 (by omega)]
          rcases Nat.lt_or_ge 1 k with hk2 | hk2
          · rw [hIH k (k - 1) hk1 le_rfl (by omega) (by omega)]
            simp only [show ¬ k = k - 1 by omega, ↓reduceIte]; ring
          · rw [show k - 1 = 0 by omega, hz]; simp
        · rw [hsym, hAv k hk1 (by omega), h, hIH m m hm1 le_rfl hm1 le_rfl,
            hIH m k hm1 le_rfl hk1 (by omega), hIH k m hk1 (by omega) hm1 le_rfl,
            show m - 1 = k by omega, hIH k k hk1 (by omega) hk1 (by omega)]
          simp only [show ¬ m = k by omega, show ¬ k = m by omega, ↓reduceIte]
          rcases Nat.lt_or_ge 1 k with hk2 | hk2
          · rw [hIH m (k - 1) hm1 le_rfl (by omega) (by omega)]
            simp only [show ¬ m = k - 1 by omega, ↓reduceIte]; ring
          · rw [show k - 1 = 0 by omega, hz]; ring
        · rw [hsym, hAv k hk1 (by omega), hIH m (k + 1) hm1 le_rfl (by omega) (by omega),
            hIH m k hm1 le_rfl hk1 (by omega), hIH k m hk1 (by omega) hm1 le_rfl,
            hIH k (m - 1) hk1 (by omega) (by omega) (by omega)]
          simp only [show ¬ m = k + 1 by omega, show ¬ m = k by omega, show ¬ k = m by omega,
            show ¬ k = m - 1 by omega, ↓reduceIte]
          rcases Nat.lt_or_ge 1 k with hk2 | hk2
          · rw [hIH m (k - 1) hm1 le_rfl (by omega) (by omega)]
            simp only [show ¬ m = k - 1 by omega, ↓reduceIte]; ring
          · rw [show k - 1 = 0 by omega, hz]; ring
      have hb := hβ m hm1 (by omega)
      have : β (m + 1) * (V k ⬝ᵥ (S *ᵥ V (m + 1))) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hb
    rcases (by omega : j ≤ m ∨ j = m + 1) with hj' | hj' <;>
      rcases (by omega : k ≤ m ∨ k = m + 1) with hk' | hk'
    · exact ih (by omega) j k hj hj' hk hk'
    · subst hk'; rw [hnew j hj hj']; simp only [show ¬ j = m + 1 by omega, ↓reduceIte]
    · subst hj'; rw [dot_mulVec_symm hS, hnew k hk hk']
      simp only [show ¬ m + 1 = k by omega, ↓reduceIte]
    · subst hj' hk'; rw [hnorm (m + 1) (by omega) hm]; simp

/-! ### The algorithm 3.2.21 / 3.2.24 -/

/-- One step of 3.2.24 on the state `(v_{j−1}, v_j, α_j, β_j)`:
`u = (A − α_j S)v_j − β_j S v_{j−1}`, `β_{j+1} = ‖L⁻ᵀu‖₂`, `v_{j+1} = L⁻¹L⁻ᵀu/β_{j+1}`,
`α_{j+1} = v_{j+1}ᵀAv_{j+1}` (with `Lt = L⁻ᵀ`). -/
noncomputable def lzStep (A S Lt : Matrix (Fin n) (Fin n) ℝ)
    (s : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ) : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ :=
  let u := A *ᵥ s.2.1 - s.2.2.1 • (S *ᵥ s.2.1) - s.2.2.2 • (S *ᵥ s.1)
  let b := ‖toLp 2 (Lt *ᵥ u)‖
  let v := b⁻¹ • (Ltᵀ *ᵥ (Lt *ᵥ u))
  (s.2.1, v, v ⬝ᵥ (A *ᵥ v), b)

/-- The state `(v_{j−1}, v_j, α_j, β_j)` after `j − 1` steps, from `v₀ = 0`, `v₁`,
`α₁ = v₁ᵀAv₁`, `β₁ = 0`. -/
noncomputable def lzState (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) :
    ℕ → (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ
  | 0 => (0, v₁, v₁ ⬝ᵥ (A *ᵥ v₁), 0)
  | m + 1 => lzStep A S Lt (lzState A S Lt v₁ m)

/-- The Lanczos vectors `v_j` (`v₀ = 0`). -/
noncomputable def lzV (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) (j : ℕ) :
    Fin n → ℝ :=
  if j = 0 then 0 else (lzState A S Lt v₁ (j - 1)).2.1

/-- The coefficients `α_j`. -/
noncomputable def lzα (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) (j : ℕ) : ℝ :=
  (lzState A S Lt v₁ (j - 1)).2.2.1

/-- The coefficients `β_j` (`β₁ = 0`). -/
noncomputable def lzβ (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) (j : ℕ) : ℝ :=
  (lzState A S Lt v₁ (j - 1)).2.2.2

theorem lzState_fst (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) (m : ℕ) :
    (lzState A S Lt v₁ m).1 = lzV A S Lt v₁ m := by
  cases m with
  | zero => simp [lzState, lzV]
  | succ m => simp [lzState, lzStep, lzV]

theorem lzState_eq (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) (m : ℕ) :
    lzState A S Lt v₁ m =
      (lzV A S Lt v₁ m, lzV A S Lt v₁ (m + 1), lzα A S Lt v₁ (m + 1), lzβ A S Lt v₁ (m + 1)) := by
  ext : 1
  · exact lzState_fst A S Lt v₁ m
  · ext : 1
    · simp [lzV]
    · rfl

/-- **DLMF 3.2.24** (and **3.2.21** for `S = I`, `L = I`): for `j ≥ 1`, with
`u = (A − α_j S)v_j − β_j S v_{j−1}`, `β_{j+1} = ‖L⁻ᵀu‖₂`, `v_{j+1} = L⁻¹L⁻ᵀu/β_{j+1}`,
`α_{j+1} = v_{j+1}ᵀAv_{j+1}`. -/
theorem dlmf_3_2_24 (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) {j : ℕ} (hj : 1 ≤ j) :
    let u := A *ᵥ lzV A S Lt v₁ j - lzα A S Lt v₁ j • (S *ᵥ lzV A S Lt v₁ j) -
      lzβ A S Lt v₁ j • (S *ᵥ lzV A S Lt v₁ (j - 1))
    lzβ A S Lt v₁ (j + 1) = ‖toLp 2 (Lt *ᵥ u)‖ ∧
      lzV A S Lt v₁ (j + 1) = (lzβ A S Lt v₁ (j + 1))⁻¹ • (Ltᵀ *ᵥ (Lt *ᵥ u)) ∧
      lzα A S Lt v₁ (j + 1) = lzV A S Lt v₁ (j + 1) ⬝ᵥ (A *ᵥ lzV A S Lt v₁ (j + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have e : lzState A S Lt v₁ (m + 1) = lzStep A S Lt
      (lzV A S Lt v₁ m, lzV A S Lt v₁ (m + 1), lzα A S Lt v₁ (m + 1), lzβ A S Lt v₁ (m + 1)) := by
    rw [lzState, lzState_eq]
  have h1 : lzβ A S Lt v₁ (m + 1 + 1) = (lzState A S Lt v₁ (m + 1)).2.2.2 := rfl
  have h2 : lzV A S Lt v₁ (m + 1 + 1) = (lzState A S Lt v₁ (m + 1)).2.1 := by simp [lzV]
  have h3 : lzα A S Lt v₁ (m + 1 + 1) = (lzState A S Lt v₁ (m + 1)).2.2.1 := rfl
  simp only [Nat.add_sub_cancel]
  rw [h1, h2, h3, e]
  exact ⟨rfl, rfl, rfl⟩

theorem lzV_one (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) : lzV A S Lt v₁ 1 = v₁ := by
  simp [lzV, lzState]

theorem lzα_one (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) :
    lzα A S Lt v₁ 1 = v₁ ⬝ᵥ (A *ᵥ v₁) := by
  simp [lzα, lzState]

theorem lzβ_one (A S Lt : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) : lzβ A S Lt v₁ 1 = 0 := by
  simp [lzβ, lzState]

theorem dot_self_eq_norm_sq (z : Fin n → ℝ) : z ⬝ᵥ z = ‖toLp 2 z‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp [dotProduct, sq]

/-- **The Lanczos vectors are `S`-orthonormal**: `v_jᵀ S v_k = δ_{jk}`, `j, k = 1, …, n`, when
`A`, `S` are symmetric, `S L⁻¹L⁻ᵀ = I`, `v₁ᵀSv₁ = 1`, and the recursion does not break down
(`β_{j+1} ≠ 0`, `j < n`). -/
theorem lanczosS_orthonormal {A S Lt : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (hS : Sᵀ = S)
    (hSL : S * (Ltᵀ * Lt) = 1) {v₁ : Fin n → ℝ} (hv₁ : v₁ ⬝ᵥ (S *ᵥ v₁) = 1)
    (hβ : ∀ j, 1 ≤ j → j < n → lzβ A S Lt v₁ (j + 1) ≠ 0) :
    ∀ j k, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
      lzV A S Lt v₁ j ⬝ᵥ (S *ᵥ lzV A S Lt v₁ k) = if j = k then 1 else 0 := by
  set V := lzV A S Lt v₁
  -- `S v_{j+1} = u/β_{j+1}`
  have hSv : ∀ j, 1 ≤ j → lzβ A S Lt v₁ (j + 1) ≠ 0 →
      lzβ A S Lt v₁ (j + 1) • (S *ᵥ V (j + 1)) = A *ᵥ V j - lzα A S Lt v₁ j • (S *ᵥ V j) -
        lzβ A S Lt v₁ j • (S *ᵥ V (j - 1)) := by
    intro j hj hb
    obtain ⟨_, hv, _⟩ := dlmf_3_2_24 A S Lt v₁ hj
    simp only [V]
    rw [hv, mulVec_smul, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hSL, one_mulVec,
      smul_smul, mul_inv_cancel₀ hb, one_smul]
  have hnorm : ∀ j, 1 ≤ j → j ≤ n → V j ⬝ᵥ (S *ᵥ V j) = 1 := by
    intro j hj hjn
    rcases Nat.eq_or_lt_of_le hj with h | h
    · subst h; simp [V, lzV_one, hv₁]
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hb := hβ m (by omega) (by omega)
      obtain ⟨hbeta, hv, _⟩ := dlmf_3_2_24 A S Lt v₁ (j := m) (by omega)
      have hS' := hSv m (by omega) hb
      set u := A *ᵥ V m - lzα A S Lt v₁ m • (S *ᵥ V m) - lzβ A S Lt v₁ m • (S *ᵥ V (m - 1))
      have hSu : S *ᵥ V (m + 1) = (lzβ A S Lt v₁ (m + 1))⁻¹ • u := by
        rw [← hS', smul_smul, inv_mul_cancel₀ hb, one_smul]
      rw [hSu, dotProduct_smul]
      change (lzβ A S Lt v₁ (m + 1))⁻¹ • (lzV A S Lt v₁ (m + 1) ⬝ᵥ u) = 1
      rw [hv, smul_dotProduct, mulVec_transpose, ← dotProduct_mulVec, dot_self_eq_norm_sq,
        ← hbeta, smul_eq_mul, smul_eq_mul]
      field_simp
  exact lanczos_orthonormal_aux hA hS V (lzα A S Lt v₁) (lzβ A S Lt v₁) n (by simp [V, lzV])
    (fun j hj _ => by
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rcases m with _ | m
      · simp [V, lzV_one, lzα_one]
      · exact (dlmf_3_2_24 A S Lt v₁ (j := m + 1) (by omega)).2.2)
    (fun j hj hjn => hSv j hj (hβ j hj hjn)) hnorm hβ n le_rfl

/-- **DLMF 3.2.24**, `S`-orthogonality with `S = LᵀL` (`L` invertible, `Lt = L⁻ᵀ`). -/
theorem dlmf_3_2_24_orthonormal {A L : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A)
    (hL : IsUnit L.det) {v₁ : Fin n → ℝ} (hv₁ : v₁ ⬝ᵥ ((Lᵀ * L) *ᵥ v₁) = 1)
    (hβ : ∀ j, 1 ≤ j → j < n → lzβ A (Lᵀ * L) (L⁻¹)ᵀ v₁ (j + 1) ≠ 0) :
    ∀ j k, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
      lzV A (Lᵀ * L) (L⁻¹)ᵀ v₁ j ⬝ᵥ ((Lᵀ * L) *ᵥ lzV A (Lᵀ * L) (L⁻¹)ᵀ v₁ k) =
        if j = k then 1 else 0 := by
  refine lanczosS_orthonormal hA (by simp [Matrix.transpose_mul]) ?_ hv₁ hβ
  rw [transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc L, Matrix.mul_nonsing_inv _ hL,
    Matrix.one_mul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hL, transpose_one]

/-- **"Then `v_jᵀv_k = δ_{j,k}`, `j, k = 1, 2, …, n`"** (3.2.21: `S = I`, `L = I`), for a
normalized `v₁`, when the recursion does not break down. -/
theorem dlmf_3_2_21_orthonormal {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) {v₁ : Fin n → ℝ}
    (hv₁ : ‖toLp 2 v₁‖ = 1) (hβ : ∀ j, 1 ≤ j → j < n → lzβ A 1 1 v₁ (j + 1) ≠ 0) :
    ∀ j k, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
      lzV A 1 1 v₁ j ⬝ᵥ lzV A 1 1 v₁ k = if j = k then 1 else 0 := by
  intro j k hj hjn hk hkn
  have h := lanczosS_orthonormal hA (transpose_one) (by simp) (v₁ := v₁)
    (by rw [one_mulVec, dot_self_eq_norm_sq, hv₁]; norm_num) hβ j k hj hjn hk hkn
  rwa [one_mulVec] at h

/-! ### The tridiagonal matrix 3.2.22 -/

/-- The relation `β_{j+1} S v_{j+1} = (A − α_j S)v_j − β_j S v_{j−1}` when `β_{j+1} ≠ 0`. -/
theorem lz_rel {A S Lt : Matrix (Fin n) (Fin n) ℝ} (hSL : S * (Ltᵀ * Lt) = 1) (v₁ : Fin n → ℝ)
    {j : ℕ} (hj : 1 ≤ j) (hb : lzβ A S Lt v₁ (j + 1) ≠ 0) :
    lzβ A S Lt v₁ (j + 1) • (S *ᵥ lzV A S Lt v₁ (j + 1)) = A *ᵥ lzV A S Lt v₁ j -
      lzα A S Lt v₁ j • (S *ᵥ lzV A S Lt v₁ j) -
        lzβ A S Lt v₁ j • (S *ᵥ lzV A S Lt v₁ (j - 1)) := by
  obtain ⟨_, hv, _⟩ := dlmf_3_2_24 A S Lt v₁ hj
  rw [hv, mulVec_smul, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hSL, one_mulVec,
    smul_smul, mul_inv_cancel₀ hb, one_smul]

/-- The entries of 3.2.22 (indices from `0`): `α_{i+1}` on the diagonal, `β_{i+2}` beside it. -/
def lzBEntry (α β : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = j then α (i + 1) else if j = i + 1 then β (j + 1) else if i = j + 1 then β (i + 1) else 0

/-- **DLMF 3.2.22**: the tridiagonal matrix `B` (its leading `k × k` block). -/
noncomputable def lanczosB (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => lzBEntry (lzα A 1 1 v₁) (lzβ A 1 1 v₁) i j

/-- The matrix with columns `v₁, …, v_n`. -/
noncomputable def lanczosV (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun r c => lzV A 1 1 v₁ (c.val + 1) r

/-- `v_aᵀ A v_b` is the `(a, b)` entry of `B`. -/
theorem lz_entry {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) {v₁ : Fin n → ℝ}
    (hv₁ : ‖toLp 2 v₁‖ = 1) (hβ : ∀ j, 1 ≤ j → j < n → lzβ A 1 1 v₁ (j + 1) ≠ 0)
    (a b : ℕ) (ha : a < n) (hb : b < n) :
    lzV A 1 1 v₁ (a + 1) ⬝ᵥ (A *ᵥ lzV A 1 1 v₁ (b + 1)) =
      lzBEntry (lzα A 1 1 v₁) (lzβ A 1 1 v₁) a b := by
  set V := lzV A 1 1 v₁
  set α := lzα A 1 1 v₁
  set β := lzβ A 1 1 v₁
  have hO := dlmf_3_2_21_orthonormal hA hv₁ hβ
  have hz : ∀ x, x ⬝ᵥ V 0 = 0 := fun x => by simp [V, lzV]
  -- `x ⬝ A v_k` for `1 ≤ k < n`
  have hexp : ∀ k, 1 ≤ k → k < n → ∀ x, x ⬝ᵥ (A *ᵥ V k) =
      β (k + 1) * (x ⬝ᵥ V (k + 1)) + α k * (x ⬝ᵥ V k) + β k * (x ⬝ᵥ V (k - 1)) := by
    intro k hk hkn x
    have h := congrArg (fun w => x ⬝ᵥ w) (lz_rel (A := A) (S := 1) (Lt := 1) (by simp) v₁ hk
      (hβ k hk hkn))
    simp only [one_mulVec, dotProduct_smul, dotProduct_sub, smul_eq_mul] at h
    linarith
  have hαn : ∀ k, 1 ≤ k → α k = V k ⬝ᵥ (A *ᵥ V k) := fun k hk => by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rcases m with _ | m
    · simp [α, V, lzV_one, lzα_one]
    · exact (dlmf_3_2_24 A 1 1 v₁ (j := m + 1) (by omega)).2.2
  -- the inner products of the Lanczos vectors
  have hOV : ∀ c d, 1 ≤ c → c ≤ n → d ≤ n → V c ⬝ᵥ V d = if c = d then 1 else 0 := by
    intro c d hc hcn hdn
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, hz]; simp [show c ≠ 0 by omega]
    · exact hO c d hc hcn h hdn
  unfold lzBEntry
  rcases Nat.lt_or_ge (b + 1) n with hbn | hbn
  · rw [hexp (b + 1) (by omega) hbn, hOV (a + 1) (b + 1 + 1) (by omega) (by omega) (by omega),
      hOV (a + 1) (b + 1) (by omega) (by omega) (by omega),
      hOV (a + 1) (b + 1 - 1) (by omega) (by omega) (by omega)]
    split_ifs <;> subst_vars <;> first | omega | ring1
  · rcases Nat.lt_or_ge (a + 1) n with han | han
    · rw [dot_mulVec_symm hA, hexp (a + 1) (by omega) han,
        hOV (b + 1) (a + 1 + 1) (by omega) (by omega) (by omega),
        hOV (b + 1) (a + 1) (by omega) (by omega) (by omega),
        hOV (b + 1) (a + 1 - 1) (by omega) (by omega) (by omega)]
      split_ifs <;> subst_vars <;> first | omega | ring1
    · have hab : a = b := by omega
      subst hab
      simp only [↓reduceIte]
      exact (hαn (a + 1) (by omega)).symm

/-- `VᵀV = I` and `VᵀAV = B`. -/
theorem lanczosV_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) {v₁ : Fin n → ℝ}
    (hv₁ : ‖toLp 2 v₁‖ = 1) (hβ : ∀ j, 1 ≤ j → j < n → lzβ A 1 1 v₁ (j + 1) ≠ 0) :
    (lanczosV A v₁)ᵀ * lanczosV A v₁ = 1 ∧
      (lanczosV A v₁)ᵀ * A * lanczosV A v₁ = lanczosB A v₁ n := by
  have hO := dlmf_3_2_21_orthonormal hA hv₁ hβ
  constructor
  · ext i j
    have := hO (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega) (by omega)
    simp only [Matrix.mul_apply, transpose_apply, lanczosV, Matrix.of_apply, Matrix.one_apply]
    rw [show (∑ k, lzV A 1 1 v₁ (i.val + 1) k * lzV A 1 1 v₁ (j.val + 1) k) =
      lzV A 1 1 v₁ (i.val + 1) ⬝ᵥ lzV A 1 1 v₁ (j.val + 1) from rfl, this]
    simp [Fin.ext_iff]
  · ext i j
    rw [Matrix.mul_assoc, show lanczosB A v₁ n i j =
      lzBEntry (lzα A 1 1 v₁) (lzβ A 1 1 v₁) i j from rfl,
      ← lz_entry hA hv₁ hβ i.val j.val i.isLt j.isLt]
    simp only [Matrix.mul_apply, transpose_apply, lanczosV, Matrix.of_apply, dotProduct,
      Matrix.mulVec, Finset.mul_sum]

/-- **"The tridiagonal matrix `B` has the same eigenvalues as `A`"** (indeed the same
characteristic polynomial: `B = VᵀAV`, `V` orthogonal). -/
theorem dlmf_3_2_22 {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) {v₁ : Fin n → ℝ}
    (hv₁ : ‖toLp 2 v₁‖ = 1) (hβ : ∀ j, 1 ≤ j → j < n → lzβ A 1 1 v₁ (j + 1) ≠ 0) :
    (lanczosB A v₁ n).charpoly = A.charpoly ∧
      ∀ lam : ℝ, IsEigenvalue (lanczosB A v₁ n) lam ↔ IsEigenvalue A lam := by
  obtain ⟨h1, h2⟩ := lanczosV_spec hA hv₁ hβ
  set V := lanczosV A v₁
  have h1' : V * Vᵀ = 1 := mul_eq_one_comm.mp h1
  have hU : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr
    (Matrix.isUnit_det_of_left_inverse h1)
  have hinv : V⁻¹ = Vᵀ := Matrix.inv_eq_left_inv h1
  have hA' : A = (hU.unit : Matrix (Fin n) (Fin n) ℝ) * lanczosB A v₁ n *
      (hU.unit : Matrix (Fin n) (Fin n) ℝ)⁻¹ := by
    rw [IsUnit.unit_spec, hinv, ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1', Matrix.one_mul,
      Matrix.mul_assoc, h1', Matrix.mul_one]
  have hcp : (lanczosB A v₁ n).charpoly = A.charpoly := by
    conv_rhs => rw [hA']
    rw [charpoly_units_conj]
  refine ⟨hcp, fun lam => ?_⟩
  rw [← charpoly_isRoot_iff, ← charpoly_isRoot_iff, hcp]

/-! ### The characteristic polynomial 3.2.23 -/

/-- **The determinant of a tridiagonal matrix** (entries `f i j`, zero for `|i − j| ≥ 2`) obeys
the three-term recurrence `D_{k+2} = f_{k+1,k+1} D_{k+1} − f_{k+1,k} f_{k,k+1} D_k`, by expanding
along the last row and then the last column. -/
theorem det_tridiag {R : Type*} [CommRing R] (f : ℕ → ℕ → R)
    (hf : ∀ i j, i + 2 ≤ j ∨ j + 2 ≤ i → f i j = 0) (k : ℕ) :
    (Matrix.of fun i j : Fin (k + 2) => f i j).det =
      f (k + 1) (k + 1) * (Matrix.of fun i j : Fin (k + 1) => f i j).det -
        f (k + 1) k * f k (k + 1) * (Matrix.of fun i j : Fin k => f i j).det := by
  rw [det_succ_row _ (Fin.last (k + 1))]
  have hne : Fin.last (k + 1) ≠ (Fin.castSucc (Fin.last k)) := by simp [Fin.ext_iff]
  rw [Finset.sum_eq_add (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) hne]
  · -- the diagonal term
    have hsub1 : (Matrix.of fun i j : Fin (k + 2) => f i j).submatrix
        (Fin.last (k + 1)).succAbove (Fin.last (k + 1)).succAbove =
        Matrix.of fun i j : Fin (k + 1) => f i j := by
      ext i j; simp [Fin.succAbove_last]
    -- the off-diagonal term: its minor has last column `f · (k+1)`
    have hsub2 : (Matrix.of fun i j : Fin (k + 2) => f i j).submatrix
        (Fin.last (k + 1)).succAbove (Fin.castSucc (Fin.last k)).succAbove =
        Matrix.of fun i j : Fin (k + 1) => f i (if j.val < k then j.val else k + 1) := by
      ext i j
      simp only [submatrix_apply, Fin.succAbove_last, Matrix.of_apply, Fin.val_castSucc]
      rcases Fin.lt_or_le (Fin.castSucc j) (Fin.castSucc (Fin.last k)) with h | h
      · rw [Fin.succAbove_of_castSucc_lt _ _ h]
        have : j.val < k := by simpa [Fin.lt_def] using h
        simp [this]
      · rw [Fin.succAbove_of_le_castSucc _ _ h]
        have : ¬ j.val < k := by simp [Fin.le_def] at h; omega
        simp only [Fin.val_succ, this, ↓reduceIte]
        congr 1
        have := j.isLt
        omega
    have hminor : (Matrix.of fun i j : Fin (k + 1) =>
        f i (if j.val < k then j.val else k + 1)).det =
        f k (k + 1) * (Matrix.of fun i j : Fin k => f i j).det := by
      rw [det_succ_column _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
      · simp only [Matrix.of_apply, Fin.val_last, lt_irrefl, ↓reduceIte]
        rw [Even.neg_one_pow ⟨k, rfl⟩, one_mul]
        congr 1
        congr 1
        ext i j
        simp [Fin.succAbove_last, j.isLt]
      · intro i _ hi
        have hik : i.val < k := by
          have := i.isLt
          have : i.val ≠ k := fun h => hi (Fin.ext (by simp [h]))
          omega
        simp only [Matrix.of_apply, Fin.val_last, lt_irrefl, ↓reduceIte]
        rw [hf i (k + 1) (Or.inl (by omega)), mul_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
    rw [hsub1, hsub2, hminor]
    have e1 : (-1 : R) ^ (k + 1 + (k + 1)) = 1 := by
      rw [show k + 1 + (k + 1) = 2 * (k + 1) by ring, pow_mul]; simp
    have e2 : (-1 : R) ^ (k + 1 + k) = -1 := by
      rw [show k + 1 + k = 2 * k + 1 by ring, pow_succ, pow_mul]; simp
    rw [e1, e2]
    ring
  · intro j _ hj
    have hjk : j.val + 2 ≤ k + 1 := by
      have h1 : j ≠ Fin.last (k + 1) := hj.1
      have h2 : j ≠ Fin.castSucc (Fin.last k) := hj.2
      have := j.isLt
      have : j.val ≠ k + 1 := fun h => h1 (Fin.ext (by simp [h]))
      have : j.val ≠ k := fun h => h2 (Fin.ext (by simp [h]))
      omega
    simp only [Matrix.of_apply, Fin.val_last]
    rw [hf (k + 1) j (Or.inr hjk), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `p_k(λ) = det[λI − B_k]`, the characteristic polynomial of the leading `k × k` block. -/
noncomputable def lanczosP (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) (k : ℕ) : ℝ[X] :=
  (lanczosB A v₁ k).charpoly

theorem charmatrix_lanczosB (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) (k : ℕ) :
    charmatrix (lanczosB A v₁ k) = Matrix.of fun i j : Fin k =>
      ((if (i : ℕ) = j then X else 0) - C (lzBEntry (lzα A 1 1 v₁) (lzβ A 1 1 v₁) i j) : ℝ[X]) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [charmatrix_apply_eq, lanczosB]
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [charmatrix_apply_ne _ _ _ h, lanczosB, h']

/-- **DLMF 3.2.23**: `p_{k+1}(λ) = (λ − α_{k+1}) p_k(λ) − β_{k+1}² p_{k−1}(λ)`, `p₋₁ = 0`,
`p₀ = 1`; and `p_n` is the characteristic polynomial of `B` (hence of `A`, `dlmf_3_2_22`). -/
theorem dlmf_3_2_23 (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : Fin n → ℝ) :
    lanczosP A v₁ 0 = 1 ∧ lanczosP A v₁ 1 = X - C (lzα A 1 1 v₁ 1) ∧
      ∀ k, lanczosP A v₁ (k + 2) = (X - C (lzα A 1 1 v₁ (k + 2))) * lanczosP A v₁ (k + 1) -
        C (lzβ A 1 1 v₁ (k + 2) ^ 2) * lanczosP A v₁ k := by
  set g : ℕ → ℕ → ℝ[X] := fun i j =>
    (if i = j then X else 0) - C (lzBEntry (lzα A 1 1 v₁) (lzβ A 1 1 v₁) i j)
  have hp : ∀ k, lanczosP A v₁ k = (Matrix.of fun i j : Fin k => g i j).det := fun k => by
    rw [lanczosP, Matrix.charpoly, charmatrix_lanczosB]
  refine ⟨by simp [lanczosP], ?_, fun k => ?_⟩
  · rw [hp, Matrix.det_unique]
    simp [g, lzBEntry]
  · have hg : ∀ i j, i + 2 ≤ j ∨ j + 2 ≤ i → g i j = 0 := by
      intro i j h
      simp only [g, lzBEntry]
      simp [show ¬ i = j by omega, show ¬ j = i + 1 by omega, show ¬ i = j + 1 by omega]
    have hg1 : g (k + 1) (k + 1) = X - C (lzα A 1 1 v₁ (k + 2)) := by simp [g, lzBEntry]
    have hg2 : g (k + 1) k = -C (lzβ A 1 1 v₁ (k + 2)) := by
      simp [g, lzBEntry, show ¬ k = k + 1 + 1 by omega]
    have hg3 : g k (k + 1) = -C (lzβ A 1 1 v₁ (k + 2)) := by simp [g, lzBEntry]
    rw [hp (k + 2), det_tridiag g hg k, ← hp (k + 1), ← hp k, hg1, hg2, hg3, C_pow]
    ring

end Azurite.DLMF
