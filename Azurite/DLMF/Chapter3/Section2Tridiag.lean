/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter3.Section2

/-!
# DLMF §3.2(ii): Gaussian elimination for a tridiagonal matrix

* **3.2.7** (`tridiag`, `triEntry`): `b_j` on the diagonal, `c_j` above, `a_j` below. The
  sequences are indexed from `1` as in the DLMF.
* The general elimination of §3.2(i) (`AzMatrix.gaussSteps`) changes one row per step on a
  tridiagonal matrix. After `k` steps rows `≤ k` are rows of `U` and the rest are untouched
  (`gaussSteps_tridiag`, `triG`). This holds with no assumption on the pivots.
* **3.2.8–3.2.10**: hence `L` (`luL`) is unit lower bidiagonal with `ℓ_j = a_j/d_{j−1}`
  (`dlmf_3_2_8`), and `U` (`luU`) is upper bidiagonal with `d_j` and `u_j = c_j` (`dlmf_3_2_9`).
  Here `d₁ = b₁` and `d_j = b_j − ℓ_j c_{j−1}` (`triD`, `triL`, `dlmf_3_2_10`).
  * `A = LU` when `d₁, …, d_{n−1} ≠ 0` (`tridiag_LU`).
* **3.2.11–3.2.12**: forward elimination `y₁ = f₁`, `y_j = f_j − ℓ_j y_{j−1}` (`triY`,
  `dlmf_3_2_11`), then back substitution `x_n = y_n/d_n`, `x_j = (y_j − u_j x_{j+1})/d_j`
  (`triX`, `dlmf_3_2_12`).
  * They solve `Ax = f` when `d₁, …, d_n ≠ 0` (`tridiag_solve`, via `Ly = f`, `Ux = y` and the
    bidiagonal row sums `sum_lower_bidiag`, `sum_upper_bidiag`).
-/

namespace Azurite.DLMF

open Azurite

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The matrix 3.2.7 and the recurrences 3.2.10 -/

/-- The entries of 3.2.7 (rows and columns from `0`, the sequences indexed from `1` as in the
DLMF): `b_i` on the diagonal, `c_i` above it, `a_i` below it. -/
def triEntry (a b c : ℕ → K) (i j : ℕ) : K :=
  if j = i then b (i + 1) else if j = i + 1 then c (i + 1) else if j + 1 = i then a (i + 1) else 0

/-- **DLMF 3.2.7**: the tridiagonal matrix. -/
def tridiag (a b c : ℕ → K) : AzMatrix K n n := AzMatrix.ofFn fun i j => triEntry a b c i j

/-- The pivots `d_j` of 3.2.9–3.2.10: `d₁ = b₁`, `d_j = b_j − (a_j/d_{j−1}) c_{j−1}`. -/
def triD (a b c : ℕ → K) : ℕ → K
  | 0 => 0
  | 1 => b 1
  | j + 2 => b (j + 2) - a (j + 2) / triD a b c (j + 1) * c (j + 1)

/-- The multipliers `ℓ_j = a_j/d_{j−1}` of 3.2.8. -/
def triL (a b c : ℕ → K) (j : ℕ) : K := a j / triD a b c (j - 1)

/-- **DLMF 3.2.10**: `ℓ_j = a_j/d_{j−1}`, `d_j = b_j − ℓ_j c_{j−1}`, `j = 2, …, n`
(and `d₁ = b₁`). -/
theorem dlmf_3_2_10 (a b c : ℕ → K) {j : ℕ} (hj : 2 ≤ j) :
    triL a b c j = a j / triD a b c (j - 1) ∧
      triD a b c j = b j - triL a b c j * c (j - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  exact ⟨rfl, rfl⟩

/-- The matrix after `k` elimination steps: rows `≤ k` are rows of `U` (`d_{i+1}`, `c_{i+1}`),
the others are still those of `A`. -/
def triG (a b c : ℕ → K) (k i j : ℕ) : K :=
  if i ≤ k then (if j = i then triD a b c (i + 1) else if j = i + 1 then c (i + 1) else 0)
  else triEntry a b c i j

/-- **The elimination on a tridiagonal matrix** touches only one row per step. -/
theorem gaussSteps_tridiag (a b c : ℕ → K) :
    ∀ k : ℕ, ∀ i j : Fin n,
      ((tridiag a b c : AzMatrix K n n).gaussSteps k).toFn i j = triG a b c k i j := by
  intro k
  induction k with
  | zero =>
    intro i j
    rw [AzMatrix.gaussSteps_zero, tridiag, AzMatrix.toFn_ofFn]
    unfold triG triEntry
    rcases Nat.eq_zero_or_pos i.val with h | h
    · rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ 2 ≤ j.val) with hj | hj | hj
      · simp [h, hj, triD]
      · simp [h, hj]
      · simp [h, show ¬ j.val = 0 by omega, show ¬ j.val = 1 by omega]
    · simp only [show ¬ i.val ≤ 0 by omega, ↓reduceIte]
  | succ k ih =>
    intro i j
    by_cases hk : k < n
    · rw [AzMatrix.gaussSteps_succ _ _ hk, AzMatrix.toFn_eliminateBelow]
      simp only [ih]
      unfold triG triEntry
      by_cases hi : i.val ≤ k
      · simp only [hi, ↓reduceIte, show i.val ≤ k + 1 by omega]
      · simp only [hi, ↓reduceIte]
        rcases lt_trichotomy j.val k with hj | hj | hj
        · simp only [hj, ↓reduceIte]
          split_ifs <;> first | rfl | omega
        · have hjk : j = ⟨k, hk⟩ := Fin.ext hj
          simp only [hjk, lt_irrefl, ↓reduceIte]
          split_ifs <;> first | rfl | omega
        · have hjk : j ≠ ⟨k, hk⟩ := fun h => by rw [h] at hj; exact lt_irrefl _ hj
          simp only [show ¬ j.val < k by omega, hjk, ↓reduceIte, le_refl]
          by_cases hik : i.val = k + 1
          · simp only [hik, le_refl, ↓reduceIte, show ¬ k = k + 1 + 1 by omega,
              show ¬ k = k + 1 by omega]
            rcases (by omega : j.val = k + 1 ∨ j.val = k + 2 ∨ k + 2 < j.val) with h | h | h
            · simp only [h, ↓reduceIte, show ¬ k + 1 = k by omega, triD]
            · simp only [h, ↓reduceIte, show ¬ k + 2 = k + 1 by omega, add_assoc]
              norm_num
            · simp only [show ¬ j.val = k + 1 by omega, show ¬ j.val = k + 1 + 1 by omega,
                show ¬ j.val + 1 = k + 1 by omega, show ¬ j.val = k by omega, ↓reduceIte,
                mul_zero, sub_zero]
          · simp only [show ¬ i.val ≤ k + 1 by omega, ↓reduceIte,
              show ¬ k = i.val by omega, show ¬ k = i.val + 1 by omega,
              show ¬ k + 1 = i.val by omega, zero_div, zero_mul, sub_zero]
    · rw [AzMatrix.gaussSteps_of_ge _ _ hk, ih]
      unfold triG
      simp only [show i.val ≤ k by omega, show i.val ≤ k + 1 by omega, ↓reduceIte]

/-- **DLMF 3.2.9**: `U` is upper bidiagonal, with `d_j` on the diagonal and `u_j = c_j` above. -/
theorem dlmf_3_2_9 (a b c : ℕ → K) :
    luU (tridiag a b c : AzMatrix K n n) = AzMatrix.ofFn fun i j =>
      if j.val = i.val then triD a b c (i.val + 1)
      else if j.val = i.val + 1 then c (i.val + 1) else 0 := by
  apply AzMatrix.toFn_injective
  funext i j
  rw [luU, gaussSteps_tridiag, AzMatrix.toFn_ofFn, triG]
  simp only [show i.val ≤ n by omega, ↓reduceIte]

/-- **DLMF 3.2.8**: `L` is unit lower bidiagonal, with `ℓ_j` below the diagonal. -/
theorem dlmf_3_2_8 (a b c : ℕ → K) :
    luL (tridiag a b c : AzMatrix K n n) = AzMatrix.ofFn fun i k =>
      if k = i then 1 else if k.val + 1 = i.val then triL a b c (i.val + 1) else 0 := by
  apply AzMatrix.toFn_injective
  funext i k
  rw [luL, AzMatrix.toFn_ofFn, AzMatrix.toFn_ofFn]
  by_cases hki : k.val < i.val
  · have hne : k ≠ i := fun h => by rw [h] at hki; exact lt_irrefl _ hki
    simp only [hki, hne, ↓reduceIte, luMult, gaussSteps_tridiag, triG, le_refl,
      show ¬ i.val ≤ k.val by omega, triEntry, show ¬ k.val = i.val by omega,
      show ¬ k.val = i.val + 1 by omega]
    by_cases h1 : k.val + 1 = i.val
    · simp only [h1, ↓reduceIte, triL, show i.val + 1 - 1 = k.val + 1 by omega]
    · simp [h1]
  · by_cases h : k = i
    · simp [h]
    · simp [hki, h, show ¬ k.val + 1 = i.val by omega]

/-- **3.2.5 for the tridiagonal matrix**: `A = LU` when `d₁, …, d_{n−1} ≠ 0`. -/
theorem tridiag_LU (a b c : ℕ → K) (hd : ∀ j : ℕ, 1 ≤ j → j < n → triD a b c j ≠ 0) :
    luL (tridiag a b c : AzMatrix K n n) * luU (tridiag a b c) = tridiag a b c := by
  refine dlmf_3_2_5 _ fun k hk => ?_
  rw [gaussSteps_tridiag, triG]
  simp only [le_refl, ↓reduceIte]
  exact hd (k + 1) (by omega) hk

/-! ### Forward elimination 3.2.11 and back substitution 3.2.12 -/

/-- **DLMF 3.2.11**: `y₁ = f₁`, `y_j = f_j − ℓ_j y_{j−1}`. -/
def triY (a b c f : ℕ → K) : ℕ → K
  | 0 => 0
  | 1 => f 1
  | j + 2 => f (j + 2) - triL a b c (j + 2) * triY a b c f (j + 1)

/-- Back substitution from `x_n` downwards: `triXrev m = x_{n−m}`. -/
def triXrev (a b c f : ℕ → K) (n : ℕ) : ℕ → K
  | 0 => triY a b c f n / triD a b c n
  | m + 1 => (triY a b c f (n - (m + 1)) - c (n - (m + 1)) * triXrev a b c f n m) /
      triD a b c (n - (m + 1))

/-- The solution `x_j` of 3.2.12. -/
def triX (a b c f : ℕ → K) (n j : ℕ) : K := triXrev a b c f n (n - j)

theorem dlmf_3_2_11 (a b c f : ℕ → K) {j : ℕ} (hj : 2 ≤ j) :
    triY a b c f j = f j - triL a b c j * triY a b c f (j - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  rfl

/-- **DLMF 3.2.12**: `x_n = y_n/d_n` and `x_j = (y_j − u_j x_{j+1})/d_j`, `j = n − 1, …, 1`. -/
theorem dlmf_3_2_12 (a b c f : ℕ → K) (n : ℕ) :
    triX a b c f n n = triY a b c f n / triD a b c n ∧
      ∀ j : ℕ, j < n → triX a b c f n j =
        (triY a b c f j - c j * triX a b c f n (j + 1)) / triD a b c j := by
  refine ⟨by simp [triX, triXrev], fun j hj => ?_⟩
  unfold triX
  rw [show n - j = (n - (j + 1)) + 1 by omega, triXrev, show n - (n - (j + 1) + 1) = j by omega]

theorem sum_lower_bidiag (i : Fin n) (α β : K) (v : Fin n → K) :
    ∑ j : Fin n, (if j = i then α else if j.val + 1 = i.val then β else 0) * v j =
      α * v i + if h : 0 < i.val then β * v ⟨i.val - 1, by omega⟩ else 0 := by
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · rw [Finset.sum_eq_single i]
    · simp [h0]
    · intro j _ hj; simp [hj, h0]
    · intro h; exact absurd (Finset.mem_univ _) h
  · set i' : Fin n := ⟨i.val - 1, by omega⟩
    have hne : i ≠ i' := fun h => by
      have := congrArg Fin.val h; simp [i'] at this; omega
    rw [Finset.sum_eq_add i i' hne]
    · have h1 : i' ≠ i := fun h => hne h.symm
      have h2 : i'.val + 1 = i.val := by simp [i']; omega
      simp [h1, h2, hpos, i']
    · intro j _ hj
      have hj1 : j ≠ i := hj.1
      have hj2 : ¬ j.val + 1 = i.val := fun h => hj.2 (Fin.ext (by simp [i']; omega))
      simp [hj1, hj2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_upper_bidiag (i : Fin n) (α β : K) (v : Fin n → K) :
    ∑ j : Fin n, (if j.val = i.val then α else if j.val = i.val + 1 then β else 0) * v j =
      α * v i + if h : i.val + 1 < n then β * v ⟨i.val + 1, h⟩ else 0 := by
  by_cases hn : i.val + 1 < n
  · set i' : Fin n := ⟨i.val + 1, hn⟩
    have hne : i ≠ i' := fun h => by
      have := congrArg Fin.val h; simp [i'] at this
    rw [Finset.sum_eq_add i i' hne]
    · simp [hn, i']
    · intro j _ hj
      have hj1 : ¬ j.val = i.val := fun h => hj.1 (Fin.ext h)
      have hj2 : ¬ j.val = i.val + 1 := fun h => hj.2 (Fin.ext (by simp [i']; omega))
      simp [hj1, hj2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single i]
    · simp [hn]
    · intro j _ hj
      have hj1 : ¬ j.val = i.val := fun h => hj (Fin.ext h)
      have hj2 : ¬ j.val = i.val + 1 := by omega
      simp [hj1, hj2]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **Solving `Ax = f`** by 3.2.11–3.2.12: when `d₁, …, d_n ≠ 0`, the vector `(x_1, …, x_n)`
solves the tridiagonal system. -/
theorem tridiag_solve (a b c f : ℕ → K) (hd : ∀ j : ℕ, 1 ≤ j → j ≤ n → triD a b c j ≠ 0) :
    (tridiag a b c : AzMatrix K n n).mulVec (AzVector.ofFn fun i => triX a b c f n (i.val + 1)) =
      AzVector.ofFn fun i => f (i.val + 1) := by
  have hLU := tridiag_LU (n := n) a b c fun j h1 h2 => hd j h1 h2.le
  have hU : (luU (tridiag a b c : AzMatrix K n n)).mulVec
      (AzVector.ofFn fun i => triX a b c f n (i.val + 1)) =
        AzVector.ofFn fun i => triY a b c f (i.val + 1) := by
    apply AzVector.toFn_injective
    funext i
    rw [AzMatrix.toFn_mulVec, dlmf_3_2_9, dotProduct, AzVector.toFn_ofFn]
    simp only [AzMatrix.toFn_ofFn]
    rw [sum_upper_bidiag i _ _ (AzVector.ofFn fun i => triX a b c f n (i.val + 1)).toFn]
    simp only [AzVector.toFn_ofFn]
    have hdi := hd (i.val + 1) (by omega) i.isLt
    split_ifs with h
    · rw [(dlmf_3_2_12 a b c f n).2 (i.val + 1) h]
      field_simp
      ring
    · have hin : i.val + 1 = n := by omega
      rw [hin, (dlmf_3_2_12 a b c f n).1]
      rw [hin] at hdi
      field_simp
      simp
  have hL : (luL (tridiag a b c : AzMatrix K n n)).mulVec
      (AzVector.ofFn fun i => triY a b c f (i.val + 1)) = AzVector.ofFn fun i => f (i.val + 1) := by
    apply AzVector.toFn_injective
    funext i
    rw [AzMatrix.toFn_mulVec, dlmf_3_2_8, dotProduct, AzVector.toFn_ofFn]
    simp only [AzMatrix.toFn_ofFn]
    rw [sum_lower_bidiag i _ _ (AzVector.ofFn fun i => triY a b c f (i.val + 1)).toFn]
    simp only [AzVector.toFn_ofFn, one_mul]
    split_ifs with h
    · rw [dlmf_3_2_11 a b c f (by omega : 2 ≤ i.val + 1),
        show i.val + 1 - 1 = i.val - 1 + 1 by omega]
      ring
    · rw [show i.val = 0 by omega]; simp [triY]
  calc (tridiag a b c : AzMatrix K n n).mulVec (AzVector.ofFn fun i => triX a b c f n (i.val + 1))
      = (luL (tridiag a b c) * luU (tridiag a b c)).mulVec
          (AzVector.ofFn fun i => triX a b c f n (i.val + 1)) := by rw [hLU]
    _ = _ := by rw [mulVec_mul, hU, hL]

end Azurite.DLMF
