/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5GaussLegendre

/-!
# DLMF §3.5(vi): eigenvalue/eigenvector characterization of Gauss quadrature formulas

For any Gauss weight `w` on `I` and its monic orthogonal polynomials `p_n` (`IsOrthMonic` for
all `n`):

* 3.5.30: `dlmf_3_5_30`, `x p_n = p_{n+1} + α_n p_n + β_n p_{n−1}` with `α_n = ∫ x p_n² w/h_n`
  (`recA`), `β_n = h_n/h_{n−1}` (`recB`, `β_0 = h_0 = ∫ w`, `recB_zero`), `β_n > 0`
  (`recB_pos`), `p_{−1} = 0`, `p_0 = 1` (`prevP`, `orth_P_zero`); proved by orthogonality
  (`eq_zero_of_wInt_mul_P`).
* `h_n = h_0 β_1 ⋯ β_n` (`gaussGamma_eq_prod`) and 3.5.33, `γ_n = β_0 β_1 ⋯ β_n`
  (`dlmf_3_5_33`).
* 3.5.30_5: the orthonormal polynomials `q_n = p_n/√h_n` (`orthoQ`, `orthoQ_zero`),
  `dlmf_3_5_30_5`.
* 3.5.31: the symmetric tridiagonal Jacobi matrix `J_n` (`jacEntry`, `jacobiMatrix`,
  `jacobiMatrix_isSymm`); its eigenvalues are exactly the Gauss nodes (`dlmf_3_5_31`,
  `dlmf_3_5_31_hasEigenvalue`), with eigenvector `(q_0(x), …, q_{n−1}(x))`
  (`jacobiMatrix_mulVec_qvec`), and every eigenvector a multiple of it (`eigvec_eq_smul_qvec`).
* 3.5.32: `w_k = β_0 v_{k,1}²` for a normalized eigenvector (`dlmf_3_5_32`), via the Christoffel
  sum `christoffel_mul_sum`.
-/

open Polynomial Finset Set
open scoped Matrix

namespace Azurite.DLMF

variable {I : Set ℝ} {w : ℝ → ℝ} {P : ℕ → ℝ[X]}

/-! ### The recurrence coefficients -/

/-- `p_{n−1}`, with `p_{−1} = 0`. -/
noncomputable def prevP (P : ℕ → ℝ[X]) : ℕ → ℝ[X]
  | 0 => 0
  | n + 1 => P n

/-- The recurrence coefficient `α_n = ∫ x p_n² w / h_n`. -/
noncomputable def recA (I : Set ℝ) (w : ℝ → ℝ) (P : ℕ → ℝ[X]) (n : ℕ) : ℝ :=
  wInt I w (X * P n * P n) / gaussGamma I w (P n)

/-- The recurrence coefficient `β_n = h_n/h_{n−1}` (`n ≥ 1`), and `β_0 = h_0 = ∫ w`. -/
noncomputable def recB (I : Set ℝ) (w : ℝ → ℝ) (P : ℕ → ℝ[X]) : ℕ → ℝ
  | 0 => gaussGamma I w (P 0)
  | n + 1 => gaussGamma I w (P (n + 1)) / gaussGamma I w (P n)

theorem degree_C_mul_le' (a : ℝ) (p : ℝ[X]) : (C a * p).degree ≤ p.degree := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [degree_C_mul ha]

section General

variable (hw : IsGaussWeight I w) (hP : ∀ n, IsOrthMonic I w n (P n))
include hw hP

theorem gaussGamma_pos_of_orth (n : ℕ) : 0 < gaussGamma I w (P n) :=
  wInt_mul_self_pos hw (hP n).1.ne_zero

theorem recB_pos (n : ℕ) : 0 < recB I w P n := by
  cases n with
  | zero => exact gaussGamma_pos_of_orth hw hP 0
  | succ n => exact div_pos (gaussGamma_pos_of_orth hw hP _) (gaussGamma_pos_of_orth hw hP _)

omit hw in
theorem orth_P_zero : P 0 = 1 := by
  obtain ⟨hm, hd, -⟩ := hP 0
  have h1 := hm.coeff_natDegree
  rw [hd] at h1
  rw [eq_C_of_natDegree_eq_zero hd, h1, map_one]

omit hw in
theorem degree_orth_P (n : ℕ) : (P n).degree = n := by
  rw [degree_eq_natDegree (hP n).1.ne_zero, (hP n).2.1]

omit hw in
/-- `β_0 = ∫ w`. -/
theorem recB_zero : recB I w P 0 = wInt I w 1 := by
  rw [recB, gaussGamma, orth_P_zero hP, mul_one]

/-- A polynomial of degree `≤ n` orthogonal to `p_0, …, p_n` vanishes. -/
theorem eq_zero_of_wInt_mul_P {n : ℕ} {s : ℝ[X]} (hs : s.degree < ((n + 1 : ℕ) : WithBot ℕ))
    (h : ∀ j ≤ n, wInt I w (s * P j) = 0) : s = 0 := by
  have key : ∀ d, ∀ q : ℝ[X], q.natDegree = d → d ≤ n → wInt I w (s * q) = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro q hq hdn
      by_cases hq0 : q = 0
      · simp [hq0, wInt_zero]
      set r := q - C q.leadingCoeff * P d with hr_def
      have hPd := hP d
      have hr : r = 0 ∨ r.natDegree < d := by
        by_cases hr0 : r = 0
        · exact Or.inl hr0
        right
        have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
        have hdeg : (C q.leadingCoeff * P d).degree = q.degree := by
          rw [degree_C_mul hlc, degree_orth_P hP, degree_eq_natDegree hq0, hq]
        have hlc2 : (C q.leadingCoeff * P d).leadingCoeff = q.leadingCoeff := by
          rw [leadingCoeff_mul, leadingCoeff_C, hPd.1.leadingCoeff, mul_one]
        have hlt := degree_sub_lt_left hdeg.symm hq0 hlc2.symm
        rw [degree_eq_natDegree hq0, hq] at hlt
        exact (natDegree_lt_iff_degree_lt hr0).mpr hlt
      have hqr : q = C q.leadingCoeff * P d + r := by rw [hr_def]; ring
      rw [hqr, mul_add, wInt_add hw, mul_left_comm, wInt_C_mul, h d hdn, mul_zero, zero_add]
      rcases hr with hr | hr
      · rw [hr, mul_zero, wInt_zero]
      · exact ih _ hr r rfl (by omega)
  by_contra hs0
  have hsn : s.natDegree ≤ n := by
    have := (natDegree_lt_iff_degree_lt hs0).mpr hs; omega
  have := wInt_mul_self_pos hw hs0
  rw [key _ s rfl hsn] at this
  exact lt_irrefl _ this

omit hw in
theorem degree_X_mul_P_sub_lt (n : ℕ) :
    (X * P n - P (n + 1)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
  have hX : (X * P n).Monic := monic_X.mul (hP n).1
  have hd : (X * P n).degree = (P (n + 1)).degree := by
    rw [degree_eq_natDegree hX.ne_zero, natDegree_mul X_ne_zero (hP n).1.ne_zero, natDegree_X,
      (hP n).2.1, degree_orth_P hP, add_comm]
  have := degree_sub_lt_left hd hX.ne_zero (by rw [hX.leadingCoeff, (hP (n + 1)).1.leadingCoeff])
  rwa [hd, degree_orth_P hP] at this

theorem wInt_X_mul_P_mul_P_succ (n : ℕ) :
    wInt I w (X * P n * P (n + 1)) = gaussGamma I w (P (n + 1)) := by
  rw [show X * P n * P (n + 1) = P (n + 1) * P (n + 1) + P (n + 1) * (X * P n - P (n + 1)) by
      ring, wInt_add hw, (hP (n + 1)).wInt_mul_eq_zero (degree_X_mul_P_sub_lt hP n), add_zero,
    gaussGamma]

omit hw in
theorem wInt_P_mul_P_of_lt {m j : ℕ} (hj : j < m) : wInt I w (P m * P j) = 0 :=
  (hP m).wInt_mul_eq_zero (by rw [degree_orth_P hP]; exact_mod_cast hj)

omit hw in
theorem degree_prevP_lt (n : ℕ) : (prevP P n).degree < n := by
  cases n with
  | zero => simp [prevP]
  | succ n => rw [prevP, degree_orth_P hP]; exact_mod_cast Nat.lt_succ_self n

/-- **DLMF 3.5.30**: `x p_n = p_{n+1} + α_n p_n + β_n p_{n−1}` (`p_{−1} = 0`), with `β_n > 0`
(`recB_pos`). -/
theorem dlmf_3_5_30 (n : ℕ) :
    X * P n = P (n + 1) + C (recA I w P n) * P n + C (recB I w P n) * prevP P n := by
  set α := recA I w P n
  set β := recB I w P n
  set s := X * P n - P (n + 1) - C α * P n - C β * prevP P n
  have hγ := gaussGamma_pos_of_orth hw hP n
  have hs : s.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have h1 := degree_X_mul_P_sub_lt hP n
    have h2 : (C α * P n).degree < ((n + 1 : ℕ) : WithBot ℕ) :=
      (degree_C_mul_le' _ _).trans_lt (by rw [degree_orth_P hP]; exact_mod_cast n.lt_succ_self)
    have h3 : (C β * prevP P n).degree < ((n + 1 : ℕ) : WithBot ℕ) :=
      (degree_C_mul_le' _ _).trans_lt ((degree_prevP_lt hP n).trans (by exact_mod_cast
        n.lt_succ_self))
    exact (degree_sub_le _ _).trans_lt (max_lt ((degree_sub_le _ _).trans_lt (max_lt h1 h2)) h3)
  suffices s = 0 by
    rw [show s = X * P n - (P (n + 1) + C α * P n + C β * prevP P n) by ring] at this
    exact sub_eq_zero.mp this
  refine eq_zero_of_wInt_mul_P hw hP hs fun j hj => ?_
  have e : s * P j = X * P n * P j - P (n + 1) * P j - C α * (P n * P j) -
      C β * (prevP P n * P j) := by ring
  rw [e, wInt_sub hw, wInt_sub hw, wInt_sub hw, wInt_C_mul, wInt_C_mul,
    wInt_P_mul_P_of_lt hP (by omega : j < n + 1)]
  rcases Nat.lt_or_ge j n with hjn | hjn
  · -- `j < n`, so `n = m + 1`
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [wInt_P_mul_P_of_lt hP hjn, prevP]
    rcases Nat.lt_or_ge j m with hjm | hjm
    · rw [show X * P (m + 1) * P j = P (m + 1) * (X * P j) by ring,
        (hP (m + 1)).wInt_mul_eq_zero (by
          rw [degree_mul, degree_X, degree_orth_P hP]
          exact_mod_cast (by omega : 1 + j < m + 1)),
        wInt_P_mul_P_of_lt hP hjm]
      ring
    · obtain rfl : j = m := by omega
      rw [show X * P (j + 1) * P j = X * P j * P (j + 1) by ring,
        wInt_X_mul_P_mul_P_succ hw hP, ← gaussGamma]
      have hγj := gaussGamma_pos_of_orth hw hP j
      simp only [β, recB]
      field_simp
      ring
  · obtain rfl : j = n := by omega
    rw [show prevP P j * P j = P j * prevP P j by ring,
      (hP j).wInt_mul_eq_zero (degree_prevP_lt hP j), ← gaussGamma]
    simp only [α, recA]
    field_simp
    ring

/-- `h_n = h_0 β_1 β_2 ⋯ β_n`. -/
theorem gaussGamma_eq_prod (n : ℕ) :
    gaussGamma I w (P n) = gaussGamma I w (P 0) * ∏ i ∈ range n, recB I w P (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih, recB]
    have := gaussGamma_pos_of_orth hw hP n
    field_simp

/-- **DLMF 3.5.33**: the error constant `γ_n = β_0 β_1 ⋯ β_n`. -/
theorem dlmf_3_5_33 (n : ℕ) :
    gaussGamma I w (P n) = ∏ i ∈ range (n + 1), recB I w P i := by
  rw [prod_range_succ', gaussGamma_eq_prod hw hP n, mul_comm]
  rfl

/-! ### The orthonormal polynomials, 3.5.30_5 -/

/-- The orthonormal polynomials `q_n = p_n/√h_n`. -/
noncomputable def orthoQ (I : Set ℝ) (w : ℝ → ℝ) (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  C (1 / √(gaussGamma I w (P n))) * P n

omit hw in
/-- `q_0 = 1/√h_0`. -/
theorem orthoQ_zero : orthoQ I w P 0 = C (1 / √(recB I w P 0)) := by
  simp only [orthoQ, recB]
  rw [orth_P_zero hP, mul_one]

/-- **DLMF 3.5.30_5**: `x q_n = √β_{n+1} q_{n+1} + α_n q_n + √β_n q_{n−1}` (`q_{−1} = 0`). -/
theorem dlmf_3_5_30_5 (n : ℕ) :
    X * orthoQ I w P n = C √(recB I w P (n + 1)) * orthoQ I w P (n + 1) +
      C (recA I w P n) * orthoQ I w P n + C √(recB I w P n) * prevP (orthoQ I w P) n := by
  have h := congrArg (C (1 / √(gaussGamma I w (P n))) * ·) (dlmf_3_5_30 hw hP n)
  have g0 := gaussGamma_pos_of_orth hw hP n
  have g1 := gaussGamma_pos_of_orth hw hP (n + 1)
  have s0 := Real.sqrt_pos.mpr g0
  have s1 := Real.sqrt_pos.mpr g1
  have e1 : √(recB I w P (n + 1)) * (1 / √(gaussGamma I w (P (n + 1)))) =
      1 / √(gaussGamma I w (P n)) := by
    rw [recB, Real.sqrt_div g1.le]; field_simp
  have e2 : C (1 / √(gaussGamma I w (P n))) * (C (recB I w P n) * prevP P n) =
      C √(recB I w P n) * prevP (orthoQ I w P) n := by
    cases n with
    | zero => simp [prevP]
    | succ m =>
      have g2 := gaussGamma_pos_of_orth hw hP m
      have s2 := Real.sqrt_pos.mpr g2
      simp only [prevP, orthoQ, recB, ← mul_assoc, ← C_mul]
      congr 2
      rw [Real.sqrt_div g0.le]
      field_simp
      rw [Real.sq_sqrt g0.le, Real.sq_sqrt g2.le]
  rw [← e2]
  simp only [orthoQ]
  rw [← mul_assoc (C √(recB I w P (n + 1))), ← C_mul, e1,
    show X * (C (1 / √(gaussGamma I w (P n))) * P n) =
      C (1 / √(gaussGamma I w (P n))) * (X * P n) by ring, h]
  ring

/-! ### The Jacobi matrix, 3.5.31 -/

/-- The entries of the Jacobi matrix (3.5.31): `α_i` on the diagonal, `√β_{max(i,j)}` on the two
adjacent diagonals, `0` elsewhere. -/
noncomputable def jacEntry (I : Set ℝ) (w : ℝ → ℝ) (P : ℕ → ℝ[X]) (i j : ℕ) : ℝ :=
  (if i = j then recA I w P i else 0) + (if i + 1 = j then √(recB I w P j) else 0) +
    (if j + 1 = i then √(recB I w P i) else 0)

/-- The `n × n` (symmetric tridiagonal) Jacobi matrix `J_n` (3.5.31). -/
noncomputable def jacobiMatrix (I : Set ℝ) (w : ℝ → ℝ) (P : ℕ → ℝ[X]) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => jacEntry I w P i j

omit hw hP in
theorem jacobiMatrix_isSymm (n : ℕ) : (jacobiMatrix I w P n).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, jacobiMatrix, jacEntry]
  by_cases h : (i : ℕ) = j
  · obtain rfl := Fin.ext h; rfl
  · by_cases h1 : (i : ℕ) + 1 = j
    · simp [h1, h, show (j : ℕ) ≠ i by omega, show ¬ (j : ℕ) + 1 = i by omega]
    · by_cases h2 : (j : ℕ) + 1 = i
      · simp [h2, h, show (j : ℕ) ≠ i by omega, show ¬ (i : ℕ) + 1 = j by omega]
      · simp [h, h1, h2, show (j : ℕ) ≠ i by omega]

/-- The extension of `v : Fin n → ℝ` by zero. -/
noncomputable def vext {n : ℕ} (v : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then v ⟨i, h⟩ else 0

/-- `f(i − 1)`, with `f(−1) = 0`. -/
noncomputable def vprev (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => f k

omit hw hP in
theorem jacobiMatrix_mulVec {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (jacobiMatrix I w P n *ᵥ v) i = recA I w P i * vext v i +
      √(recB I w P (i + 1)) * vext v (i + 1) + √(recB I w P i) * vprev (vext v) i := by
  have hv : ∀ j : Fin n, v j = vext v j := fun j => by simp [vext, j.2]
  simp only [Matrix.mulVec, dotProduct, jacobiMatrix, hv]
  rw [Fin.sum_univ_eq_sum_range (fun j => jacEntry I w P i j * vext v j)]
  simp only [jacEntry, add_mul, sum_add_distrib, ite_mul, zero_mul]
  rw [sum_ite_eq _ _ (fun j => recA I w P i * vext v j), sum_ite_eq _ _
    (fun j => √(recB I w P j) * vext v j)]
  simp only [mem_range.mpr i.2, ↓reduceIte]
  congr 1
  · congr 1
    split_ifs with h
    · rfl
    · simp [vext, show ¬ (i : ℕ) + 1 < n from fun h' => h (mem_range.mpr h')]
  · rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · rw [h0]
      simp [vprev]
    · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨i - 1, by omega⟩
      rw [hk, vprev]
      rw [sum_eq_single_of_mem k (mem_range.mpr (by omega)) (fun j _ hj => by simp [hj])]
      simp

/-- The vector `(q_0(x), q_1(x), …)`. -/
noncomputable def qvec (I : Set ℝ) (w : ℝ → ℝ) (P : ℕ → ℝ[X]) (x : ℝ) (i : ℕ) : ℝ :=
  (orthoQ I w P i).eval x

theorem qvec_rec (x : ℝ) (i : ℕ) :
    x * qvec I w P x i = √(recB I w P (i + 1)) * qvec I w P x (i + 1) +
      recA I w P i * qvec I w P x i + √(recB I w P i) * vprev (qvec I w P x) i := by
  have h := congrArg (eval x) (dlmf_3_5_30_5 hw hP i)
  simp only [eval_mul, eval_add, eval_C, eval_X] at h
  rw [qvec, h]
  cases i with
  | zero => simp [prevP, vprev, qvec]
  | succ k => simp [prevP, vprev, qvec]

/-- The eigenvector `(q_0(x), …, q_{n−1}(x))`: `J_n q = x q − √β_n q_n(x) e_n`. -/
theorem jacobiMatrix_mulVec_qvec {n : ℕ} (x : ℝ) (i : Fin n) :
    (jacobiMatrix I w P n *ᵥ fun j : Fin n => qvec I w P x j) i =
      x * qvec I w P x i -
        if (i : ℕ) + 1 = n then √(recB I w P n) * qvec I w P x n else 0 := by
  rw [jacobiMatrix_mulVec, qvec_rec hw hP x i]
  have h1 : vext (fun j : Fin n => qvec I w P x j) i = qvec I w P x i := by simp [vext, i.2]
  have h2 : vprev (vext fun j : Fin n => qvec I w P x j) i = vprev (qvec I w P x) i := by
    obtain ⟨i, hi⟩ := i
    rcases i with _ | k
    · rfl
    · simp only [vprev, vext, show k < n by omega, ↓reduceDIte]
  rw [h1, h2]
  by_cases hi : (i : ℕ) + 1 = n
  · simp only [hi, ↓reduceIte, vext, lt_self_iff_false, ↓reduceDIte, mul_zero, add_zero]
    ring
  · simp only [hi, ↓reduceIte, vext, show (i : ℕ) + 1 < n by omega, ↓reduceDIte]; ring

/-- An eigenvector of `J_n` for the eigenvalue `x` is a multiple of `(q_0(x), …, q_{n−1}(x))`. -/
theorem eigvec_eq_smul_qvec {n : ℕ} {x : ℝ} {v : Fin n → ℝ}
    (hv : jacobiMatrix I w P n *ᵥ v = x • v) :
    ∀ i < n, vext v i = vext v 0 * √(recB I w P 0) * qvec I w P x i := by
  have h0 := recB_pos hw hP 0
  set c := vext v 0 * √(recB I w P 0)
  have hq0 : qvec I w P x 0 = 1 / √(recB I w P 0) := by
    rw [qvec, orthoQ_zero hP, eval_C]
  have hrow : ∀ i (hi : i < n), recA I w P i * vext v i + √(recB I w P (i + 1)) * vext v (i + 1) +
      √(recB I w P i) * vprev (vext v) i = x * vext v i := fun i hi => by
    have := congrFun hv ⟨i, hi⟩
    rw [jacobiMatrix_mulVec] at this
    rw [this]; simp [vext, hi]
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | k
    · rw [hq0]; simp only [c]; field_simp [(Real.sqrt_pos.mpr h0).ne']
    · have hk := hrow k (by omega)
      have hq := qvec_rec hw hP x k
      have ek := ih k (by omega) (by omega)
      have ep : vprev (vext v) k = c * vprev (qvec I w P x) k := by
        rcases k with _ | j
        · simp [vprev]
        · simp only [vprev]; exact ih j (by omega) (by omega)
      have hb := Real.sqrt_pos.mpr (recB_pos hw hP (k + 1))
      rw [ek, ep] at hk
      have : √(recB I w P (k + 1)) * (vext v (k + 1) - c * qvec I w P x (k + 1)) = 0 := by
        linear_combination hk + c * hq
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hb.ne'
      · linarith

/-- **DLMF 3.5.31**: the eigenvalues of the Jacobi matrix `J_n` are exactly the Gauss nodes, the
zeros of `p_n`. -/
theorem dlmf_3_5_31 {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    (∃ v : Fin n → ℝ, v ≠ 0 ∧ jacobiMatrix I w P n *ᵥ v = x • v) ↔ (P n).IsRoot x := by
  have h0 := recB_pos hw hP 0
  have hs0 := Real.sqrt_pos.mpr h0
  have hγn := gaussGamma_pos_of_orth hw hP n
  have hqn : qvec I w P x n = 0 ↔ (P n).IsRoot x := by
    rw [qvec, orthoQ, eval_mul, eval_C, IsRoot.def, mul_eq_zero, or_iff_right]
    exact div_ne_zero one_ne_zero (Real.sqrt_pos.mpr hγn).ne'
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hprop := eigvec_eq_smul_qvec hw hP hv
    set c := vext v 0 * √(recB I w P 0)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hc : c ≠ 0 := by
      intro hc
      apply hv0
      ext ⟨i, hi⟩
      have := hprop i hi
      rw [hc, zero_mul] at this
      simpa [vext, hi] using this
    have hm := congrFun hv ⟨m, by omega⟩
    rw [jacobiMatrix_mulVec] at hm
    have hq := qvec_rec hw hP x m
    have em := hprop m (by omega)
    have ep : vprev (vext v) m = c * vprev (qvec I w P x) m := by
      rcases m with _ | j
      · simp [vprev]
      · simp only [vprev]; exact hprop j (by omega)
    have hlast : vext v (m + 1) = 0 := by simp [vext]
    simp only [Pi.smul_apply, smul_eq_mul] at hm
    rw [show v ⟨m, by omega⟩ = vext v m by simp [vext]] at hm
    rw [em, ep, hlast] at hm
    have hb := Real.sqrt_pos.mpr (recB_pos hw hP (m + 1))
    have : c * √(recB I w P (m + 1)) * qvec I w P x (m + 1) = 0 := by
      linear_combination -hm - c * hq
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hc
      · exact absurd h hb.ne'
    · exact hqn.mp h
  · intro hx
    refine ⟨fun j => qvec I w P x j, fun h => ?_, ?_⟩
    · have := congrFun h ⟨0, hn⟩
      simp only [Pi.zero_apply] at this
      rw [qvec, orthoQ_zero hP, eval_C] at this
      exact (div_ne_zero one_ne_zero hs0.ne') this
    · ext i
      rw [jacobiMatrix_mulVec_qvec hw hP, hqn.mpr hx]
      simp

/-- **DLMF 3.5.31** (as eigenvalues of the linear map): the Gauss nodes are the eigenvalues of
`J_n`. -/
theorem dlmf_3_5_31_hasEigenvalue {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (jacobiMatrix I w P n)) x ↔ (P n).IsRoot x := by
  rw [← dlmf_3_5_31 hw hP hn]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, by simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.mp hv.1⟩
  · rintro ⟨v, hv0, hv⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by simpa [Matrix.toLin'_apply] using hv), hv0⟩

/-- **DLMF 3.5.32**: if `v_k` is a normalized eigenvector of `J_n` for the eigenvalue `x_k`, then
`w_k = β_0 v_{k,1}²`. -/
theorem dlmf_3_5_32 {n : ℕ} (hn : 1 ≤ n) {xk : ℝ} (hk : xk ∈ (P n).roots.toFinset)
    {v : Fin n → ℝ} (hv : jacobiMatrix I w P n *ᵥ v = xk • v) (hnorm : ∑ i, v i ^ 2 = 1) :
    christoffel I w (P n) xk = recB I w P 0 * v ⟨0, hn⟩ ^ 2 := by
  have h0 := recB_pos hw hP 0
  have hs0 := Real.sqrt_pos.mpr h0
  have hprop := eigvec_eq_smul_qvec hw hP hv
  set c := vext v 0 * √(recB I w P 0)
  have hsum := christoffel_mul_sum hw hP n hk
  have hq2 : ∀ j, (P j).eval xk ^ 2 / gaussGamma I w (P j) = qvec I w P xk j ^ 2 := fun j => by
    have := gaussGamma_pos_of_orth hw hP j
    rw [qvec, orthoQ, eval_mul, eval_C, mul_pow, div_pow, Real.sq_sqrt this.le]
    ring
  simp only [hq2] at hsum
  have hnorm' : c ^ 2 * ∑ j ∈ range n, qvec I w P xk j ^ 2 = 1 := by
    rw [← hnorm, mul_sum, ← Fin.sum_univ_eq_sum_range (fun j => c ^ 2 * qvec I w P xk j ^ 2)]
    refine sum_congr rfl fun i _ => ?_
    have := hprop i i.2
    simp only [vext, i.2, dite_true] at this
    rw [this]; ring
  have hv0 : v ⟨0, hn⟩ = c / √(recB I w P 0) := by
    rw [show c / √(recB I w P 0) = vext v 0 by simp only [c]; field_simp]
    simp [vext, show 0 < n by omega]
  have hS : ∑ j ∈ range n, qvec I w P xk j ^ 2 ≠ 0 := by
    intro h; rw [h, mul_zero] at hnorm'; exact zero_ne_one hnorm'
  have hc : christoffel I w (P n) xk = c ^ 2 := mul_right_cancel₀ hS (hsum.trans hnorm'.symm)
  rw [hc, hv0, div_pow, Real.sq_sqrt h0.le]
  field_simp

end General

end Azurite.DLMF
