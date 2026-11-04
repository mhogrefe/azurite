/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Eigen
import Azurite.DLMF.Chapter3.Section5GaussHermite
import Azurite.DLMF.Chapter3.Section5GaussLaguerre

/-!
# DLMF §3.5(vi): recurrence coefficients of the classical orthogonal polynomials

Table 3.5.17_5 for the Legendre, Hermite and Laguerre polynomials, and 3.5.33_3.

* Tools: `recAB_of_rec` (any three-term recurrence of the monic family has the coefficients
  `α_n`, `β_n`) and `recA_eq_coeff` (`α_n = [xⁿ](x p_n) − [xⁿ] p_{n+1}`).
* Legendre (`P_n`): `α_n = 0`, `β_n = n²/(4n² − 1)`, `h_0 = 2`
  (`table_3_5_17_5_legendre_alpha`, `_beta`, `_h0`), from `legendreMonic_rec`.
* Hermite (`H_n`): `α_n = 0`, `β_n = n/2`, `h_0 = √π` (`table_3_5_17_5_hermite_*`), from
  `derivative_hermMonic_succ` and `hermMonic_rec`.
* Laguerre (`L_n^{(α)}`): `α_n = 2n + α + 1`, `β_n = n(n + α)`, `h_0 = Γ(α + 1)`
  (`table_3_5_17_5_laguerre_*`), `h_n = Γ(n + α + 1)/n!` for `L_n` (`wInt_lagL_sq`), the
  orthonormal version `q_n = (−1)ⁿ L_n/√h_n` (`table_3_5_17_5_laguerre_q`), and 3.5.33_3 for
  `L_n/√h_n` (`lagOrtho`, `dlmf_3_5_33_3`).
-/

open Polynomial Finset Set MeasureTheory Real

namespace Azurite.DLMF

variable {I : Set ℝ} {w : ℝ → ℝ} {P : ℕ → ℝ[X]}

/-! ### Identifying recurrence coefficients -/

section Tools

variable (hw : IsGaussWeight I w) (hP : ∀ n, IsOrthMonic I w n (P n))
include hw hP

omit hw in
theorem coeff_orth_P_self (n : ℕ) : (P n).coeff n = 1 := by
  have := (hP n).1.coeff_natDegree; rwa [(hP n).2.1] at this

/-- The recurrence coefficients in 3.5.30 are unique: any recurrence
`x p_n = p_{n+1} + a p_n + b p_{n−1}` has `a = α_n` and (`n ≥ 1`) `b = β_n`. -/
theorem recAB_of_rec {n : ℕ} {a b : ℝ}
    (h : X * P n = P (n + 1) + C a * P n + C b * prevP P n) :
    recA I w P n = a ∧ (1 ≤ n → recB I w P n = b) := by
  have h30 := dlmf_3_5_30 hw hP n
  have e : C (recA I w P n - a) * P n = C (b - recB I w P n) * prevP P n := by
    rw [C_sub, C_sub]; linear_combination h - h30
  have hc := congrArg (coeff · n) e
  simp only [coeff_C_mul] at hc
  rw [coeff_orth_P_self hP, coeff_eq_zero_of_degree_lt (degree_prevP_lt hP n), mul_zero, mul_one,
    sub_eq_zero] at hc
  refine ⟨hc, fun hn => ?_⟩
  rw [hc, sub_self, C_0, zero_mul] at e
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [prevP] at e
  rcases mul_eq_zero.mp e.symm with h0 | h0
  · rw [C_eq_zero, sub_eq_zero] at h0; exact h0.symm
  · exact absurd h0 (hP m).1.ne_zero

/-- `α_n` from the subleading coefficients: `α_n = [xⁿ](x p_n) − [xⁿ] p_{n+1}`. -/
theorem recA_eq_coeff (n : ℕ) :
    recA I w P n = (X * P n).coeff n - (P (n + 1)).coeff n := by
  have h := congrArg (coeff · n) (dlmf_3_5_30 hw hP n)
  simp only [coeff_add, coeff_C_mul] at h
  rw [coeff_orth_P_self hP, coeff_eq_zero_of_degree_lt (degree_prevP_lt hP n)] at h
  linarith

end Tools

/-! ### Legendre: `α_n = 0`, `β_n = n²/(4n² − 1)`, `h_0 = 2` -/

theorem legendreMonic_zero : legendreMonic 0 = 1 := by simp [legendreMonic, rodrigues]

theorem legendreMonic_one : legendreMonic 1 = X := by
  apply Polynomial.funext; intro x
  simp [legendreMonic, rodrigues]
  ring

theorem legendreMonic_rec (n : ℕ) :
    X * legendreMonic n = legendreMonic (n + 1) + C 0 * legendreMonic n +
      C ((n : ℝ) ^ 2 / (4 * n ^ 2 - 1)) * prevP legendreMonic n := by
  cases n with
  | zero => simp [prevP, legendreMonic_zero, legendreMonic_one]
  | succ k =>
    rw [legendreMonic_succ_succ k, prevP, C_0, zero_mul, add_zero]
    push_cast
    ring

/-- Table 3.5.17_5, Legendre: `α_n = 0`. -/
theorem table_3_5_17_5_legendre_alpha (n : ℕ) :
    recA (Ioo (-1) 1) (fun _ => 1) legendreMonic n = 0 :=
  (recAB_of_rec isGaussWeight_legendre isOrthMonic_legendreMonic (legendreMonic_rec n)).1

/-- Table 3.5.17_5, Legendre: `β_n = n²/(4n² − 1)`. -/
theorem table_3_5_17_5_legendre_beta {n : ℕ} (hn : 1 ≤ n) :
    recB (Ioo (-1) 1) (fun _ => 1) legendreMonic n = (n : ℝ) ^ 2 / (4 * n ^ 2 - 1) :=
  (recAB_of_rec isGaussWeight_legendre isOrthMonic_legendreMonic (legendreMonic_rec n)).2 hn

/-- Table 3.5.17_5, Legendre: `h_0 = 2`. -/
theorem table_3_5_17_5_legendre_h0 : recB (Ioo (-1) 1) (fun _ => 1) legendreMonic 0 = 2 := by
  rw [recB_zero isOrthMonic_legendreMonic, wInt_Ioo_one]
  simp; norm_num

/-! ### Hermite: `α_n = 0`, `β_n = n/2`, `h_0 = √π` -/

theorem derivative_hermMonic_succ (n : ℕ) :
    derivative (hermMonic (n + 1)) = C ((n : ℝ) + 1) * hermMonic n := by
  have h := congrArg derivative (hermMonic_eq (n + 1))
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_hermiteH_succ,
    ← hermMonic_eq n] at h
  have h2 : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  calc derivative (hermMonic (n + 1))
      = C ((2 : ℝ) ^ (n + 1))⁻¹ * (C ((2 : ℝ) ^ (n + 1)) * derivative (hermMonic (n + 1))) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ h2, C_1, one_mul]
    _ = C ((n : ℝ) + 1) * hermMonic n := by
        rw [h, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
        congr 2
        rw [pow_succ]; field_simp

theorem hermMonic_rec (n : ℕ) :
    X * hermMonic n = hermMonic (n + 1) + C 0 * hermMonic n +
      C ((n : ℝ) / 2) * prevP hermMonic n := by
  cases n with
  | zero => simp [prevP, hermMonic]
  | succ k =>
    rw [show hermMonic (k + 1 + 1) = X * hermMonic (k + 1) -
      C (1 / 2) * derivative (hermMonic (k + 1)) from rfl, derivative_hermMonic_succ, prevP,
      ← mul_assoc, ← C_mul, C_0, zero_mul, add_zero]
    push_cast
    ring_nf

/-- Table 3.5.17_5, Hermite: `α_n = 0`. -/
theorem table_3_5_17_5_hermite_alpha (n : ℕ) : recA univ hermW hermMonic n = 0 :=
  (recAB_of_rec isGaussWeight_hermW isOrthMonic_hermMonic (hermMonic_rec n)).1

/-- Table 3.5.17_5, Hermite: `β_n = n/2`. -/
theorem table_3_5_17_5_hermite_beta {n : ℕ} (hn : 1 ≤ n) :
    recB univ hermW hermMonic n = (n : ℝ) / 2 :=
  (recAB_of_rec isGaussWeight_hermW isOrthMonic_hermMonic (hermMonic_rec n)).2 hn

/-- Table 3.5.17_5, Hermite: `h_0 = √π`. -/
theorem table_3_5_17_5_hermite_h0 : recB univ hermW hermMonic 0 = √π := by
  rw [recB_zero isOrthMonic_hermMonic, wInt_hermW_one]

/-! ### Laguerre: `α_n = 2n + α + 1`, `β_n = n(n + α)`, `h_0 = Γ(α + 1)` -/

section Laguerre

variable {α : ℝ} (hα : -1 < α)
include hα

/-- Table 3.5.17_5, Laguerre: `α_n = 2n + α + 1`. -/
theorem table_3_5_17_5_laguerre_alpha (n : ℕ) :
    recA (Ioi 0) (lagW α) (lagMonic α) n = 2 * n + α + 1 := by
  rw [recA_eq_coeff (isGaussWeight_lagW hα) (isOrthMonic_lagMonic hα)]
  have hg : ∀ s : ℝ, 0 < s → Gamma (s + 1) / Gamma s = s := fun s hs => by
    rw [Gamma_add_one hs.ne']; field_simp [(Gamma_pos_of_pos hs).ne']
  cases n with
  | zero =>
    rw [coeff_X_mul_zero, coeff_lagMonic]
    simp only [show 0 ≤ 1 by omega, ↓reduceIte]
    rw [laguerreCoeff]
    have := hg (α + 1) (by linarith)
    simp only [Nat.cast_zero, Nat.cast_one, Nat.sub_zero, pow_one, Nat.choose_zero_right,
      zero_add] at this ⊢
    rw [show (1 : ℝ) + α + 1 = α + 1 + 1 by ring, this]
    ring
  | succ k =>
    rw [coeff_X_mul, coeff_lagMonic, coeff_lagMonic]
    simp only [show k ≤ k + 1 by omega, show k + 1 ≤ k + 1 + 1 by omega, ↓reduceIte]
    rw [laguerreCoeff, laguerreCoeff, show k + 1 - k = 1 by omega, Nat.choose_succ_self_right,
      show k + 1 + 1 - (k + 1) = 1 by omega, Nat.choose_succ_self_right]
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have e1 : Gamma ((k : ℝ) + 1 + α + 1) / Gamma ((k : ℝ) + α + 1) = k + α + 1 := by
      rw [show (k : ℝ) + 1 + α + 1 = (k + α + 1) + 1 by ring]; exact hg _ (by linarith)
    have e2 : Gamma ((k : ℝ) + 1 + 1 + α + 1) / Gamma ((k : ℝ) + 1 + α + 1) = k + 1 + α + 1 := by
      rw [show (k : ℝ) + 1 + 1 + α + 1 = (k + 1 + α + 1) + 1 by ring]; exact hg _ (by linarith)
    push_cast
    rw [e1, e2]
    ring

/-- Table 3.5.17_5, Laguerre: `β_n = n(n + α)`. -/
theorem table_3_5_17_5_laguerre_beta {n : ℕ} (hn : 1 ≤ n) :
    recB (Ioi 0) (lagW α) (lagMonic α) n = n * (n + α) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [recB, dlmf_3_5_27 hα, dlmf_3_5_27 hα, Nat.factorial_succ]
  have hs : (0 : ℝ) < k + α + 1 := by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
  have hG := (Gamma_pos_of_pos hs).ne'
  push_cast
  rw [show (k : ℝ) + 1 + α + 1 = k + α + 1 + 1 by ring, Gamma_add_one hs.ne']
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Table 3.5.17_5, Laguerre: `h_0 = Γ(α + 1)`. -/
theorem table_3_5_17_5_laguerre_h0 : recB (Ioi 0) (lagW α) (lagMonic α) 0 = Gamma (α + 1) := by
  rw [recB, dlmf_3_5_27 hα]; simp

/-- `h_n = ∫ (L_n^{(α)})² w = Γ(n + α + 1)/n!` (Table 18.3.1). -/
theorem wInt_lagL_sq (n : ℕ) :
    wInt (Ioi 0) (lagW α) (lagL α n * lagL α n) = Gamma (n + α + 1) / n.factorial := by
  have h := dlmf_3_5_27 hα n
  rw [gaussGamma, lagMonic_eq_lagL hα,
    show C ((-1 : ℝ) ^ n * n.factorial) * lagL α n * (C ((-1 : ℝ) ^ n * n.factorial) * lagL α n)
      = C ((-1 : ℝ) ^ n * n.factorial) * (C ((-1 : ℝ) ^ n * n.factorial) *
        (lagL α n * lagL α n)) by ring,
    wInt_C_mul, wInt_C_mul, ← mul_assoc] at h
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have e : ((-1 : ℝ) ^ n * n.factorial) * ((-1 : ℝ) ^ n * n.factorial) = (n.factorial : ℝ) ^ 2 := by
    rw [← sq, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]; norm_num
  rw [e] at h
  rw [eq_div_iff hf]
  apply mul_left_cancel₀ hf
  linear_combination h

/-- The orthonormal Laguerre polynomials `L_n^{(α)}/√h_n` of 3.5.33_3. -/
noncomputable def lagOrtho (α : ℝ) (n : ℕ) : ℝ[X] :=
  C (1 / √(Gamma (n + α + 1) / n.factorial)) * lagL α n

/-- Table 3.5.17_5, Laguerre: the orthonormal version is `q_n = (−1)ⁿ L_n^{(α)}/√h_n`. -/
theorem table_3_5_17_5_laguerre_q (n : ℕ) :
    orthoQ (Ioi 0) (lagW α) (lagMonic α) n = C ((-1) ^ n) * lagOrtho α n := by
  have hs : (0 : ℝ) < n + α + 1 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hG := Gamma_pos_of_pos hs
  have hf : (0 : ℝ) < n.factorial := by positivity
  rw [orthoQ, lagOrtho, dlmf_3_5_27 hα, lagMonic_eq_lagL hα, ← mul_assoc, ← mul_assoc, ← C_mul,
    ← C_mul]
  congr 2
  rw [Real.sqrt_mul hf.le, Real.sqrt_div hG.le]
  have h1 := Real.sqrt_pos.mpr hf
  have h2 := Real.sqrt_pos.mpr hG
  field_simp
  rw [Real.sq_sqrt hf.le]

/-- **DLMF 3.5.33_3**: for `q_n = L_n^{(α)}/√h_n`,
`x q_n = −√β_{n+1} q_{n+1} + α_n q_n − √β_n q_{n−1}` (`q_{−1} = 0`). -/
theorem dlmf_3_5_33_3 (n : ℕ) :
    X * lagOrtho α n = -(C √(recB (Ioi 0) (lagW α) (lagMonic α) (n + 1)) * lagOrtho α (n + 1)) +
      C (recA (Ioi 0) (lagW α) (lagMonic α) n) * lagOrtho α n -
        C √(recB (Ioi 0) (lagW α) (lagMonic α) n) * prevP (lagOrtho α) n := by
  have hq : ∀ m, lagOrtho α m = C ((-1) ^ m) * orthoQ (Ioi 0) (lagW α) (lagMonic α) m := fun m => by
    rw [table_3_5_17_5_laguerre_q hα, ← mul_assoc, ← C_mul, ← mul_pow]; norm_num
  have h := dlmf_3_5_30_5 (isGaussWeight_lagW hα) (isOrthMonic_lagMonic hα) n
  rw [hq n, hq (n + 1), mul_left_comm, h]
  cases n with
  | zero => simp [prevP]
  | succ k =>
    simp only [prevP, hq k, pow_succ, C_mul, C_neg, C_1]
    ring

end Laguerre

end Azurite.DLMF
