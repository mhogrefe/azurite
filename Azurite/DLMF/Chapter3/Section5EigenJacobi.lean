/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5EigenClassical
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# DLMF §3.5(vi): recurrence coefficients of the Jacobi and ultraspherical polynomials

3.5.33_1, 3.5.33_2, the Jacobi `h_0`, and Table 3.5.17_5 for `C_n^{(λ)}`.

* The subleading coefficient of the Rodrigues factors: `coeff_jacR_succ`, `jacR_sub`
  (`(a + b)[x^k]R_{k+1} = −(k + 1)(b − a)[x^{k+1}]R_{k+1}`), `coeff_jacMonic_sub`.
* 3.5.33_1: `dlmf_3_5_33_1_alpha` (`α_n = (β² − α²)/((2n + α + β)(2n + α + β + 2))` whenever
  `2n + α + β ≠ 0`), `dlmf_3_5_33_1_beta` (`n ≥ 2`, from the ratio of 3.5.26).
* 3.5.33_2 (the values at `n = 0, 1` "by continuity"): `dlmf_3_5_33_2_alpha`,
  `dlmf_3_5_33_2_beta`, and `dlmf_3_5_33_1_beta_one` (agreement with 3.5.33_1 when
  `α + β ≠ −1`).
* `h_0 = 2^{α+β+1}Γ(α+1)Γ(β+1)/Γ(α+β+2)` (`jacobi_h0`).
* Ultraspherical `C_n^{(λ)}` (`α = β = λ − ½`, weight `(1 − x²)^{λ−½}`, `jacW_ultra`; the monic
  `C_n^{(λ)}` is the monic Jacobi polynomial, 18.7.1): `α_n = 0`,
  `β_n = n(n + 2λ − 1)/(4(n + λ)(n + λ − 1))` (`λ ≠ 0`), `h_0 = √π Γ(λ + ½)/Γ(λ + 1)` (duplication
  formula) (`table_3_5_17_5_ultra_*`).
-/

open Polynomial Finset Set MeasureTheory Real

namespace Azurite.DLMF

/-! ### The subleading coefficient of `R_k` -/

theorem coeff_jacR_succ (a b : ℝ) (k j : ℕ) :
    (jacR a b (k + 1)).coeff (j + 1) = (b - a) * (jacR a b k).coeff (j + 1) -
      (a + b - 2 * k) * (jacR a b k).coeff j + (j + 2) * (jacR a b k).coeff (j + 2) -
        j * (jacR a b k).coeff j := by
  rw [jacR_succ_eq, coeff_sub, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul,
    coeff_derivative, coeff_X_pow_mul']
  rcases j with _ | j
  · simp; ring
  · simp only [show 2 ≤ j + 1 + 1 by omega, ↓reduceIte, show j + 1 + 1 - 2 = j by omega,
      coeff_derivative]
    push_cast
    ring

/-- `(a + b) [x^k] R_{k+1} = −(k + 1)(b − a) [x^{k+1}] R_{k+1}`. -/
theorem jacR_sub (a b : ℝ) (k : ℕ) :
    (a + b) * (jacR a b (k + 1)).coeff k =
      -((k + 1) * (b - a)) * (jacR a b (k + 1)).coeff (k + 1) := by
  induction k with
  | zero =>
    rw [(jacR_degree a b 1).2, coeff_zero_eq_eval_zero]
    simp [jacR]; ring
  | succ k ih =>
    rw [coeff_jacR_succ, (jacR_degree a b (k + 1 + 1)).2, prod_range_succ,
      ← (jacR_degree a b (k + 1)).2,
      coeff_eq_zero_of_natDegree_lt (by have := (jacR_degree a b (k + 1)).1; omega :
        (jacR a b (k + 1)).natDegree < k + 2)]
    push_cast
    linear_combination (-(a + b - k - 2)) * ih

/-! ### `α_n`: 3.5.33_1 and 3.5.33_2 -/

section Jacobi

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
include hα hβ

theorem coeff_jacMonic_sub (n : ℕ) :
    (jacMonic α β (n + 1)).coeff n = -((n + 1) * (β - α)) / (2 * (n + 1) + α + β) := by
  have hl := jacLead_ne_zero hα hβ (n + 1)
  have hab : (0 : ℝ) < 2 * (n + 1) + α + β := by
    have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have h := jacR_sub ((n + 1 : ℕ) + α) ((n + 1 : ℕ) + β) n
  rw [(jacR_degree _ _ (n + 1)).2] at h
  rw [jacMonic, coeff_C_mul]
  have e : (jacR ((n + 1 : ℕ) + α) ((n + 1 : ℕ) + β) (n + 1)).coeff n =
      -((n + 1) * (β - α)) * jacLead α β (n + 1) / (2 * (n + 1) + α + β) := by
    rw [eq_div_iff hab.ne']
    rw [jacLead]
    push_cast at h ⊢
    linear_combination h
  rw [e]
  field_simp

/-- **DLMF 3.5.33_2** (`α_0`): `α_0 = (β − α)/(α + β + 2)`. -/
theorem dlmf_3_5_33_2_alpha :
    recA (Ioo (-1) 1) (jacW α β) (jacMonic α β) 0 = (β - α) / (α + β + 2) := by
  rw [recA_eq_coeff (isGaussWeight_jacW hα hβ) (isOrthMonic_jacMonic hα hβ), coeff_X_mul_zero,
    coeff_jacMonic_sub hα hβ 0]
  push_cast
  ring_nf

/-- **DLMF 3.5.33_1** (`α_n`): `α_n = (β² − α²)/((2n + α + β)(2n + α + β + 2))` whenever
`2n + α + β ≠ 0` (always for `n ≥ 1`). -/
theorem dlmf_3_5_33_1_alpha (n : ℕ) (hn : 2 * (n : ℝ) + α + β ≠ 0) :
    recA (Ioo (-1) 1) (jacW α β) (jacMonic α β) n =
      (β ^ 2 - α ^ 2) / ((2 * n + α + β) * (2 * n + α + β + 2)) := by
  have h2 : (2 * (n : ℝ) + α + β + 2) ≠ 0 := by
    have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  cases n with
  | zero =>
    rw [dlmf_3_5_33_2_alpha hα hβ]
    simp only [Nat.cast_zero, mul_zero, zero_add] at hn h2 ⊢
    rw [div_eq_div_iff (by linarith) (mul_ne_zero hn h2)]
    ring
  | succ m =>
    rw [recA_eq_coeff (isGaussWeight_jacW hα hβ) (isOrthMonic_jacMonic hα hβ), coeff_X_mul,
      coeff_jacMonic_sub hα hβ m, coeff_jacMonic_sub hα hβ (m + 1)]
    push_cast at hn h2 ⊢
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have hB : 2 * ((m : ℝ) + 1) + α + β ≠ 0 := by linarith
    have hD : 2 * ((m : ℝ) + 1 + 1) + α + β ≠ 0 := by linarith
    rw [div_sub_div _ _ hB hD, div_eq_div_iff (mul_ne_zero hB hD) (mul_ne_zero hn h2)]
    ring

/-! ### `β_n` and `h_0` -/

/-- DLMF §3.5(vi): `h_0 = 2^{α+β+1} Γ(α+1)Γ(β+1)/Γ(α+β+2)`. -/
theorem jacobi_h0 :
    recB (Ioo (-1) 1) (jacW α β) (jacMonic α β) 0 =
      2 ^ (α + β + 1) * Gamma (α + 1) * Gamma (β + 1) / Gamma (α + β + 2) := by
  rw [recB_zero (isOrthMonic_jacMonic hα hβ), wInt_jacW]
  simp only [eval_one, one_mul, jacW]
  rw [integral_jac_beta hα hβ]
  ring

/-- **DLMF 3.5.33_1** (`β_n`, `n ≥ 2`):
`β_n = 4n(n+α)(n+β)(n+α+β)/((2n+α+β+1)(2n+α+β−1)(2n+α+β)²)`. -/
theorem dlmf_3_5_33_1_beta {n : ℕ} (hn : 2 ≤ n) :
    recB (Ioo (-1) 1) (jacW α β) (jacMonic α β) n =
      4 * n * (n + α) * (n + β) * (n + α + β) /
        ((2 * n + α + β + 1) * (2 * n + α + β - 1) * (2 * n + α + β) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 = m + 1 + 1 by ring, recB, dlmf_3_5_26 hα hβ (by omega),
    dlmf_3_5_26 hα hβ (by omega)]
  rw [Nat.factorial_succ (m + 1)]
  push_cast
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  generalize (m : ℝ) = s at hm ⊢
  have g1 : Gamma (s + 1 + 1 + α + 1) = (s + 1 + α + 1) * Gamma (s + 1 + α + 1) := by
    rw [show s + 1 + 1 + α + 1 = (s + 1 + α + 1) + 1 by ring, Gamma_add_one (by linarith)]
  have g2 : Gamma (s + 1 + 1 + β + 1) = (s + 1 + β + 1) * Gamma (s + 1 + β + 1) := by
    rw [show s + 1 + 1 + β + 1 = (s + 1 + β + 1) + 1 by ring, Gamma_add_one (by linarith)]
  have g3 : Gamma (s + 1 + 1 + α + β + 1) = (s + 1 + α + β + 1) * Gamma (s + 1 + α + β + 1) := by
    rw [show s + 1 + 1 + α + β + 1 = (s + 1 + α + β + 1) + 1 by ring, Gamma_add_one (by linarith)]
  have g4 : Gamma (2 * (s + 1 + 1) + α + β + 1) = (2 * (s + 1) + α + β + 2) *
      (2 * (s + 1) + α + β + 1) * Gamma (2 * (s + 1) + α + β + 1) := by
    rw [show 2 * (s + 1 + 1) + α + β + 1 = (2 * (s + 1) + α + β + 1 + 1) + 1 by ring,
      Gamma_add_one (by linarith), Gamma_add_one (by linarith)]
    ring
  have e2 : (2 : ℝ) ^ (2 * (s + 1 + 1) + α + β + 1) = 4 * 2 ^ (2 * (s + 1) + α + β + 1) := by
    rw [show 2 * (s + 1 + 1) + α + β + 1 = (2 * (s + 1) + α + β + 1) + 2 by ring,
      rpow_add two_pos, rpow_two]
    ring
  rw [g1, g2, g3, g4, e2]
  have p1 := Gamma_pos_of_pos (by linarith : 0 < s + 1 + α + 1)
  have p2 := Gamma_pos_of_pos (by linarith : 0 < s + 1 + β + 1)
  have p3 := Gamma_pos_of_pos (by linarith : 0 < s + 1 + α + β + 1)
  have p4 := Gamma_pos_of_pos (by linarith : 0 < 2 * (s + 1) + α + β + 1)
  have p5 : (0 : ℝ) < 2 ^ (2 * (s + 1) + α + β + 1) := rpow_pos_of_pos two_pos _
  have p6 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by positivity
  have q1 : 2 * (s + 1) + α + β + 1 ≠ 0 := by linarith
  have q2 : 2 * (s + 1 + 1) + α + β + 1 ≠ 0 := by linarith
  have q3 : 2 * (s + 1) + α + β + 2 ≠ 0 := by linarith
  have q4 : 2 * (s + 1 + 1) + α + β - 1 ≠ 0 := by linarith
  have q5 : 2 * (s + 1 + 1) + α + β ≠ 0 := by linarith
  have r1 := p1.ne'
  have r2 := p2.ne'
  have r3 := p3.ne'
  have r4 := p4.ne'
  have r5 := p5.ne'
  have r6 := p6.ne'
  rw [show 2 * (s + 1) + α + β + 2 = 2 * (s + 1 + 1) + α + β by ring,
    show 2 * (s + 1 + 1) + α + β - 1 = 2 * (s + 1) + α + β + 1 by ring]
  generalize Gamma (s + 1 + α + 1) = G1 at r1 ⊢
  generalize Gamma (s + 1 + β + 1) = G2 at r2 ⊢
  generalize Gamma (s + 1 + α + β + 1) = G3 at r3 ⊢
  generalize Gamma (2 * (s + 1) + α + β + 1) = G4 at r4 ⊢
  generalize (2 : ℝ) ^ (2 * (s + 1) + α + β + 1) = T at r5 ⊢
  generalize (((m + 1).factorial : ℕ) : ℝ) = F at r6 ⊢
  field_simp
  ring

/-- **DLMF 3.5.33_2** (`β_1`): `β_1 = 4(α + 1)(β + 1)/((α + β + 3)(α + β + 2)²)`. -/
theorem dlmf_3_5_33_2_beta :
    recB (Ioo (-1) 1) (jacW α β) (jacMonic α β) 1 =
      4 * (α + 1) * (β + 1) / ((α + β + 3) * (α + β + 2) ^ 2) := by
  have h0 := jacobi_h0 hα hβ
  rw [recB] at h0
  rw [recB, h0, dlmf_3_5_26 hα hβ le_rfl]
  push_cast
  have g1 : Gamma (1 + α + 1) = (α + 1) * Gamma (α + 1) := by
    rw [show 1 + α + 1 = (α + 1) + 1 by ring, Gamma_add_one (by linarith)]
  have g2 : Gamma (1 + β + 1) = (β + 1) * Gamma (β + 1) := by
    rw [show 1 + β + 1 = (β + 1) + 1 by ring, Gamma_add_one (by linarith)]
  have g3 : Gamma (2 * 1 + α + β + 1) = (α + β + 2) * Gamma (α + β + 2) := by
    rw [show 2 * 1 + α + β + 1 = (α + β + 2) + 1 by ring, Gamma_add_one (by linarith)]
  have e2 : (2 : ℝ) ^ (2 * 1 + α + β + 1) = 4 * 2 ^ (α + β + 1) := by
    rw [show 2 * 1 + α + β + 1 = (α + β + 1) + 2 by ring, rpow_add two_pos, rpow_two]; ring
  rw [g1, g2, g3, e2, show (1 : ℝ) + α + β + 1 = α + β + 2 by ring,
    show (2 : ℝ) * 1 + α + β + 1 = α + β + 3 by ring, Nat.factorial_one, Nat.cast_one]
  have p1 := Gamma_pos_of_pos (by linarith : 0 < α + 1)
  have p2 := Gamma_pos_of_pos (by linarith : 0 < β + 1)
  have p3 := Gamma_pos_of_pos (by linarith : 0 < α + β + 2)
  have p5 : (0 : ℝ) < 2 ^ (α + β + 1) := rpow_pos_of_pos two_pos _
  have q1 : α + β + 3 ≠ 0 := by linarith
  have q1' : 2 * 1 + α + β + 1 ≠ 0 := by linarith
  have q3 : α + β + 2 ≠ 0 := by linarith
  have q4 : α + 1 ≠ 0 := by linarith
  have q5 : β + 1 ≠ 0 := by linarith
  have r1 := p1.ne'
  have r2 := p2.ne'
  have r3 := p3.ne'
  have r5 := p5.ne'
  field_simp

/-- "By continuity": for `α + β ≠ −1` the 3.5.33_1 expression for `β_1` agrees with 3.5.33_2. -/
theorem dlmf_3_5_33_1_beta_one (h : α + β + 1 ≠ 0) :
    recB (Ioo (-1) 1) (jacW α β) (jacMonic α β) 1 =
      4 * 1 * (1 + α) * (1 + β) * (1 + α + β) /
        ((2 * 1 + α + β + 1) * (2 * 1 + α + β - 1) * (2 * 1 + α + β) ^ 2) := by
  rw [dlmf_3_5_33_2_beta hα hβ]
  have q1 : α + β + 3 ≠ 0 := by linarith
  have q3 : α + β + 2 ≠ 0 := by linarith
  rw [div_eq_div_iff (mul_ne_zero q1 (pow_ne_zero 2 q3)) (by
    rw [show 2 * 1 + α + β - 1 = α + β + 1 by ring]
    exact mul_ne_zero (mul_ne_zero (by linarith) h) (pow_ne_zero 2 (by linarith)))]
  ring

end Jacobi

/-! ### Ultraspherical (Gegenbauer) polynomials `C_n^{(λ)}`: `α = β = λ − ½` -/

section Ultraspherical

variable {l : ℝ} (hl : -1 / 2 < l)
include hl

omit hl in
/-- The ultraspherical weight `(1 − x²)^{λ−½}` is the Jacobi weight with `α = β = λ − ½`. -/
theorem jacW_ultra {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    jacW (l - 1 / 2) (l - 1 / 2) x = (1 - x ^ 2) ^ (l - 1 / 2) := by
  rw [jacW, ← mul_rpow (by linarith [hx.2]) (by linarith [hx.1])]
  congr 1; ring

theorem ultra_hab : -1 < l - 1 / 2 := by linarith

/-- Table 3.5.17_5, `C_n^{(λ)}`: `α_n = 0`. -/
theorem table_3_5_17_5_ultra_alpha (n : ℕ) :
    recA (Ioo (-1) 1) (jacW (l - 1 / 2) (l - 1 / 2)) (jacMonic (l - 1 / 2) (l - 1 / 2)) n = 0 := by
  cases n with
  | zero => rw [dlmf_3_5_33_2_alpha (ultra_hab hl) (ultra_hab hl)]; simp
  | succ m =>
    rw [dlmf_3_5_33_1_alpha (ultra_hab hl) (ultra_hab hl) (m + 1) (by
      have : (0 : ℝ) ≤ m := m.cast_nonneg; push_cast; linarith)]
    simp

/-- Table 3.5.17_5, `C_n^{(λ)}` (`λ ≠ 0`): `β_n = n(n + 2λ − 1)/(4(n + λ)(n + λ − 1))`. -/
theorem table_3_5_17_5_ultra_beta (hl0 : l ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    recB (Ioo (-1) 1) (jacW (l - 1 / 2) (l - 1 / 2)) (jacMonic (l - 1 / 2) (l - 1 / 2)) n =
      n * (n + 2 * l - 1) / (4 * (n + l) * (n + l - 1)) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    rw [dlmf_3_5_33_2_beta (ultra_hab hl) (ultra_hab hl)]
    have q1 : (1 : ℝ) + l ≠ 0 := by linarith
    have q2 : (2 : ℝ) * l + 1 ≠ 0 := by linarith
    have hl1 : (1 : ℝ) + l - 1 ≠ 0 := by rw [show (1 : ℝ) + l - 1 = l by ring]; exact hl0
    push_cast
    rw [div_eq_div_iff (by
      rw [show l - 1 / 2 + (l - 1 / 2) + 3 = 2 * (1 + l) by ring,
        show l - 1 / 2 + (l - 1 / 2) + 2 = 2 * l + 1 by ring]
      exact mul_ne_zero (mul_ne_zero two_ne_zero q1) (pow_ne_zero 2 q2))
      (mul_ne_zero (mul_ne_zero four_ne_zero q1) hl1)]
    ring
  · rw [dlmf_3_5_33_1_beta (ultra_hab hl) (ultra_hab hl) h2]
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have q1 : (n : ℝ) + l ≠ 0 := by linarith
    have q2 : (n : ℝ) + l - 1 ≠ 0 := by linarith
    have q3 : 2 * (n : ℝ) + (l - 1 / 2) + (l - 1 / 2) + 1 ≠ 0 := by linarith
    have q4 : 2 * (n : ℝ) + (l - 1 / 2) + (l - 1 / 2) - 1 ≠ 0 := by linarith
    have q5 : 2 * (n : ℝ) + (l - 1 / 2) + (l - 1 / 2) ≠ 0 := by linarith
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero q3 q4) (pow_ne_zero 2 q5))
      (mul_ne_zero (mul_ne_zero four_ne_zero q1) q2)]
    ring

/-- Table 3.5.17_5, `C_n^{(λ)}`: `h_0 = √π Γ(λ + ½)/Γ(λ + 1)`. -/
theorem table_3_5_17_5_ultra_h0 :
    recB (Ioo (-1) 1) (jacW (l - 1 / 2) (l - 1 / 2)) (jacMonic (l - 1 / 2) (l - 1 / 2)) 0 =
      √π * Gamma (l + 1 / 2) / Gamma (l + 1) := by
  rw [jacobi_h0 (ultra_hab hl) (ultra_hab hl)]
  have hs : 0 < l + 1 / 2 := by linarith
  have hd := Gamma_mul_Gamma_add_half (l + 1 / 2)
  rw [show l + 1 / 2 + 1 / 2 = l + 1 by ring, show 2 * (l + 1 / 2) = 2 * l + 1 by ring,
    show 1 - (2 * l + 1) = -(2 * l) by ring] at hd
  rw [show l - 1 / 2 + 1 = l + 1 / 2 by ring, show l - 1 / 2 + (l - 1 / 2) + 1 = 2 * l by ring,
    show l - 1 / 2 + (l - 1 / 2) + 2 = 2 * l + 1 by ring]
  have p1 := Gamma_pos_of_pos hs
  have p2 := Gamma_pos_of_pos (by linarith : 0 < l + 1)
  have p3 := Gamma_pos_of_pos (by linarith : 0 < 2 * l + 1)
  have e : (2 : ℝ) ^ (2 * l) * 2 ^ (-(2 * l)) = 1 := by
    rw [← rpow_add two_pos, add_neg_cancel, rpow_zero]
  rw [div_eq_div_iff p3.ne' p2.ne']
  linear_combination (Gamma (l + 1 / 2) * 2 ^ (2 * l)) * hd +
    (Gamma (2 * l + 1) * √π * Gamma (l + 1 / 2)) * e

end Ultraspherical

end Azurite.DLMF
