/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5EigenClassical
import Azurite.DLMF.Chapter3.Section5GaussChebyshev

/-!
# DLMF §3.5(vi): recurrence coefficients of the Chebyshev polynomials

Table 3.5.17_5 for the Chebyshev polynomials `T_n`, `U_n`, `V_n`, `W_n` and the shifted `T_n^*`.

* Recurrences of the monic polynomials (`gcT_rec`, `gcU_rec`, `gcV_rec`, `gcW_rec`, from
  Mathlib's `Chebyshev.T_add_two`, `Chebyshev.U_add_two`) and
  `table_3_5_17_5_{T,U,V,W}_{alpha,beta,h0}`: `α_n = 0, 0, ½δ_{n,0}, −½δ_{n,0}`,
  `β_n = ¼(1 + δ_{n,1}), ¼, ¼, ¼`, `h_0 = π, π/2, π, π`.
* The affine shift `x ↦ 2x − 1` from `(0, 1)` to `(−1, 1)`: `shLin`, `shW`, `shP`, `wInt_shW`,
  `isGaussWeight_shW`, `isOrthMonic_shP`, `shP_rec`, `recAB_shP` (`α_n^* = (α_n + 1)/2`,
  `β_n^* = β_n/4`), `recB_shP_zero` (`h_0^* = h_0`).
* `T_n^*(x) = T_n(2x − 1)` with weight `(x − x²)^{−1/2}` (`shW_chebWeight_one`, `shP_gcT`):
  `α_n = ½`, `β_n = (1/16)(1 + δ_{n,1})`, `h_0 = π` (`table_3_5_17_5_Tstar_*`).
-/

open Polynomial Finset Set MeasureTheory Real

namespace Azurite.DLMF

/-! ### Chebyshev recurrences -/

theorem cheb_T_nat (k : ℕ) :
    Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ) =
      2 * X * Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ) - Chebyshev.T ℝ (k : ℤ) := by
  push_cast; exact Chebyshev.T_add_two ℝ (k : ℤ)

theorem cheb_U_int (j : ℤ) (x : ℝ) :
    (Chebyshev.U ℝ (j + 2)).eval x =
      2 * x * (Chebyshev.U ℝ (j + 1)).eval x - (Chebyshev.U ℝ j).eval x := by
  rw [Chebyshev.U_add_two]; simp

theorem gcT_rec (n : ℕ) :
    X * gcT n = gcT (n + 1) + C 0 * gcT n +
      C (if n = 1 then 1 / 2 else 1 / 4) * prevP gcT n := by
  apply Polynomial.funext; intro x
  rcases n with _ | _ | k
  · simp [gcT, prevP, Chebyshev.T_zero, Chebyshev.T_one]
  · simp [gcT, prevP, Chebyshev.T_two, Chebyshev.T_one, Chebyshev.T_zero]; ring
  · have h := congrArg (eval x) (cheb_T_nat (k + 1))
    simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at h
    simp only [gcT, prevP, eval_mul, eval_add, eval_C, eval_X, show k + 1 + 1 ≠ 1 by omega,
      ↓reduceIte, Nat.add_sub_cancel, zero_mul, add_zero]
    rw [show k + 1 + 1 + 1 = k + 1 + 2 by ring, h]
    push_cast
    field_simp
    ring

theorem gcU_rec (n : ℕ) :
    X * gcU n = gcU (n + 1) + C 0 * gcU n + C (1 / 4) * prevP gcU n := by
  apply Polynomial.funext; intro x
  rcases n with _ | k
  · simp [gcU, prevP, Chebyshev.U_zero, Chebyshev.U_one]
  · have h := cheb_U_int (k : ℤ) x
    simp only [gcU, prevP, eval_mul, eval_add, eval_C, eval_X, zero_mul, add_zero]
    push_cast
    rw [show (k : ℤ) + 1 + 1 = k + 2 by ring, h]
    field_simp
    ring

theorem gcV_rec (n : ℕ) :
    X * gcV n = gcV (n + 1) + C (if n = 0 then 1 / 2 else 0) * gcV n +
      C (1 / 4) * prevP gcV n := by
  apply Polynomial.funext; intro x
  rcases n with _ | k
  · simp [gcV, prevP, Chebyshev.U_zero, Chebyshev.U_one, Chebyshev.U_neg_one]; ring
  · have h1 := cheb_U_int (k : ℤ) x
    have h2 := cheb_U_int ((k : ℤ) - 1) x
    rw [show (k : ℤ) - 1 + 2 = k + 1 by ring, show (k : ℤ) - 1 + 1 = k by ring] at h2
    simp only [gcV, prevP, eval_mul, eval_add, eval_sub, eval_C, eval_X, show k + 1 ≠ 0 by omega,
      ↓reduceIte, zero_mul, add_zero]
    push_cast
    rw [show (k : ℤ) + 1 + 1 - 1 = k + 1 by ring, show (k : ℤ) + 1 - 1 = k by ring,
      show (k : ℤ) + 1 + 1 = k + 2 by ring, h1, h2]
    field_simp
    ring

theorem gcW_rec (n : ℕ) :
    X * gcW n = gcW (n + 1) + C (if n = 0 then -1 / 2 else 0) * gcW n +
      C (1 / 4) * prevP gcW n := by
  apply Polynomial.funext; intro x
  rcases n with _ | k
  · simp [gcW, prevP, Chebyshev.U_zero, Chebyshev.U_one, Chebyshev.U_neg_one]; ring
  · have h1 := cheb_U_int (k : ℤ) x
    have h2 := cheb_U_int ((k : ℤ) - 1) x
    rw [show (k : ℤ) - 1 + 2 = k + 1 by ring, show (k : ℤ) - 1 + 1 = k by ring] at h2
    simp only [gcW, prevP, eval_mul, eval_add, eval_C, eval_X, show k + 1 ≠ 0 by omega,
      ↓reduceIte, zero_mul, add_zero]
    push_cast
    rw [show (k : ℤ) + 1 + 1 - 1 = k + 1 by ring, show (k : ℤ) + 1 - 1 = k by ring,
      show (k : ℤ) + 1 + 1 = k + 2 by ring, h1, h2]
    field_simp
    ring

/-! ### Table 3.5.17_5 for `T_n`, `U_n`, `V_n`, `W_n` -/

theorem isGaussWeight_cheb1 : IsGaussWeight (Ioo (-1) 1) (chebWeight 1) :=
  isGaussWeight_chebWeight fun _ _ => by simp

theorem isGaussWeight_chebU : IsGaussWeight (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) :=
  isGaussWeight_chebWeight fun x hx => by
    simp only [eval_sub, eval_one, eval_pow, eval_X]; nlinarith [hx.1, hx.2]

theorem isGaussWeight_chebV : IsGaussWeight (Ioo (-1) 1) (chebWeight (1 + X)) :=
  isGaussWeight_chebWeight fun x hx => by simp only [eval_add, eval_one, eval_X]; linarith [hx.1]

theorem isGaussWeight_chebW : IsGaussWeight (Ioo (-1) 1) (chebWeight (1 - X)) :=
  isGaussWeight_chebWeight fun x hx => by simp only [eval_sub, eval_one, eval_X]; linarith [hx.2]

/-- Table 3.5.17_5, `T_n`: `α_n = 0`. -/
theorem table_3_5_17_5_T_alpha (n : ℕ) : recA (Ioo (-1) 1) (chebWeight 1) gcT n = 0 :=
  (recAB_of_rec isGaussWeight_cheb1 isOrthMonic_gcT (gcT_rec n)).1

/-- Table 3.5.17_5, `T_n`: `β_n = ¼(1 + δ_{n,1})`. -/
theorem table_3_5_17_5_T_beta {n : ℕ} (hn : 1 ≤ n) :
    recB (Ioo (-1) 1) (chebWeight 1) gcT n = 1 / 4 * (1 + if n = 1 then 1 else 0) := by
  rw [(recAB_of_rec isGaussWeight_cheb1 isOrthMonic_gcT (gcT_rec n)).2 hn]
  split_ifs <;> norm_num

/-- Table 3.5.17_5, `T_n`: `h_0 = π`. -/
theorem table_3_5_17_5_T_h0 : recB (Ioo (-1) 1) (chebWeight 1) gcT 0 = π := by
  rw [recB_zero isOrthMonic_gcT, wInt_chebWeight]; simp

/-- Table 3.5.17_5, `U_n`: `α_n = 0`. -/
theorem table_3_5_17_5_U_alpha (n : ℕ) : recA (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) gcU n = 0 :=
  (recAB_of_rec isGaussWeight_chebU isOrthMonic_gcU (gcU_rec n)).1

/-- Table 3.5.17_5, `U_n`: `β_n = ¼`. -/
theorem table_3_5_17_5_U_beta {n : ℕ} (hn : 1 ≤ n) :
    recB (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) gcU n = 1 / 4 :=
  (recAB_of_rec isGaussWeight_chebU isOrthMonic_gcU (gcU_rec n)).2 hn

/-- Table 3.5.17_5, `U_n`: `h_0 = π/2`. -/
theorem table_3_5_17_5_U_h0 : recB (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) gcU 0 = π / 2 := by
  rw [recB_zero isOrthMonic_gcU, wInt_chebWeight]
  simp only [one_mul, eval_sub, eval_one, eval_pow, eval_X]
  rw [intervalIntegral.integral_sub (f := fun _ => (1 : ℝ)) (g := fun θ => cos θ ^ 2)
    intervalIntegrable_const ((continuous_cos.pow 2).intervalIntegrable _ _), integral_cos_sq]
  simp; ring

/-- Table 3.5.17_5, `V_n`: `α_n = ½δ_{n,0}`. -/
theorem table_3_5_17_5_V_alpha (n : ℕ) :
    recA (Ioo (-1) 1) (chebWeight (1 + X)) gcV n = if n = 0 then 1 / 2 else 0 :=
  (recAB_of_rec isGaussWeight_chebV isOrthMonic_gcV (gcV_rec n)).1

/-- Table 3.5.17_5, `V_n`: `β_n = ¼`. -/
theorem table_3_5_17_5_V_beta {n : ℕ} (hn : 1 ≤ n) :
    recB (Ioo (-1) 1) (chebWeight (1 + X)) gcV n = 1 / 4 :=
  (recAB_of_rec isGaussWeight_chebV isOrthMonic_gcV (gcV_rec n)).2 hn

/-- Table 3.5.17_5, `V_n`: `h_0 = π`. -/
theorem table_3_5_17_5_V_h0 : recB (Ioo (-1) 1) (chebWeight (1 + X)) gcV 0 = π := by
  rw [recB_zero isOrthMonic_gcV, wInt_chebWeight]
  simp only [one_mul, eval_add, eval_one, eval_X]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (continuous_cos.intervalIntegrable _ _), integral_cos]
  simp

/-- Table 3.5.17_5, `W_n`: `α_n = −½δ_{n,0}`. -/
theorem table_3_5_17_5_W_alpha (n : ℕ) :
    recA (Ioo (-1) 1) (chebWeight (1 - X)) gcW n = if n = 0 then -1 / 2 else 0 :=
  (recAB_of_rec isGaussWeight_chebW isOrthMonic_gcW (gcW_rec n)).1

/-- Table 3.5.17_5, `W_n`: `β_n = ¼`. -/
theorem table_3_5_17_5_W_beta {n : ℕ} (hn : 1 ≤ n) :
    recB (Ioo (-1) 1) (chebWeight (1 - X)) gcW n = 1 / 4 :=
  (recAB_of_rec isGaussWeight_chebW isOrthMonic_gcW (gcW_rec n)).2 hn

/-- Table 3.5.17_5, `W_n`: `h_0 = π`. -/
theorem table_3_5_17_5_W_h0 : recB (Ioo (-1) 1) (chebWeight (1 - X)) gcW 0 = π := by
  rw [recB_zero isOrthMonic_gcW, wInt_chebWeight]
  simp only [one_mul, eval_sub, eval_one, eval_X]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (continuous_cos.intervalIntegrable _ _), integral_cos]
  simp

/-! ### The shift `x ↦ 2x − 1` from `(0, 1)` to `(−1, 1)` -/

/-- The linear map `2x − 1`. -/
noncomputable def shLin : ℝ[X] := C 2 * X + C (-1)

theorem eval_shLin (x : ℝ) : shLin.eval x = 2 * x - 1 := by simp [shLin]; ring

theorem natDegree_shLin : shLin.natDegree = 1 := natDegree_linear two_ne_zero

theorem leadingCoeff_shLin : shLin.leadingCoeff = 2 := leadingCoeff_linear two_ne_zero

/-- The shifted weight `2 w(2x − 1)` on `(0, 1)`. -/
noncomputable def shW (w : ℝ → ℝ) (x : ℝ) : ℝ := 2 * w (2 * x - 1)

/-- The shifted monic polynomials `2⁻ⁿ p_n(2x − 1)`. -/
noncomputable def shP (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] := C ((2 : ℝ) ^ n)⁻¹ * (P n).comp shLin

theorem wInt_Ioo_interval {a b : ℝ} (hab : a ≤ b) (w : ℝ → ℝ) (p : ℝ[X]) :
    wInt (Ioo a b) w p = ∫ x in a..b, p.eval x * w x := by
  rw [wInt, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem wInt_shW (w : ℝ → ℝ) (p : ℝ[X]) :
    wInt (Ioo 0 1) (shW w) (p.comp shLin) = wInt (Ioo (-1) 1) w p := by
  rw [wInt_Ioo_interval zero_le_one, wInt_Ioo_interval (by norm_num)]
  have h := intervalIntegral.integral_comp_mul_sub (fun y => p.eval y * w y)
    (two_ne_zero (α := ℝ)) 1 (a := 0) (b := 1)
  norm_num at h
  simp only [shW, eval_comp, eval_shLin]
  rw [show (fun x => p.eval (2 * x - 1) * (2 * w (2 * x - 1))) =
      fun x => 2 * (p.eval (2 * x - 1) * w (2 * x - 1)) by ext; ring,
    intervalIntegral.integral_const_mul, h]
  ring

variable {w : ℝ → ℝ} {P : ℕ → ℝ[X]}

theorem isGaussWeight_shW (hw : IsGaussWeight (Ioo (-1) 1) w) :
    IsGaussWeight (Ioo 0 1) (shW w) where
  isOpen := isOpen_Ioo
  ordConnected := ordConnected_Ioo
  nonempty := ⟨1 / 2, by norm_num, by norm_num⟩
  pos := fun x hx => mul_pos two_pos (hw.pos _ ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  integrableOn := fun k => by
    set Q : ℝ[X] := C 2 * (C (1 / 2) * (X + 1)) ^ k
    have hg := hw.integrableOn_eval Q
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at hg
    have h2 := (hg.comp_mul_left (c := 2)).comp_sub_right (1 / 2)
    norm_num at h2
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    refine h2.congr fun x _ => ?_
    simp only [Q, shW, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
    rw [show 2 * (x - 1 / 2) = 2 * x - 1 by ring, show 1 / 2 * (2 * x - 1 + 1) = x by ring]
    ring

theorem isOrthMonic_shP (hP : ∀ n, IsOrthMonic (Ioo (-1) 1) w n (P n)) (n : ℕ) :
    IsOrthMonic (Ioo 0 1) (shW w) n (shP P n) := by
  obtain ⟨hm, hd, ho⟩ := hP n
  have h2 : ((2 : ℝ) ^ n)⁻¹ ≠ 0 := by positivity
  have hcd : ((P n).comp shLin).natDegree = n := by
    rw [natDegree_comp, hd, natDegree_shLin, mul_one]
  refine ⟨?_, ?_, fun q hqd => ?_⟩
  · have h1 : shLin.natDegree ≠ 0 := by rw [natDegree_shLin]; norm_num
    rw [Monic, shP, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp h1, hm.leadingCoeff,
      leadingCoeff_shLin, hd]
    field_simp
  · rw [shP, natDegree_C_mul h2, hcd]
  · set q' := q.comp (C (1 / 2) * X + C (1 / 2))
    have hq : q = q'.comp shLin := by
      rw [comp_assoc]
      conv_lhs => rw [← comp_X (p := q)]
      congr 1
      apply Polynomial.funext; intro x
      simp [shLin]; ring
    have hq' : q'.degree < n := by
      by_cases h0 : q = 0
      · simp [q', h0]
      · rw [degree_eq_natDegree (by intro h; apply h0; rw [hq, h, zero_comp]),
          natDegree_comp, natDegree_linear (by norm_num), mul_one]
        rw [degree_eq_natDegree h0] at hqd; exact hqd
    rw [shP, hq, mul_assoc, ← mul_comp, wInt_C_mul, wInt_shW, ho q' hq', mul_zero]

theorem shP_rec (hw : IsGaussWeight (Ioo (-1) 1) w) (hP : ∀ n, IsOrthMonic (Ioo (-1) 1) w n (P n))
    (n : ℕ) :
    X * shP P n = shP P (n + 1) + C ((recA (Ioo (-1) 1) w P n + 1) / 2) * shP P n +
      C (recB (Ioo (-1) 1) w P n / 4) * prevP (shP P) n := by
  apply Polynomial.funext; intro x
  have hx := congrArg (eval (2 * x - 1)) (dlmf_3_5_30 hw hP n)
  simp only [eval_mul, eval_add, eval_X, eval_C] at hx
  cases n with
  | zero =>
    simp only [prevP, eval_zero, mul_zero, add_zero] at hx
    simp only [shP, prevP, eval_mul, eval_add, eval_X, eval_C, eval_comp, eval_shLin,
      mul_zero, add_zero, pow_zero, inv_one, one_mul]
    linear_combination (1 / 2 : ℝ) * hx
  | succ m =>
    simp only [prevP] at hx
    simp only [shP, prevP, eval_mul, eval_add, eval_X, eval_C, eval_comp, eval_shLin]
    linear_combination ((2 : ℝ) ^ (m + 2))⁻¹ * hx

/-- The recurrence coefficients of the shifted polynomials: `α_n* = (α_n + 1)/2`,
`β_n* = β_n/4`, `h_0* = h_0`. -/
theorem recAB_shP (hw : IsGaussWeight (Ioo (-1) 1) w)
    (hP : ∀ n, IsOrthMonic (Ioo (-1) 1) w n (P n)) (n : ℕ) :
    recA (Ioo 0 1) (shW w) (shP P) n = (recA (Ioo (-1) 1) w P n + 1) / 2 ∧
      (1 ≤ n → recB (Ioo 0 1) (shW w) (shP P) n = recB (Ioo (-1) 1) w P n / 4) :=
  recAB_of_rec (isGaussWeight_shW hw) (isOrthMonic_shP hP) (shP_rec hw hP n)

theorem recB_shP_zero (hP : ∀ n, IsOrthMonic (Ioo (-1) 1) w n (P n)) :
    recB (Ioo 0 1) (shW w) (shP P) 0 = recB (Ioo (-1) 1) w P 0 := by
  rw [recB_zero (isOrthMonic_shP hP), recB_zero hP, ← wInt_shW]
  simp

/-! ### The shifted Chebyshev polynomials `T_n^*(x) = T_n(2x − 1)` -/

/-- The weight of `T_n^*`: `2 w_T(2x − 1) = (x − x²)^{−1/2}` on `(0, 1)`. -/
theorem shW_chebWeight_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    shW (chebWeight 1) x = (√(x - x ^ 2))⁻¹ := by
  have h : 0 < x - x ^ 2 := by nlinarith [hx.1, hx.2]
  simp only [shW, chebWeight, eval_one, one_mul]
  rw [show 1 - (2 * x - 1) ^ 2 = 4 * (x - x ^ 2) by ring, Real.sqrt_mul (by norm_num),
    show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have := Real.sqrt_pos.mpr h
  field_simp

/-- `p_n = T_n^*/k_n`: the shifted monic polynomial is `2^{1−2n} T_n(2x − 1)` (`n ≥ 1`). -/
theorem shP_gcT (n : ℕ) :
    shP gcT n = C (((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ (n - 1))⁻¹) * (Chebyshev.T ℝ n).comp shLin := by
  rw [shP, gcT, mul_comp, C_comp, ← mul_assoc, ← C_mul]

/-- Table 3.5.17_5, `T_n^*`: `α_n = ½`. -/
theorem table_3_5_17_5_Tstar_alpha (n : ℕ) :
    recA (Ioo 0 1) (shW (chebWeight 1)) (shP gcT) n = 1 / 2 := by
  rw [(recAB_shP isGaussWeight_cheb1 isOrthMonic_gcT n).1, table_3_5_17_5_T_alpha]; norm_num

/-- Table 3.5.17_5, `T_n^*`: `β_n = (1/16)(1 + δ_{n,1})`. -/
theorem table_3_5_17_5_Tstar_beta {n : ℕ} (hn : 1 ≤ n) :
    recB (Ioo 0 1) (shW (chebWeight 1)) (shP gcT) n = 1 / 16 * (1 + if n = 1 then 1 else 0) := by
  rw [(recAB_shP isGaussWeight_cheb1 isOrthMonic_gcT n).2 hn, table_3_5_17_5_T_beta hn]
  ring

/-- Table 3.5.17_5, `T_n^*`: `h_0 = π`. -/
theorem table_3_5_17_5_Tstar_h0 : recB (Ioo 0 1) (shW (chebWeight 1)) (shP gcT) 0 = π := by
  rw [recB_shP_zero isOrthMonic_gcT, table_3_5_17_5_T_h0]

end Azurite.DLMF
