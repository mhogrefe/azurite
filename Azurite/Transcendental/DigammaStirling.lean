/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.LogGammaStirling
import Azurite.DLMF.Chapter5.Section4Series
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The asymptotic series of `ψ` with its remainder, in tangent numbers

For `x > 0` (DLMF 5.11.2 and §5.11(ii), `Azurite/DLMF/Chapter5/Section11Bounds.lean`),

  `ψ(x) = ln x − 1/(2x) − ∑_{k=1}^{n−1} B_{2k} / (2k x^(2k)) + r`,

where the remainder `r` has the sign of the first neglected term and is at most that term in
magnitude.  With the tangent numbers `T_k` the coefficients are

  `B_{2k} / (2k) = (−1)^(k+1) c_k`,   `c_k = T_k / (4^(2k) − 2^(2k)) > 0`

(`psiCoeffT`, `bernoulli_div_eq_psiCoeffT`).  `psiNu_eq_sum_add` is the statement used by
`AzFloat/DigammaBracket.lean`: `ν(x) = ψ(x) − ln x + 1/(2x) = ∑_{i<n−1} t_{i+1}(x) + r` with
`t_k(x) = (−1)^k c_k / x^(2k)`, `0 ≤ (−1)^n r ≤ c_n / x^(2n)`, for every `n ≥ 1`.

`psiR_near_zero`: `−1/x − 2 < ψ(x) < −1/x` for `0 < |x| ≤ 1/4`, the pole of `ψ` at `0`.
-/

namespace Azurite

open Finset

/-- The positive coefficient `c_k = T_k / (4^(2k) − 2^(2k))` of the series of `ψ`. -/
noncomputable def psiCoeffT (k : ℕ) : ℝ :=
  (BZ.tangentNumber k : ℝ) / ((4 : ℝ) ^ (2 * k) - 2 ^ (2 * k))

theorem psiCoeffT_eq {k : ℕ} (hk : 1 ≤ k) : psiCoeffT k = (2 * k - 1) * stirlingCoeffT k := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd := four_pow_sub_two_pow_pos hk
  have h2 : (2 * (k : ℝ) - 1) ≠ 0 := by linarith
  rw [psiCoeffT, stirlingCoeffT]
  field_simp

theorem psiCoeffT_pos {k : ℕ} (hk : 1 ≤ k) : 0 < psiCoeffT k := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [psiCoeffT_eq hk]
  exact mul_pos (by linarith) (stirlingCoeffT_pos hk)

/-- `B_{2k} / (2k) = (−1)^(k+1) c_k` for `k ≥ 1`. -/
theorem bernoulli_div_eq_psiCoeffT {k : ℕ} (hk : 1 ≤ k) :
    (bernoulli (2 * k) : ℝ) / (2 * k) = (-1) ^ (k + 1) * psiCoeffT k := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h := bernoulli_div_eq_stirlingCoeffT hk
  have h2 : (2 * (k : ℝ) - 1) ≠ 0 := by linarith
  rw [psiCoeffT_eq hk, ← mul_assoc, mul_comm _ (2 * (k : ℝ) - 1), mul_assoc, ← h]
  field_simp

theorem psiCoeffT_one : psiCoeffT 1 = 1 / 12 := by
  have h := bernoulli_div_eq_psiCoeffT (k := 1) le_rfl
  rw [show 2 * 1 = 2 by norm_num, bernoulli_two] at h
  norm_num at h
  linarith

/-- The term of index `k ≥ 1` of the series of `ψ`, `(−1)^k c_k / x^(2k)`. -/
noncomputable def psiTermT (k : ℕ) (x : ℝ) : ℝ := (-1) ^ k * psiCoeffT k / x ^ (2 * k)

/-- `ν(x) = ψ(x) − ln x + 1/(2x)`. -/
noncomputable def psiNu (x : ℝ) : ℝ := DLMF.psiR x - Real.log x + 1 / (2 * x)

/-- The remainder of DLMF's series after the terms `k = 1, …, n − 1`, for a real argument. -/
theorem psiRem_eq_psiNu_sub {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    DLMF.psiRem n x = ((psiNu x - ∑ i ∈ range (n - 1), psiTermT (i + 1) x : ℝ) : ℂ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [DLMF.psiRem, DLMF.digamma_ofReal, show 2 * 1 = 1 + 1 by norm_num, sum_range_succ,
      sum_range_one, DLMF.psiCoeff, DLMF.psiCoeff, ← Complex.ofReal_log hx.le]
    simp only [↓reduceIte, one_ne_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one, Nat.cast_one,
      zpow_neg, zpow_one, Nat.sub_self, range_zero, sum_empty, sub_zero, psiNu]
    push_cast
    ring
  | succ n hn ih =>
    have hs := DLMF.psiRem_succ hn (x : ℂ)
    rw [ih, DLMF.psiFirst_ofReal hn] at hs
    have e : DLMF.psiRem (n + 1) x
        = ((psiNu x - ∑ i ∈ range (n - 1), psiTermT (i + 1) x : ℝ) : ℂ)
          - ((-(bernoulli (2 * n) : ℝ) / (2 * n * x ^ (2 * n)) : ℝ) : ℂ) := by
      rw [hs]; ring
    rw [e, ← Complex.ofReal_sub, show n + 1 - 1 = (n - 1) + 1 by omega, sum_range_succ,
      show n - 1 + 1 = n by omega]
    congr 1
    have hb := bernoulli_div_eq_psiCoeffT hn
    have hx' : x ^ (2 * n) ≠ 0 := (pow_pos hx _).ne'
    have hn0 : (2 * (n : ℝ)) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hterm : -(bernoulli (2 * n) : ℝ) / (2 * n * x ^ (2 * n)) = psiTermT n x := by
      rw [psiTermT, show -(bernoulli (2 * n) : ℝ) / (2 * n * x ^ (2 * n))
        = -((bernoulli (2 * n) : ℝ) / (2 * n)) / x ^ (2 * n) by field_simp, hb, pow_succ]
      ring
    rw [hterm]
    ring

/-- **The series of `ψ` with its remainder**: for `x > 0` and `n ≥ 1`,
`ν(x) = ∑_{i<n−1} t_{i+1}(x) + r` with `0 ≤ (−1)^n r` and `|r| ≤ c_n / x^(2n)`. -/
theorem psiNu_eq_sum_add {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ r : ℝ, psiNu x = ∑ i ∈ range (n - 1), psiTermT (i + 1) x + r ∧
      0 ≤ (-1) ^ n * r ∧ |r| ≤ psiCoeffT n / x ^ (2 * n) := by
  obtain ⟨r, τ, hr, hτ, habs, hsign⟩ := DLMF.dlmf_5_11_ii_psi_real hn hx
  rw [psiRem_eq_psiNu_sub hn hx, Complex.ofReal_inj] at hr
  rw [DLMF.psiFirst_ofReal hn, Complex.ofReal_inj] at hτ
  have hxp : 0 < x ^ (2 * n) := pow_pos hx _
  have hc := psiCoeffT_pos hn
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hτ' : τ = (-1) ^ n * (psiCoeffT n / x ^ (2 * n)) := by
    rw [← hτ, show -(bernoulli (2 * n) : ℝ) / (2 * n * x ^ (2 * n))
      = -((bernoulli (2 * n) : ℝ) / (2 * n)) / x ^ (2 * n) by field_simp,
      bernoulli_div_eq_psiCoeffT hn, pow_succ]
    ring
  have hq : 0 < psiCoeffT n / x ^ (2 * n) := div_pos hc hxp
  refine ⟨r, by rw [← hr]; ring, ?_, ?_⟩
  · rw [hτ'] at hsign
    have : 0 ≤ ((-1 : ℝ) ^ n * r) * (psiCoeffT n / x ^ (2 * n)) := by nlinarith [hsign]
    exact nonneg_of_mul_nonneg_left this hq
  · rw [hτ', abs_mul, abs_of_pos hq] at habs
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] at habs <;> simpa using habs

/-- `ln x − 1/(2x) − 1/(12x²) ≤ ψ(x) ≤ ln x − 1/(2x)` for `x > 0`. -/
theorem psiR_bounds {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) ≤ DLMF.psiR x ∧
      DLMF.psiR x ≤ Real.log x - 1 / (2 * x) := by
  obtain ⟨r, hν, hsign, habs⟩ := psiNu_eq_sum_add (n := 1) le_rfl hx
  rw [Nat.sub_self, range_zero, sum_empty, zero_add, psiNu] at hν
  rw [pow_one, neg_one_mul] at hsign
  rw [psiCoeffT_one, abs_le] at habs
  have : (1 : ℝ) / 12 / x ^ (2 * 1) = 1 / (12 * x ^ 2) := by rw [div_div]
  rw [this] at habs
  constructor <;> linarith [habs.1]

/-- **`ψ` at its pole `0`**: `−1/x − 2 < ψ(x) < −1/x` for `0 < |x| ≤ 1/4`. -/
theorem psiR_near_zero {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 4) :
    -(1 / x) - 2 < DLMF.psiR x ∧ DLMF.psiR x < -(1 / x) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  have hnp : ∀ m : ℕ, x ≠ -m := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact hx0 (by simpa using hm)
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
      linarith
  have hshift := DLMF.psiR_add_nat hnp 3
  rw [sum_range_succ, sum_range_succ, sum_range_one] at hshift
  push_cast at hshift
  rw [add_zero] at hshift
  have hy : 0 < x + 3 := by linarith
  obtain ⟨hlo, hhi⟩ := psiR_bounds hy
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hepos := Real.exp_pos 1
  -- `2 − e/y ≤ ln y ≤ y/e`
  have hlog_hi : Real.log (x + 3) ≤ (x + 3) / Real.exp 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hy hepos)
    rw [Real.log_div hy.ne' hepos.ne', Real.log_exp] at this
    linarith
  have hlog_lo : 2 - Real.exp 1 / (x + 3) ≤ Real.log (x + 3) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hy hepos)
    rw [Real.log_div hy.ne' hepos.ne', Real.log_exp, inv_div] at this
    linarith
  have h1 : (0 : ℝ) < x + 1 := by linarith
  have h2 : (0 : ℝ) < x + 2 := by linarith
  have a1 : 1 / (x + 1) ≤ 4 / 3 := by rw [div_le_iff₀ h1]; linarith
  have a1' : 4 / 5 ≤ 1 / (x + 1) := by rw [le_div_iff₀ h1]; linarith
  have a2 : 1 / (x + 2) ≤ 4 / 7 := by rw [div_le_iff₀ h2]; linarith
  have a2' : 4 / 9 ≤ 1 / (x + 2) := by rw [le_div_iff₀ h2]; linarith
  have b1 : (x + 3) / Real.exp 1 ≤ 6 / 5 := by rw [div_le_iff₀ hepos]; linarith
  have b2 : Real.exp 1 / (x + 3) ≤ 99 / 100 := by rw [div_le_iff₀ hy]; linarith
  have b3 : 1 / (2 * (x + 3)) ≤ 2 / 11 := by rw [div_le_iff₀ (by linarith)]; linarith
  have b3' : 0 < 1 / (2 * (x + 3)) := by positivity
  have b4 : 1 / (12 * (x + 3) ^ 2) ≤ 1 / 90 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  constructor <;> linarith

end Azurite
