/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section17Zeta
import Azurite.DLMF.Chapter5.Section11StirlingK
import Azurite.Transcendental.DigammaStirling
import Azurite.BrentZimmermann.Chapter4.Exercises

/-!
# The Glaisher–Kinkelin constant: the expansion with its remainder

For the computation of `A = e^C` (`DLMF.glaisherA`, `DLMF.glaisherC`; the Glaisher–Kinkelin
constant, Glaisher's constant in DLMF §5.17) the asymptotic expansion 5.17.5 is needed with an
explicit remainder at the integers.

* `abs_glaisherC_sub_le`: for `n ≥ 1` and `j ≥ 1`,
  `|C − (glaisherSeq n + ∑_{k=1}^{j} t_k)| ≤ |t_j|` with
  `t_k = B_{2k+2} / (2k (2k + 1) (2k + 2) n^{2k})` (`glaisherTerm`), where `glaisherSeq n` is
  `∑_{k ≤ n} k ln k − (n²/2 + n/2 + 1/12) ln n + n²/4`.  It is `glaisherR_sub_sum` (the
  expansion with the remainder `∫₀^∞ B̃_{2m}(t)/(n + t)^{2m−1} dt`) and
  `|B̃_{2m}| ≤ |B_{2m}|`.
* `abs_glaisherTerm_le`: `|t_j| ≤ 16 (j + 1)² / 4^j` when `n ≥ 4j + 4`.
* `sum_mul_log_eq_log_hyper`: `∑_{k ≤ n} k ln k = ln ((n!)ⁿ / ∏_{k<n} k!)`.
* `glaisherTau`, `glaisherTerm_eq_tau`, `exTerm_succ_eq_tau`, `glaisherSeq_sub_eq`: the same
  expansion in the enveloping form of DLMF 2.10.4–2.10.5 (`dlmf_2_10_5_bound`), with the
  coefficients on the tangent numbers — what the summation on enclosures uses.
* `glaisherA_eq_exp_zeta`: `A = exp (1/12 − ζ′(−1))`.
-/

open Complex Filter Topology Set Finset MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

/-- `t_k = B_{2k+2} / (2k (2k + 1) (2k + 2) n^{2k})`, the terms of the expansion of
`glaisherSeq n` around `C`. -/
noncomputable def glaisherTerm (n k : ℕ) : ℝ :=
  (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2) * (n : ℝ) ^ (2 * k))

/-- The sum of 5.17.5 up to `z^{−2j}`, without the vanishing odd terms. -/
theorem sum_glaisherCoeff (j : ℕ) (z : ℂ) :
    ∑ s ∈ range (2 * j + 1), glaisherCoeff s * z ^ (-(s : ℤ)) =
      -(glaisherC : ℂ) + ∑ k ∈ Icc 1 j,
        (bernoulli (2 * k + 2) : ℂ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
          z ^ (-((2 * k : ℕ) : ℤ)) := by
  induction j with
  | zero => simp [glaisherCoeff]
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      glaisherCoeff_odd j, zero_mul, add_zero, sum_Icc_succ_top (by omega),
      show 2 * j + 1 + 1 = 2 * (j + 1) by ring, glaisherCoeff_even (by omega : 1 ≤ j + 1)]
    push_cast
    ring

/-- **The expansion of `C` with its remainder**: after `j ≥ 1` terms the error is at most the
last term. -/
theorem abs_glaisherC_sub_le {n : ℕ} (hn : 1 ≤ n) {j : ℕ} (hj : 1 ≤ j) :
    |glaisherC - (glaisherSeq n + ∑ k ∈ Icc 1 j, glaisherTerm n k)| ≤ |glaisherTerm n j| := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hz0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hz : (n : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp; exact_mod_cast hn
  have hsum := glaisherR_sub_sum (2 * i + 1) hz
  rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring, sum_glaisherCoeff, glaisherR_nat,
    show 2 * i + 1 + 3 = 2 * (i + 2) by ring] at hsum
  have hterm : ∀ k : ℕ, (bernoulli (2 * k + 2) : ℂ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
      (n : ℂ) ^ (-((2 * k : ℕ) : ℤ)) = ((glaisherTerm n k : ℝ) : ℂ) := fun k => by
    rw [zpow_neg, zpow_natCast, glaisherTerm]
    push_cast
    rw [← div_eq_mul_inv, div_div]
  rw [sum_congr rfl (fun k _ => hterm k), ← ofReal_sum] at hsum
  obtain ⟨Sr, hSr⟩ : ∃ Sr : ℝ, Sr = ∑ k ∈ Icc 1 (i + 1), glaisherTerm n k := ⟨_, rfl⟩
  rw [← hSr] at hsum ⊢
  have hc : (1 / ((((2 * i + 1 : ℕ) : ℂ) + 2) * (((2 * i + 1 : ℕ) : ℂ) + 3)) : ℂ)
      = ((1 / ((2 * (i : ℝ) + 3) * (2 * i + 4)) : ℝ) : ℂ) := by
    push_cast
    ring
  have hb := (integrableOn_div_add_pow (measurable_periodicBernoulli (2 * (i + 2)))
    (C := |(bernoulli (2 * (i + 2)) : ℝ)|)
    (abs_periodicBernoulli_two_mul_le (by omega : 1 ≤ i + 2)) hz0 Real.pi_pos le_rfl
    (by simp) (m := 2 * (i + 1) + 1) (by omega)).2
  rw [Real.sin_pi_div_two, one_pow, one_mul, Complex.norm_natCast,
    show 2 * (i + 1) + 1 - 1 = 2 * (i + 1) by omega] at hb
  have hre : ((-glaisherSeq n - (-glaisherC + Sr) : ℝ) : ℂ)
      = -(((1 / ((2 * (i : ℝ) + 3) * (2 * i + 4)) : ℝ) : ℂ) *
        bernInt (2 * (i + 2)) (2 * (i + 1) + 1) n) := by
    rw [← hc, ← hsum]
    push_cast
    ring
  have hcpos : (0 : ℝ) < 1 / ((2 * (i : ℝ) + 3) * (2 * i + 4)) := by positivity
  have hnorm : |-glaisherSeq n - (-glaisherC + Sr)|
      = 1 / ((2 * (i : ℝ) + 3) * (2 * i + 4)) *
        ‖bernInt (2 * (i + 2)) (2 * (i + 1) + 1) n‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hre, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hcpos]
  have hK : ‖bernInt (2 * (i + 2)) (2 * (i + 1) + 1) n‖
      ≤ |(bernoulli (2 * (i + 2)) : ℝ)| / ((2 * (i : ℝ) + 2) * (n : ℝ) ^ (2 * (i + 1))) := by
    refine hb.trans (le_of_eq ?_)
    push_cast
    ring_nf
  have habs : |glaisherC - (glaisherSeq n + Sr)| = |-glaisherSeq n - (-glaisherC + Sr)| := by
    congr 1
    ring
  have hdpos : (0 : ℝ) < 2 * ((i + 1 : ℕ) : ℝ) * (2 * ((i + 1 : ℕ) : ℝ) + 1)
      * (2 * ((i + 1 : ℕ) : ℝ) + 2) * (n : ℝ) ^ (2 * (i + 1)) := by positivity
  rw [habs, hnorm, glaisherTerm, abs_div, abs_of_pos hdpos,
    show 2 * (i + 1) + 2 = 2 * (i + 2) by ring]
  refine (mul_le_mul_of_nonneg_left hK hcpos.le).trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

/-- `|B_{2k}| ≤ 4 (2k)^{2k}`. -/
theorem abs_bernoulli_two_mul_le_pow {k : ℕ} (hk : 1 ≤ k) :
    |(bernoulli (2 * k) : ℝ)| ≤ 4 * ((2 * k : ℕ) : ℝ) ^ (2 * k) := by
  rw [BZ.abs_bernoulli_two_mul_eq hk]
  have hζ := BZ.zetaReal_two_mul_le hk
  have hζ0 : 0 ≤ BZ.zetaReal (2 * k) := by linarith [BZ.one_le_zetaReal_two_mul hk]
  have hπ : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpow : (1 : ℝ) ≤ (2 * Real.pi) ^ (2 * k) :=
    one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hfac : ((2 * k).factorial : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ (2 * k) := by
    exact_mod_cast Nat.factorial_le_pow (2 * k)
  have hf0 : (0 : ℝ) ≤ ((2 * k).factorial : ℝ) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have h1 : 2 * ((2 * k).factorial : ℝ) * BZ.zetaReal (2 * k)
      ≤ 2 * ((2 * k : ℕ) : ℝ) ^ (2 * k) * 2 := by
    have := mul_le_mul hfac (hζ.trans hπ) hζ0 (by positivity)
    linarith
  have h2 : 2 * ((2 * k : ℕ) : ℝ) ^ (2 * k) * 2
      ≤ 4 * ((2 * k : ℕ) : ℝ) ^ (2 * k) * (2 * Real.pi) ^ (2 * k) := by
    have h0 : (0 : ℝ) ≤ 4 * ((2 * k : ℕ) : ℝ) ^ (2 * k) := by positivity
    have := mul_le_mul_of_nonneg_left hpow h0
    linarith
  exact h1.trans h2

/-- **The terms are small**: `|t_j| ≤ 16 (j + 1)² / 4^j` at `n ≥ 4j + 4`. -/
theorem abs_glaisherTerm_le {n j : ℕ} (hj : 1 ≤ j) (hn : 4 * j + 4 ≤ n) :
    |glaisherTerm n j| ≤ 16 * ((j : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ j := by
  have hB := abs_bernoulli_two_mul_le_pow (by omega : 1 ≤ j + 1)
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at hB
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hnR : 2 * (2 * (j : ℝ) + 2) ≤ n := by exact_mod_cast (by omega : 2 * (2 * j + 2) ≤ n)
  have hpn : (2 * (2 * (j : ℝ) + 2)) ^ (2 * j) ≤ (n : ℝ) ^ (2 * j) :=
    pow_le_pow_left₀ (by positivity) hnR _
  have hd : (1 : ℝ) ≤ 2 * j * (2 * j + 1) * (2 * j + 2) := by
    have h1 : (1 : ℝ) ≤ 2 * j * (2 * j + 1) := by nlinarith
    nlinarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hden : (0 : ℝ) < 2 * j * (2 * j + 1) * (2 * j + 2) * (n : ℝ) ^ (2 * j) :=
    mul_pos (by linarith) (pow_pos hn0 _)
  rw [glaisherTerm, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hcast : ((2 * j + 2 : ℕ) : ℝ) = 2 * (j : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hB
  have e1 : (2 * (j : ℝ) + 2) ^ (2 * j + 2) = (2 * (j : ℝ) + 2) ^ (2 * j) * (2 * j + 2) ^ 2 :=
    pow_add _ _ _
  have e2 : (2 * (2 * (j : ℝ) + 2)) ^ (2 * j) = 4 ^ j * (2 * (j : ℝ) + 2) ^ (2 * j) := by
    rw [mul_pow, pow_mul]
    norm_num
  have e3 : (1 / 4 : ℝ) ^ j * 4 ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have hP0 : (0 : ℝ) ≤ (2 * (j : ℝ) + 2) ^ (2 * j) := by positivity
  have hq0 : (0 : ℝ) < (1 / 4 : ℝ) ^ j := by positivity
  -- 4 P (2j+2)² = 16 (j+1)² (1/4)^j · 4^j P ≤ 16 (j+1)² (1/4)^j · n^{2j} ≤ … · d · n^{2j}
  have step1 : 4 * ((2 * (j : ℝ) + 2) ^ (2 * j) * (2 * j + 2) ^ 2)
      = 16 * ((j : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ j * (4 ^ j * (2 * (j : ℝ) + 2) ^ (2 * j)) := by
    have : 16 * ((j : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ j * (4 ^ j * (2 * (j : ℝ) + 2) ^ (2 * j))
        = 16 * ((j : ℝ) + 1) ^ 2 * ((1 / 4 : ℝ) ^ j * 4 ^ j) * (2 * (j : ℝ) + 2) ^ (2 * j) := by
      ring
    rw [this, e3]
    ring
  have hc0 : (0 : ℝ) ≤ 16 * ((j : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ j := by positivity
  calc |(bernoulli (2 * j + 2) : ℝ)| ≤ 4 * (2 * (j : ℝ) + 2) ^ (2 * j + 2) := hB
    _ = 16 * ((j : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ j * (4 ^ j * (2 * (j : ℝ) + 2) ^ (2 * j)) := by
        rw [e1, step1]
    _ ≤ 16 * ((j : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ j * (n : ℝ) ^ (2 * j) := by
        rw [← e2]
        exact mul_le_mul_of_nonneg_left hpn hc0
    _ ≤ 16 * ((j : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ j
          * (2 * j * (2 * j + 1) * (2 * j + 2) * (n : ℝ) ^ (2 * j)) := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ (2 * j) := by positivity
        have := mul_le_mul_of_nonneg_right hd hn0
        rw [one_mul] at this
        exact mul_le_mul_of_nonneg_left this hc0

/-- **The sum of `k ln k` is the logarithm of the hyperfactorial**
`∏ k^k = (n!)ⁿ / ∏_{k<n} k!`. -/
theorem sum_mul_log_eq_log_hyper (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * Real.log k
      = Real.log ((n ! : ℝ) ^ n / ∏ k ∈ range n, (k ! : ℝ)) := by
  have h := sum_log_factorial n
  have hW : (∏ k ∈ range n, (k ! : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun k _ => by positivity
  rw [Real.log_div (by positivity) hW, Real.log_pow, Real.log_prod (fun k _ => by positivity)]
  linarith

/-- `0 ≤ ∑_{k ≤ n} k ln k ≤ n³`. -/
theorem sum_mul_log_bounds (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * Real.log k ∧
      ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * Real.log k ≤ (n : ℝ) ^ 3 := by
  constructor
  · refine sum_nonneg fun k hk => ?_
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    exact mul_nonneg (by linarith) (Real.log_nonneg hk1)
  · have hterm : ∀ k ∈ Finset.Icc 1 n, (k : ℝ) * Real.log k ≤ (n : ℝ) ^ 2 := fun k hk => by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hk).2
      have hl : Real.log k ≤ k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have hl0 := Real.log_nonneg hk1
      nlinarith
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast
    ring

/-! ### The enveloping form, on the tangent numbers -/

/-- `τ_k = |t_k| = c_{k+1} / (2k (2k + 1) n^{2k})` with `c_m = T_m / (4^{2m} − 2^{2m}) =
|B_{2m}| / (2m)` the coefficients of the series of `ψ` (`psiCoeffT`). -/
noncomputable def glaisherTau (n k : ℕ) : ℝ :=
  psiCoeffT (k + 1) / (2 * k * (2 * k + 1) * (n : ℝ) ^ (2 * k))

theorem glaisherTau_pos {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : 0 < glaisherTau n k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  exact div_pos (psiCoeffT_pos (by omega)) (by positivity)

/-- `t_k = (−1)^k τ_k`. -/
theorem glaisherTerm_eq_tau {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    glaisherTerm n k = (-1) ^ k * glaisherTau n k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := bernoulli_div_eq_psiCoeffT (by omega : 1 ≤ k + 1)
  have hB : (bernoulli (2 * k + 2) : ℝ) = (-1) ^ k * psiCoeffT (k + 1) * (2 * k + 2) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring] at h
    push_cast at h
    rw [div_eq_iff (by positivity)] at h
    rw [h, pow_succ, pow_succ]
    ring
  rw [glaisherTerm, glaisherTau, hB]
  field_simp

theorem glaisherTau_eq_abs {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    glaisherTau n k = |glaisherTerm n k| := by
  rw [glaisherTerm_eq_tau hn hk, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (glaisherTau_pos hn hk)]

theorem succ_sq_mul_quarter_pow_le (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k ≤ 1 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hq : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k := by positivity
    have h1 : (((k + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((k : ℝ) + 1) ^ 2 := by
      push_cast
      nlinarith
    calc (((k + 1 : ℕ) : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ (k + 1)
        = (((k + 1 : ℕ) : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k / 4 := by rw [pow_succ]; ring
      _ ≤ 4 * ((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k / 4 := by
          have := mul_le_mul_of_nonneg_right h1 hq
          linarith
      _ = ((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k := by ring
      _ ≤ 1 := ih

/-- `τ_k ≤ 16` at `n ≥ 4k + 4`. -/
theorem glaisherTau_le_sixteen {n k : ℕ} (hk : 1 ≤ k) (hn : 4 * k + 4 ≤ n) :
    glaisherTau n k ≤ 16 := by
  rw [glaisherTau_eq_abs (by omega) hk]
  have h1 := abs_glaisherTerm_le hk hn
  have h2 := succ_sq_mul_quarter_pow_le k hk
  linarith

/-- The summand of DLMF 2.10.4 is `(−1)^(k+1) τ_k`. -/
theorem exTerm_succ_eq_tau {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    exTerm (k + 1) n = (-1) ^ (k + 1) * glaisherTau n k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := glaisherTerm_eq_tau hn hk
  have e1 : (2 * ((k + 1 : ℕ) : ℝ)) * (2 * ((k + 1 : ℕ) : ℝ) - 1) * (2 * ((k + 1 : ℕ) : ℝ) - 2)
      = 2 * k * (2 * k + 1) * (2 * k + 2) := by
    push_cast
    ring
  have e : exTerm (k + 1) n = -glaisherTerm n k := by
    rw [exTerm, e1, glaisherTerm, show 2 * (k + 1) = 2 * k + 2 by ring,
      show 2 * k + 2 - 2 = 2 * k by omega, neg_div, neg_div, div_div]
  rw [e, h, pow_succ]
  ring

/-- **The expansion of `C` in the form of DLMF 2.10.4**: `glaisherSeq n − C` is the sum of the
terms `2, …, k` and the remainder `R_{k+1}(n)`. -/
theorem glaisherSeq_sub_eq {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    glaisherSeq n - glaisherC = ∑ s ∈ Finset.Icc 2 k, exTerm s n + jlogR (k + 1) n := by
  obtain ⟨C, hC⟩ := dlmf_2_10_4
  have hCeq := (dlmf_2_10_6 hC).1
  have h := hC (k + 1) (by omega) n hn
  rw [show k + 1 - 1 = k by omega, hCeq, exS] at h
  rw [glaisherSeq, h]
  ring

/-- **`A = exp (1/12 − ζ′(−1))`.** -/
theorem glaisherA_eq_exp_zeta :
    glaisherA = Real.exp (1 / 12 - (deriv riemannZeta (-1)).re) := by
  rw [deriv_zeta_neg_one, glaisherA]
  congr 1
  simp

end Azurite.DLMF
