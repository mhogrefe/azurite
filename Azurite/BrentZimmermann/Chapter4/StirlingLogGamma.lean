/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.ErrorFunction
import Mathlib.NumberTheory.ZetaValues

/-!
# Brent–Zimmermann §4.5: Stirling's asymptotic expansion of `ln Γ`

An asymptotic expansion can sometimes give arbitrary precision.  For large `x > 0`,

  `ln Γ(x) = (x − 1/2) ln x − x + ln(2π)/2 + ∑_{k=1}^{m−1} B_{2k}/(2k(2k−1) x^(2k−1)) + R_m(x)`
                                                                                        (4.38)
with `R_m(x)` smaller in absolute value than the first neglected term
`B_{2m}/(2m(2m−1)x^(2m−1))` and of the same sign.  The ratio of successive terms is
`t_{k+1}/t_k ≈ −(k/(πx))²`, so the terms start to grow for `k > πx` and the attainable accuracy is
limited, `ln |R_m(x)| > −2πx ln x + O(x)`.  The
functional equation `Γ(x+1) = x Γ(x)` removes the limitation: evaluate `ln Γ(x + δ)` for a large
integer `δ` and shift back (Exercise 4.21).

What is formalized:

* `stirlingTerm k x = B_{2k} / (2k(2k−1) x^(2k−1))`, `stirlingApprox m x`, and the remainder
  `stirlingRem m x = ln Γ(x) − stirlingApprox m x` — definitions; the bound on `R_m` is *not*
  proven (it needs Binet's formula / Euler–Maclaurin for `ln Γ`, not in Mathlib).
* `bernoulli_two_mul_eq_zeta` — `B_{2k} = (−1)^(k+1) · 2 (2k)! ζ(2k) / (2π)^(2k)` from Mathlib's
  `hasSum_zeta_nat`, with `one_le_zetaReal_two_mul`, `zetaReal_two_mul_le` (`1 ≤ ζ(2k) ≤ π²/6`);
  `sign_bernoulli_two_mul` — `B_{2k}` has sign `(−1)^(k+1)`, so the terms alternate.
* `abs_stirlingTerm_eq` — `|t_k| = 2 (2k−2)! ζ(2k) / ((2π)^(2k) x^(2k−1))`;
  `stirlingTerm_ratio_bounds` — `(2k)(2k−1)/(2(2πx)²) ≤ |t_{k+1}|/|t_k| ≤ 2(2k)(2k−1)/(2πx)²`,
  the text's `≈ (k/(πx))²` within a factor `2`; `abs_stirlingTerm_lt_succ` — the terms grow once
  `2(2πx)² < (2k)(2k−1)` (`k ≳ 2.8 πx`).
* `abs_stirlingTerm_ge` — every term is at least `e^(−2πx) / (2π² x)`: the smallest term of the
  divergent series, hence the accuracy obtainable without shifting, is about `2πx` nats
  (`2πx / ln 2` bits).  (The text's `−2πx ln x + O(x)` is a weaker lower bound of the same kind.)
* `log_Gamma_eq_log_Gamma_add_sub` — the shift: `ln Γ(x) = ln Γ(x + δ) − ∑_{i<δ} ln(x + i)`.
-/

namespace Azurite

namespace BZ

open Real Finset

/-! ### The expansion -/

/-- The `k`-th term of (4.38), `B_{2k} / (2k (2k−1) x^(2k−1))`, for `k ≥ 1`. -/
noncomputable def stirlingTerm (k : ℕ) (x : ℝ) : ℝ :=
  (bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1) * x ^ (2 * k - 1))

/-- The truncated expansion with the terms `k = 1, …, m − 1`. -/
noncomputable def stirlingApprox (m : ℕ) (x : ℝ) : ℝ :=
  (x - 1 / 2) * Real.log x - x + Real.log (2 * π) / 2 + ∑ k ∈ Icc 1 (m - 1), stirlingTerm k x

/-- The remainder `R_m(x) = ln Γ(x) − (expansion with m − 1 terms)`. -/
noncomputable def stirlingRem (m : ℕ) (x : ℝ) : ℝ := Real.log (Real.Gamma x) - stirlingApprox m x

theorem log_Gamma_eq_stirlingApprox_add (m : ℕ) (x : ℝ) :
    Real.log (Real.Gamma x) = stirlingApprox m x + stirlingRem m x := by
  unfold stirlingRem; ring

/-! ### The Bernoulli numbers through the even zeta values -/

/-- `ζ(2k) = (−1)^(k+1) 2^(2k−1) π^(2k) B_{2k} / (2k)!` (Mathlib's `hasSum_zeta_nat`). -/
theorem zetaReal_two_mul_eq {k : ℕ} (hk : 1 ≤ k) :
    zetaReal (2 * k) = (-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k)
      / (2 * k).factorial := by
  have h := hasSum_zeta_nat (k := k) (by omega)
  rw [zetaReal, ← h.tsum_eq]
  congr 1
  funext n
  rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, one_div]

/-- `1 ≤ ζ(2k)`: the `n = 1` term. -/
theorem one_le_zetaReal_two_mul {k : ℕ} (hk : 1 ≤ k) : 1 ≤ zetaReal (2 * k) := by
  unfold zetaReal
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * (k : ℝ)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  have h := hs.le_tsum 1 fun n _ => by positivity
  simpa using h

/-- `ζ(2k) ≤ ζ(2) = π²/6` for `k ≥ 1`. -/
theorem zetaReal_two_mul_le {k : ℕ} (hk : 1 ≤ k) : zetaReal (2 * k) ≤ π ^ 2 / 6 := by
  unfold zetaReal
  rw [← hasSum_zeta_two.tsum_eq]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * (k : ℝ)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine hs.tsum_le_tsum (fun n => ?_) hasSum_zeta_two.summable
  rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, one_div]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, zero_pow (by omega), zero_pow two_ne_zero]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hn1 (by omega))

/-- `B_{2k} = (−1)^(k+1) · 2 (2k)! ζ(2k) / (2π)^(2k)`. -/
theorem bernoulli_two_mul_eq_zeta {k : ℕ} (hk : 1 ≤ k) :
    (bernoulli (2 * k) : ℝ)
      = (-1) ^ (k + 1) * 2 * (2 * k).factorial * zetaReal (2 * k) / (2 * π) ^ (2 * k) := by
  have h := zetaReal_two_mul_eq hk
  have hf : (0 : ℝ) < (2 * k).factorial := by positivity
  have hπ : (0 : ℝ) < π ^ (2 * k) := by positivity
  have h2 : (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hζF : zetaReal (2 * k) * (2 * k).factorial
      = (-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) := by
    rw [h]; field_simp
  generalize hε : ((-1 : ℝ) ^ (k + 1)) = ε at hζF ⊢
  have hε2 : ε ^ 2 = 1 := by rw [← hε, ← pow_mul, pow_mul']; simp
  rw [eq_div_iff (by positivity), mul_pow, h2]
  calc (bernoulli (2 * k) : ℝ) * (2 * 2 ^ (2 * k - 1) * π ^ (2 * k))
      = ε ^ 2 * (2 * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k)) := by rw [hε2]; ring
    _ = ε * 2 * (zetaReal (2 * k) * (2 * k).factorial) := by rw [hζF]; ring
    _ = ε * 2 * (2 * k).factorial * zetaReal (2 * k) := by ring

/-- `B_{2k}` has the sign `(−1)^(k+1)`. -/
theorem sign_bernoulli_two_mul {k : ℕ} (hk : 1 ≤ k) :
    0 < (-1) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
  rw [bernoulli_two_mul_eq_zeta hk]
  have hz := one_le_zetaReal_two_mul hk
  generalize hε : ((-1 : ℝ) ^ (k + 1)) = ε
  have hε2 : ε ^ 2 = 1 := by rw [← hε, ← pow_mul, pow_mul']; simp
  have : ε * (ε * 2 * (2 * k).factorial * zetaReal (2 * k) / (2 * π) ^ (2 * k))
      = 2 * (2 * k).factorial * zetaReal (2 * k) / (2 * π) ^ (2 * k) := by
    rw [show ε * (ε * 2 * (2 * k).factorial * zetaReal (2 * k) / (2 * π) ^ (2 * k))
      = ε ^ 2 * (2 * (2 * k).factorial * zetaReal (2 * k) / (2 * π) ^ (2 * k)) by ring, hε2,
      one_mul]
  rw [this]
  positivity

/-! ### The size of the terms -/

/-- `|t_k(x)| = 2 (2k−2)! ζ(2k) / ((2π)^(2k) x^(2k−1))` for `k ≥ 1`, `x > 0`. -/
theorem abs_stirlingTerm_eq {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    |stirlingTerm k x|
      = 2 * (2 * k - 2).factorial * zetaReal (2 * k) / ((2 * π) ^ (2 * k) * x ^ (2 * k - 1)) := by
  unfold stirlingTerm
  rw [abs_div, bernoulli_two_mul_eq_zeta hk, abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by positivity : (0 : ℝ) < (2 * k).factorial),
    abs_of_pos (lt_of_lt_of_le one_pos (one_le_zetaReal_two_mul hk)),
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ (2 * k))]
  have hk2 : (2 : ℝ) * k * (2 * k - 1) * x ^ (2 * k - 1) > 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) < 2 * k - 1 := by linarith
    positivity
  rw [abs_of_pos hk2]
  -- `(2k)! = 2k (2k−1) (2k−2)!`
  have hfac : ((2 * k).factorial : ℝ) = 2 * k * (2 * k - 1) * (2 * k - 2).factorial := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      show 2 * j + 1 + 1 - 2 = 2 * j by omega]
    push_cast
    ring
  rw [hfac]
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : (0 : ℝ) < 2 * k - 1 := by linarith
  field_simp

/-- The ratio of successive term magnitudes is `(2k)(2k−1) ζ(2k+2) / (ζ(2k) (2πx)²)`: between
`(2k)(2k−1) / (2 (2πx)²)` and `2 (2k)(2k−1) / (2πx)²`, the text's `≈ (k/(πx))²`. -/
theorem stirlingTerm_ratio_bounds {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    (2 * k) * (2 * k - 1) / (2 * (2 * π * x) ^ 2) * |stirlingTerm k x| ≤ |stirlingTerm (k + 1) x| ∧
      |stirlingTerm (k + 1) x|
        ≤ 2 * (2 * k) * (2 * k - 1) / (2 * π * x) ^ 2 * |stirlingTerm k x| := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2k : (0 : ℝ) < 2 * k - 1 := by linarith
  have hfac : ((2 * (k + 1) - 2).factorial : ℝ)
      = 2 * k * (2 * k - 1) * (2 * k - 2).factorial := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1 + 1) - 2 = 2 * j + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ,
      show 2 * (j + 1) - 2 = 2 * j by omega]
    push_cast
    ring
  have hpow : (2 * π) ^ (2 * (k + 1)) = (2 * π) ^ (2 * k) * (2 * π) ^ 2 := by
    rw [← pow_add]; congr 1
  have hxpow : x ^ (2 * (k + 1) - 1) = x ^ (2 * k - 1) * x ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hz1 := one_le_zetaReal_two_mul hk
  have hz1' := one_le_zetaReal_two_mul (k := k + 1) (by omega)
  have hz2 := zetaReal_two_mul_le hk
  have hz2' := zetaReal_two_mul_le (k := k + 1) (by omega)
  have hπ6 : π ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  push_cast at hz1' hz2'
  rw [abs_stirlingTerm_eq hk hx, abs_stirlingTerm_eq (by omega) hx, hfac, hpow, hxpow]
  push_cast
  have hf : (0 : ℝ) < (2 * k - 2).factorial := by positivity
  have hQ : 0 ≤ 4 * (k : ℝ) * (2 * k - 1) * (2 * k - 2).factorial * (2 * π) ^ (2 * k)
      * x ^ (2 * k - 1) * (2 * π) ^ 2 * x ^ 2 := by positivity
  constructor
  · have hζ : zetaReal (2 * k) ≤ 2 * zetaReal (2 * (k + 1)) := by linarith
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hζ hQ]
  · have hζ : zetaReal (2 * (k + 1)) ≤ 2 * zetaReal (2 * k) := by linarith
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hζ hQ]

/-- The terms of (4.38) start to grow once `2 (2πx)² < (2k)(2k−1)` (about `k > 2.8 πx`). -/
theorem abs_stirlingTerm_lt_succ {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x)
    (h : 2 * (2 * π * x) ^ 2 < (2 * k) * (2 * k - 1)) :
    |stirlingTerm k x| < |stirlingTerm (k + 1) x| := by
  have hb := (stirlingTerm_ratio_bounds hk hx).1
  have hpos : 0 < |stirlingTerm k x| := by
    rw [abs_stirlingTerm_eq hk hx]
    have := one_le_zetaReal_two_mul hk
    positivity
  have hr : 1 < (2 * k) * (2 * k - 1) / (2 * (2 * π * x) ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  nlinarith

/-- `y ln y ≥ −1/e` for `y > 0`. -/
theorem mul_log_ge_neg_inv_exp {y : ℝ} (hy : 0 < y) : -(exp 1)⁻¹ ≤ y * Real.log y := by
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (exp 1 * y)⁻¹)
  rw [Real.log_inv, Real.log_mul (exp_pos 1).ne' hy.ne', Real.log_exp] at h
  have he : 0 < exp 1 := exp_pos 1
  have : -(1 + Real.log y) ≤ (exp 1 * y)⁻¹ - 1 := h
  have h2 : -(1 + Real.log y) * (exp 1 * y) ≤ ((exp 1 * y)⁻¹ - 1) * (exp 1 * y) :=
    mul_le_mul_of_nonneg_right this (by positivity)
  rw [sub_mul, inv_mul_cancel₀ (by positivity)] at h2
  rw [show -(exp 1)⁻¹ = (-1) / exp 1 by ring, div_le_iff₀ he]
  linarith

/-- `(u / c)^u ≥ e^(−c/e)` for `u : ℕ` and `c > 0`: the minimum of `u ↦ (u/c)^u`. -/
theorem div_pow_self_ge {c : ℝ} (hc : 0 < c) (u : ℕ) : exp (-(c / exp 1)) ≤ ((u : ℝ) / c) ^ u := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · simp only [Nat.cast_zero, zero_div, pow_zero]
    exact exp_le_one_iff.mpr (by have := div_pos hc (exp_pos 1); linarith)
  · have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
    have hy : 0 < (u : ℝ) / c := by positivity
    rw [← Real.exp_log (pow_pos hy u), Real.log_pow]
    apply exp_le_exp.mpr
    have h := mul_log_ge_neg_inv_exp hy
    have : (u : ℝ) * Real.log (u / c) = c * ((u / c) * Real.log (u / c)) := by field_simp
    rw [this]
    have hc' : -(c / exp 1) = c * (-(exp 1)⁻¹) := by ring
    rw [hc']
    exact mul_le_mul_of_nonneg_left h hc.le

/-- Every term of the divergent series is at least `e^(−2πx) / (2π² x)`: the smallest term, and
with it the accuracy attainable from (4.38) without shifting the argument, is about `2πx` nats. -/
theorem abs_stirlingTerm_ge {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    exp (-(2 * π * x)) / (2 * π ^ 2 * x) ≤ |stirlingTerm k x| := by
  rw [abs_stirlingTerm_eq hk hx]
  have hz := one_le_zetaReal_two_mul hk
  set u := 2 * k - 2 with hu
  have hku : 2 * k = u + 2 := by omega
  -- Stirling's lower bound `(u)! ≥ (u/e)^u`
  have hfac : ((u : ℝ) / exp 1) ^ u ≤ u.factorial := by
    have h := Stirling.le_factorial_stirling u
    rcases Nat.eq_zero_or_pos u with hu0 | hu0
    · rw [hu0]; simp
    · have : 1 ≤ Real.sqrt (2 * π * u) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        have : (1 : ℝ) ≤ u := by exact_mod_cast hu0
        nlinarith [Real.pi_gt_three]
      nlinarith [pow_pos (div_pos (by exact_mod_cast hu0 : (0:ℝ) < u) (exp_pos 1)) u]
  have hmin := div_pow_self_ge (c := 2 * π * exp 1 * x) (by positivity) u
  have hexp : exp (-(2 * π * x)) = exp (-(2 * π * exp 1 * x / exp 1)) := by
    congr 1; field_simp
  have hpowc : ((u : ℝ) / (2 * π * exp 1 * x)) ^ u
      = ((u : ℝ) / exp 1) ^ u / ((2 * π) ^ u * x ^ u) := by
    rw [div_pow, div_pow, mul_pow, mul_pow]
    field_simp
  rw [hku, show u + 2 - 1 = u + 1 by omega]
  have hA : 0 < (2 * π) ^ (u + 2) * x ^ (u + 1) := by positivity
  rw [div_le_div_iff₀ (by positivity) hA]
  calc exp (-(2 * π * x)) * ((2 * π) ^ (u + 2) * x ^ (u + 1))
      ≤ ((u : ℝ) / exp 1) ^ u / ((2 * π) ^ u * x ^ u) * ((2 * π) ^ (u + 2) * x ^ (u + 1)) := by
        rw [hexp, ← hpowc]; gcongr
    _ = ((u : ℝ) / exp 1) ^ u * (2 * (2 * π ^ 2 * x)) := by
        rw [pow_add, pow_succ]
        field_simp
        ring
    _ ≤ (u.factorial : ℝ) * (2 * (2 * π ^ 2 * x)) := by gcongr
    _ ≤ 2 * u.factorial * zetaReal (2 * k) * (2 * π ^ 2 * x) := by
        have : 0 ≤ 2 * (u.factorial : ℝ) * (2 * π ^ 2 * x) := by positivity
        nlinarith

/-! ### Shifting the argument -/

/-- `ln Γ(x) = ln Γ(x + δ) − ∑_{i<δ} ln(x + i)` for `x > 0`, from `Γ(x + 1) = x Γ(x)`. -/
theorem log_Gamma_eq_log_Gamma_add_sub {x : ℝ} (hx : 0 < x) (δ : ℕ) :
    Real.log (Real.Gamma x) = Real.log (Real.Gamma (x + δ)) - ∑ i ∈ range δ, Real.log (x + i) := by
  rw [Gamma_add_nat hx δ, Real.log_mul (Gamma_pos_of_pos hx).ne', Real.log_prod]
  · ring
  · intro i _
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    exact (by linarith : (0 : ℝ) < x + i).ne'
  · exact (Finset.prod_pos fun i _ => by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith).ne'

end BZ

end Azurite
