/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.LogGammaStirling
import Mathlib.NumberTheory.ZetaValues

/-!
# A bound for the terms of Stirling's series

From `ζ(2k) ≤ ζ(2) ≤ 2` and Euler's formula for `ζ(2k)`: the coefficient
`a_k = |B_{2k}| / (2k (2k−1))` is at most `4 (2k−2)! / (2π)^(2k)`
(`stirlingCoeffT_le`), hence the term `a_k / y^(2k−1)` is at most `(9/10)^(2k−1)` as long as
`k ≤ 2.7 y` (`stirlingTerm_le`).  Crude, but all that the convergence of the bracket of `ln Γ`
needs.
-/

namespace Azurite

open Finset Nat

theorem zeta_two_mul_le (k : ℕ) (hk : k ≠ 0) :
    (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) * bernoulli (2 * k)
      / (2 * k)! ≤ 2 := by
  have h1 := hasSum_zeta_nat hk
  have h2 := hasSum_zeta_two
  have hle := hasSum_le (fun n : ℕ => ?_) h1 h2
  · have hπ : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_gt_three, Real.pi_lt_d2]
    linarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hk]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * k) := pow_le_pow_right₀ hn1 (by omega)
      exact one_div_le_one_div_of_le (by positivity) hpow

/-- `a_{j+1} ≤ 4 (2j)! / 6^(2j+2)`. -/
theorem stirlingCoeffT_le (j : ℕ) :
    stirlingCoeffT (j + 1) ≤ 4 * ((2 * j)! : ℝ) / 6 ^ (2 * j + 2) := by
  have hz := zeta_two_mul_le (j + 1) (Nat.succ_ne_zero j)
  have hb := bernoulli_div_eq_stirlingCoeffT (k := j + 1) (by omega)
  have hc := stirlingCoeffT_pos (k := j + 1) (by omega)
  set c := stirlingCoeffT (j + 1) with hcdef
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast at hb
  have hB : (bernoulli (2 * (j + 1)) : ℝ)
      = (-1) ^ (j + 1 + 1) * c * ((2 * ((j : ℝ) + 1)) * (2 * ((j : ℝ) + 1) - 1)) := by
    have hden : (2 * ((j : ℝ) + 1)) * (2 * ((j : ℝ) + 1) - 1) ≠ 0 := by
      have : (0 : ℝ) < (2 * ((j : ℝ) + 1)) * (2 * ((j : ℝ) + 1) - 1) := by nlinarith
      exact this.ne'
    rw [div_eq_iff hden] at hb
    exact hb
  have hfac : (((2 * (j + 1))! : ℕ) : ℝ)
      = (2 * ((j : ℝ) + 1)) * (2 * ((j : ℝ) + 1) - 1) * ((2 * j)! : ℝ) := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hsign : ((-1 : ℝ) ^ (j + 1 + 1)) * (-1) ^ (j + 1 + 1) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨j + 1 + 1, rfl⟩
  have hfpos : (0 : ℝ) < ((2 * j)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hπpos := Real.pi_pos
  have hZ : (-1 : ℝ) ^ (j + 1 + 1) * (2 : ℝ) ^ (2 * (j + 1) - 1) * Real.pi ^ (2 * (j + 1))
      * bernoulli (2 * (j + 1)) / (2 * (j + 1))!
      = (2 : ℝ) ^ (2 * j + 1) * Real.pi ^ (2 * j + 2) * c / ((2 * j)! : ℝ) := by
    rw [hB, hfac, show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) = 2 * j + 2 by ring]
    have hden : (2 * ((j : ℝ) + 1)) * (2 * ((j : ℝ) + 1) - 1) ≠ 0 := by
      have : (0 : ℝ) < (2 * ((j : ℝ) + 1)) * (2 * ((j : ℝ) + 1) - 1) := by nlinarith
      exact this.ne'
    generalize (2 * ((j : ℝ) + 1)) * (2 * ((j : ℝ) + 1) - 1) = D at hden ⊢
    have e : (-1 : ℝ) ^ (j + 1 + 1) * (2 : ℝ) ^ (2 * j + 1) * Real.pi ^ (2 * j + 2)
        * ((-1) ^ (j + 1 + 1) * c * D)
        = ((-1 : ℝ) ^ (j + 1 + 1) * (-1) ^ (j + 1 + 1))
          * ((2 : ℝ) ^ (2 * j + 1) * Real.pi ^ (2 * j + 2) * c) * D := by ring
    rw [e, hsign, one_mul, mul_comm D, mul_div_mul_right _ _ hden]
  rw [hZ, div_le_iff₀ hfpos] at hz
  -- `c ≤ 2 (2j)! / (2^(2j+1) π^(2j+2)) ≤ 4 (2j)! / 6^(2j+2)`
  have h6 : (6 : ℝ) ^ (2 * j + 2) ≤ 2 * ((2 : ℝ) ^ (2 * j + 1) * Real.pi ^ (2 * j + 2)) := by
    have e : (2 : ℝ) * ((2 : ℝ) ^ (2 * j + 1) * Real.pi ^ (2 * j + 2))
        = (2 * Real.pi) ^ (2 * j + 2) := by
      rw [mul_pow]
      ring
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) _
  rw [le_div_iff₀ (by positivity)]
  have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * j + 1) * Real.pi ^ (2 * j + 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h6 hc.le]

/-- **The terms of Stirling's series are small while `k ≤ 2.7 y`.** -/
theorem stirlingTerm_le {k : ℕ} (hk : 1 ≤ k) {y : ℝ} (hy : 0 < y) (hky : (k : ℝ) ≤ 27 / 10 * y) :
    stirlingCoeffT k / y ^ (2 * k - 1) ≤ (9 / 10 : ℝ) ^ (2 * k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
  have hc := stirlingCoeffT_le j
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast at hky
  set r : ℝ := ((j : ℝ) + 1) / (3 * y) with hr
  have hr0 : 0 < r := by positivity
  have hr9 : r ≤ 9 / 10 := by
    rw [hr, div_le_iff₀ (by positivity)]
    linarith
  -- `(2j)! ≤ (2j+2)^(2j)`
  have hfac : ((2 * j)! : ℝ) ≤ (2 * (j : ℝ) + 2) ^ (2 * j) := by
    have h1 : (2 * j)! ≤ (2 * j) ^ (2 * j) := Nat.factorial_le_pow _
    have h2 : (2 * j) ^ (2 * j) ≤ (2 * j + 2) ^ (2 * j) := Nat.pow_le_pow_left (by omega) _
    exact_mod_cast h1.trans h2
  have hy' : (0 : ℝ) < y ^ (2 * j + 1) := by positivity
  calc stirlingCoeffT (j + 1) / y ^ (2 * j + 1)
      ≤ (4 * (2 * (j : ℝ) + 2) ^ (2 * j) / 6 ^ (2 * j + 2)) / y ^ (2 * j + 1) := by
        refine div_le_div_of_nonneg_right (hc.trans ?_) hy'.le
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by norm_num))
          (by positivity)
    _ = r ^ (2 * j) / (9 * y) := by
        have e2 : (2 * (j : ℝ) + 2) ^ (2 * j) = 2 ^ (2 * j) * ((j : ℝ) + 1) ^ (2 * j) := by
          rw [← mul_pow]
          ring_nf
        have e6 : (6 : ℝ) ^ (2 * j + 2) = 36 * (2 ^ (2 * j) * 3 ^ (2 * j)) := by
          rw [pow_add, show (6 : ℝ) = 2 * 3 by norm_num, mul_pow]
          ring
        rw [hr, div_pow, mul_pow, e2, e6]
        field_simp
        ring
    _ ≤ r ^ (2 * j) * r := by
        rw [div_le_iff₀ (by positivity)]
        have : (1 : ℝ) ≤ r * (9 * y) := by
          rw [hr]
          field_simp
          linarith
        nlinarith [pow_pos hr0 (2 * j)]
    _ = r ^ (2 * j + 1) := by ring
    _ ≤ (9 / 10 : ℝ) ^ (2 * j + 1) := pow_le_pow_left₀ hr0.le hr9 _

end Azurite
