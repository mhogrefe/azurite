/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.EllipticIntegrals

/-!
# Brent–Zimmermann §4.8.2: First AGM algorithm for the logarithm

From (4.68), (4.69), (4.70): `(π/2)/AGM(1, k) = ln(4/k) (1 + O(k²))` (4.71), so for large
`x = 4/k`, `ln x = (π/2)/AGM(1, 4/x) (1 + O(1/x²))`; with `x ≥ 2^(n/2)` this gives `ln x` to
precision `n`, in about `2 lg n` AGM iterations when `x ∈ [2^(n/2), 2^n]`.  The constant `π` is
needed (Brent–Salamin, based on the Legendre relation `E K' + E' K − K K' = π/2` (4.72)).
Argument expansion: `ln(2^ℓ x) = ℓ ln 2 + ln x`, or `ln(x^(2^ℓ)) = 2^ℓ ln x` (with `x = 2` this
gives `ln 2`).  A rigorous error bound is `|(π/2)/AGM(1,k) − ln(4/k)| ≤ 4k² (8 − ln k)` for
`k ∈ (0, 1]` (4.73), sharpened to `0.37 k² (2.4 − ln k)` on `(0, 0.5]`; the `O(k² |ln k|)` error
is a nuisance that the exact theta-function formula (next subsections) avoids.

What is formalized:

* `agmLog x := (π/2)/AGM(1, 4/x)`, the AGM approximation to `ln x`; exactly
  `agmLog x = K'(4/x) = K(√(1 − 16/x²))` for `x ≥ 4` (`agmLog_eq_ellipticK`) and
  `agmLog x = ∫_0^{π/2} dθ/√(cos²θ + (4/x)² sin²θ)` for `x > 0` (`agmLog_eq_integral`), by
  Gauss's theorem.
* Argument expansion: `log_two_pow_mul`, `log_pow_two_pow`, and the error transport
  `abs_agmLog_two_pow_mul_sub` (shifting by `2^ℓ` keeps the error) and `abs_agmLog_pow_sub`
  (squaring `ℓ` times divides the error by `2^ℓ`).
* The iteration count: the ratio `r_j = b_j/a_j` satisfies `r_{j+1} ≥ √r_j` (`agm_ratio_succ`),
  so `r_j ≥ (b/a)^(1/2^j)` (`agm_ratio_rpow_le`); for `AGM(1, k)` with `k ≥ 2^(−n)` this puts
  the iteration into the quadratic regime after `⌈lg n⌉ + 1` steps, and `agm_log_iterations`
  gives `a_j − b_j ≤ 8/2^n` at `j = 2 ⌈lg n⌉ + 1`: the "about `2 lg n` iterations" of the text.

The asymptotic (4.71) and the rigorous bound (4.73) are proven in `AGMLogBound.lean`
(`pi_div_AGM_eq_log_mul`, `abs_pi_div_AGM_sub_log_le`, `abs_agmLog_sub_log_le`).  Not formalized:
the Legendre relation (4.72), Brent–Salamin, Exercise 4.44.
-/

namespace Azurite

namespace BZ

open Real

/-! ### The AGM approximation to the logarithm -/

/-- `(π/2)/AGM(1, 4/x)`, the AGM approximation to `ln x` (exact up to `O(1/x²)`). -/
noncomputable def agmLog (x : ℝ) : ℝ := (π / 2) / AGM 1 (4 / x)

variable {x : ℝ}

/-- `agmLog x = K'(4/x)` exactly, for `x ≥ 4`. -/
theorem agmLog_eq_ellipticK (hx : 4 ≤ x) : agmLog x = ellipticK (Real.sqrt (1 - (4 / x) ^ 2)) := by
  have hx0 : 0 < x := by linarith
  have hk : 0 < 4 / x := by positivity
  have hk1 : 4 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  have h := one_div_AGM_one hk hk1
  have hAGM : 0 < AGM 1 (4 / x) := lt_of_lt_of_le (lt_min one_pos hk) (min_le_AGM one_pos hk)
  unfold agmLog
  rw [div_eq_mul_one_div, h]
  field_simp

/-- `agmLog x = ∫_0^{π/2} dθ/√(cos²θ + (4/x)² sin²θ)` for `x > 0`. -/
theorem agmLog_eq_integral (hx : 0 < x) :
    agmLog x = ∫ θ in (0 : ℝ)..(π / 2),
      (Real.sqrt (Real.cos θ ^ 2 + (4 / x) ^ 2 * Real.sin θ ^ 2))⁻¹ := by
  have h := integral_inv_sqrt_eq_pi_div_AGM one_pos (by positivity : (0 : ℝ) < 4 / x)
  simp only [one_pow, one_mul] at h
  rw [h, agmLog, div_div]

/-! ### Argument expansion -/

theorem log_two_pow_mul (ℓ : ℕ) (hx : 0 < x) :
    Real.log (2 ^ ℓ * x) = ℓ * Real.log 2 + Real.log x := by
  rw [Real.log_mul (by positivity) hx.ne', Real.log_pow]

theorem log_pow_two_pow (ℓ : ℕ) : Real.log (x ^ 2 ^ ℓ) = 2 ^ ℓ * Real.log x := by
  rw [Real.log_pow]; push_cast; ring

/-- Shifting the argument by `2^ℓ`: the error of `agmLog` is unchanged, `ℓ ln 2` is subtracted. -/
theorem abs_agmLog_two_pow_mul_sub (ℓ : ℕ) (hx : 0 < x) {ε : ℝ}
    (h : |agmLog (2 ^ ℓ * x) - Real.log (2 ^ ℓ * x)| ≤ ε) :
    |agmLog (2 ^ ℓ * x) - ℓ * Real.log 2 - Real.log x| ≤ ε := by
  rw [log_two_pow_mul ℓ hx] at h
  convert h using 2
  ring

/-- Squaring `ℓ` times: `ln x = agmLog(x^(2^ℓ))/2^ℓ`, with the error divided by `2^ℓ`. -/
theorem abs_agmLog_pow_sub (ℓ : ℕ) {ε : ℝ}
    (h : |agmLog (x ^ 2 ^ ℓ) - Real.log (x ^ 2 ^ ℓ)| ≤ ε) :
    |agmLog (x ^ 2 ^ ℓ) / 2 ^ ℓ - Real.log x| ≤ ε / 2 ^ ℓ := by
  rw [log_pow_two_pow ℓ] at h
  rw [show agmLog (x ^ 2 ^ ℓ) / 2 ^ ℓ - Real.log x
      = (agmLog (x ^ 2 ^ ℓ) - 2 ^ ℓ * Real.log x) / 2 ^ ℓ by field_simp,
    abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ ℓ)]
  exact div_le_div_of_nonneg_right h (by positivity)

/-! ### The number of iterations for `AGM(1, k)`, `k` small -/

variable {a b : ℝ}

/-- The ratio `b_j/a_j` at least square-roots at each step: `√(b_j/a_j) ≤ b_{j+1}/a_{j+1}`. -/
theorem agm_ratio_succ (ha : 0 < a) (hb : 0 < b) (j : ℕ) (hle : agmB a b j ≤ agmA a b j) :
    Real.sqrt (agmB a b j / agmA a b j) ≤ agmB a b (j + 1) / agmA a b (j + 1) := by
  obtain ⟨hA, hB⟩ := agm_pos ha hb j
  rw [agmA_succ, agmB_succ, Real.sqrt_div hB.le, Real.sqrt_mul hA.le,
    div_le_div_iff₀ (Real.sqrt_pos.mpr hA) (by positivity)]
  have hsA := Real.sq_sqrt hA.le
  have hsB := Real.sqrt_nonneg (agmB a b j)
  nlinarith [mul_le_mul_of_nonneg_left hle hsB]

/-- `(b/a)^(1/2^j) ≤ b_j/a_j` for `b ≤ a`. -/
theorem agm_ratio_rpow_le (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (j : ℕ) :
    (b / a) ^ ((1 / 2 : ℝ) ^ j) ≤ agmB a b j / agmA a b j := by
  induction j with
  | zero => simp [agmA_zero, agmB_zero]
  | succ j ih =>
    have hle : agmB a b j ≤ agmA a b j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact hab
      · exact agmB_le_agmA ha hb hj
    calc (b / a) ^ ((1 / 2 : ℝ) ^ (j + 1))
        = Real.sqrt ((b / a) ^ ((1 / 2 : ℝ) ^ j)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), pow_succ]
      _ ≤ Real.sqrt (agmB a b j / agmA a b j) := Real.sqrt_le_sqrt ih
      _ ≤ agmB a b (j + 1) / agmA a b (j + 1) := agm_ratio_succ ha hb j hle

/-- Shifting the start: the AGM sequence of `(a_m, b_m)` is the tail of that of `(a, b)`. -/
theorem agmSeq_shift (a b : ℝ) (m : ℕ) :
    ∀ j, agmSeq (agmA a b m) (agmB a b m) j = agmSeq a b (j + m) := by
  intro j
  induction j with
  | zero => rw [zero_add]; exact Prod.ext rfl rfl
  | succ j ih =>
    show agmStep _ = agmSeq a b (j + 1 + m)
    rw [ih, show j + 1 + m = j + m + 1 by omega]
    rfl

/-- `a_j ≤ 1` for `j ≥ 1` when starting from `(1, k)` with `k ≤ 1`. -/
theorem agmA_one_le {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) {j : ℕ} (hj : 1 ≤ j) : agmA 1 k j ≤ 1 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  calc agmA 1 k (j + 1) ≤ agmA 1 k (0 + 1) := agmA_antitone one_pos hk (Nat.zero_le j)
    _ = (1 + k) / 2 := by rw [agmA_succ, agmA_zero, agmB_zero]
    _ ≤ 1 := by linarith

/-- For `AGM(1, k)` with `2^(−n) ≤ k ≤ 1`: after `m + 1` steps with `n ≤ 2^m`, the ratio
`b/a` is at least `1/2`, so the iteration is in its quadratic regime. -/
theorem agm_ratio_one_half_le {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) {n m : ℕ} (hn : n ≤ 2 ^ m)
    (hkn : (1 / 2 : ℝ) ^ n ≤ k) : 1 / 2 ≤ agmB 1 k (m + 1) / agmA 1 k (m + 1) := by
  have h := agm_ratio_rpow_le one_pos hk hk1 (m + 1)
  rw [div_one] at h
  set e : ℝ := (1 / 2 : ℝ) ^ (m + 1) with he
  refine le_trans ?_ h
  have he0 : 0 ≤ e := by positivity
  have hne : (n : ℝ) * e ≤ 1 := by
    have h2 : (n : ℝ) ≤ 2 ^ (m + 1) := by
      have : (n : ℝ) ≤ 2 ^ m := by exact_mod_cast hn
      have : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)
      linarith
    rw [he, one_div_pow, mul_one_div, div_le_one (by positivity)]
    exact h2
  calc (1 / 2 : ℝ) = (1 / 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (1 / 2 : ℝ) ^ ((n : ℝ) * e) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hne
    _ = ((1 / 2 : ℝ) ^ n) ^ e := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    _ ≤ k ^ e := Real.rpow_le_rpow (by positivity) hkn he0

/-- The iteration count for `AGM(1, k)`, `2^(−n) ≤ k ≤ 1`: after `2 ⌈lg n⌉ + 1` steps the gap
is at most `8/2^n` — "about `2 lg n` iterations" for `x = 4/k ∈ [2^(n/2), 2^n]`. -/
theorem agm_log_iterations {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (n : ℕ)
    (hkn : (1 / 2 : ℝ) ^ n ≤ k) :
    agmA 1 k (2 * Nat.clog 2 n + 1) - agmB 1 k (2 * Nat.clog 2 n + 1) ≤ 8 / 2 ^ n := by
  set m := Nat.clog 2 n with hm
  have hn : n ≤ 2 ^ m := Nat.le_pow_clog one_lt_two n
  obtain ⟨hA, hB⟩ := agm_pos one_pos hk m
  -- restart the iteration at `(a_m, b_m)`
  have hshiftA : ∀ j, agmA (agmA 1 k m) (agmB 1 k m) j = agmA 1 k (j + m) := fun j =>
    congrArg Prod.fst (agmSeq_shift 1 k m j)
  have hshiftB : ∀ j, agmB (agmA 1 k m) (agmB 1 k m) j = agmB 1 k (j + m) := fun j =>
    congrArg Prod.snd (agmSeq_shift 1 k m j)
  have hratio := agm_ratio_one_half_le hk hk1 hn hkn
  obtain ⟨hA1, hB1⟩ := agm_pos one_pos hk (m + 1)
  have hcond : agmA (agmA 1 k m) (agmB 1 k m) 1 - agmB (agmA 1 k m) (agmB 1 k m) 1
      ≤ 4 * agmB (agmA 1 k m) (agmB 1 k m) 1 := by
    rw [hshiftA, hshiftB, show 1 + m = m + 1 by ring]
    rw [le_div_iff₀ hA1] at hratio
    linarith
  have hgap := agm_gap_le_two_pow hA hB hcond (j := m) (n := n) hn
  rw [hshiftA, hshiftB, hshiftB, show m + 1 + m = 2 * m + 1 by ring,
    show 1 + m = m + 1 by ring] at hgap
  have hb1 : agmB 1 k (m + 1) ≤ 1 :=
    (agmB_le_agmA one_pos hk (by omega)).trans (agmA_one_le hk hk1 (by omega))
  calc agmA 1 k (2 * m + 1) - agmB 1 k (2 * m + 1) ≤ 8 * agmB 1 k (m + 1) / 2 ^ n := hgap
    _ ≤ 8 * 1 / 2 ^ n := by gcongr
    _ = 8 / 2 ^ n := by ring

end BZ

end Azurite
