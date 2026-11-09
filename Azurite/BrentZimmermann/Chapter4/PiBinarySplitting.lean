/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed

/-!
## `π` by Machin's formula and binary splitting (MCA §4.9.1)

`π = 16 arctan(1/5) − 4 arctan(1/239)` (Machin; `pi_eq_machin`, from Mathlib's
`Real.four_mul_arctan_inv_5_sub_arctan_inv_239`), and `arctan(1/q) = ∑_k (−1)^k/((2k+1) q^(2k+1))`
(DLMF 4.24.3; `Real.hasSum_arctan`).  The alternating series is summed by **pairs**
`atanPair q j = atanTerm q (2j) − atanTerm q (2j+1) > 0`: the first `N` pairs are the first `2N`
terms (`sum_atanPair_eq`), and by the alternating-series bounds
`∑_{j<N} atanPair q j ≤ arctan(1/q) ≤ ∑_{j<N} atanPair q j + atanTerm q (2N)`
(`arctan_inv_bounds`), with `atanTerm q (2N) ≤ (1/2)^(w+5)` once `(4N+1) b ≥ w + 5` for
`2^b ≤ q` (`atanTerm_le_half_pow`).  The exact pair sums are computed by binary splitting in
`Azurite/AzNat/AtanhSplit.lean` (`atanNumDen`), and the float bracket of `π` is
`Azurite/AzFloat/PiBracket.lean` (`piMachinBracket`).
-/

namespace Azurite.BZ

open Finset

variable {q : ℝ}

/-- The absolute value of the `k`-th term of the series of `arctan(1/q)`:
`1/((2k+1) q^(2k+1))`. -/
noncomputable def atanTerm (q : ℝ) (k : ℕ) : ℝ := 1 / ((2 * k + 1) * q ^ (2 * k + 1))

/-- Two consecutive terms of the series of `arctan(1/q)`, a positive quantity. -/
noncomputable def atanPair (q : ℝ) (j : ℕ) : ℝ := atanTerm q (2 * j) - atanTerm q (2 * j + 1)

theorem atanTerm_pos (hq : 0 < q) (k : ℕ) : 0 < atanTerm q k := by unfold atanTerm; positivity

theorem atanTerm_antitone (hq : 1 ≤ q) : Antitone (atanTerm q) := by
  refine antitone_nat_of_succ_le fun k => ?_
  unfold atanTerm
  have hq0 : 0 < q := by linarith
  apply one_div_le_one_div_of_le (by positivity)
  have h1 : (2 * (k : ℝ) + 1) ≤ 2 * ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  have h2 : q ^ (2 * k + 1) ≤ q ^ (2 * (k + 1) + 1) := pow_le_pow_right₀ hq (by omega)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem atanPair_pos (hq : 1 ≤ q) (j : ℕ) : 0 ≤ atanPair q j := by
  unfold atanPair
  have := atanTerm_antitone hq (show 2 * j ≤ 2 * j + 1 by omega)
  linarith

/-- The first `N` pairs are the first `2N` terms of the alternating series. -/
theorem sum_atanPair_eq (q : ℝ) (N : ℕ) :
    ∑ j ∈ range N, atanPair q j = ∑ k ∈ range (2 * N), (-1 : ℝ) ^ k * atanTerm q k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ,
      sum_range_succ, atanPair, pow_succ, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul, mul_neg, mul_one]
    ring

/-- **DLMF 4.24.3** at `1/q`: `arctan(1/q) = ∑_k (−1)^k/((2k+1) q^(2k+1))` for `q > 1`. -/
theorem hasSum_atanTerm (hq : 1 < q) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * atanTerm q k) (Real.arctan (1 / q)) := by
  have hq0 : 0 < q := by linarith
  have h : ‖(1 / q : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one hq0]
    exact hq
  have := Real.hasSum_arctan h
  convert this using 1
  funext k
  unfold atanTerm
  rw [one_div_pow]
  push_cast
  have : (q : ℝ) ^ (2 * k + 1) ≠ 0 := by positivity
  field_simp

/-- The alternating-series bounds: `N` pairs lie below `arctan(1/q)`, and within the next term. -/
theorem arctan_inv_bounds (hq : 1 < q) (N : ℕ) :
    ∑ j ∈ range N, atanPair q j ≤ Real.arctan (1 / q) ∧
      Real.arctan (1 / q) ≤ ∑ j ∈ range N, atanPair q j + atanTerm q (2 * N) := by
  have hs := (hasSum_atanTerm hq).tendsto_sum_nat
  have hanti := atanTerm_antitone hq.le
  constructor
  · rw [sum_atanPair_eq]
    exact hanti.alternating_series_le_tendsto hs N
  · have h := hanti.tendsto_le_alternating_series hs N
    rw [sum_range_succ, ← sum_atanPair_eq, pow_mul, neg_one_sq, one_pow, one_mul] at h
    exact h

theorem atanTerm_le (hq : 1 ≤ q) (N : ℕ) : atanTerm q N ≤ (1 / q) ^ (2 * N + 1) := by
  unfold atanTerm
  rw [one_div_pow]
  apply one_div_le_one_div_of_le (by positivity)
  have : (1 : ℝ) ≤ 2 * N + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  nlinarith [pow_pos (by linarith : (0 : ℝ) < q) (2 * N + 1)]

/-- The tail bound as a power of two: `atanTerm q (2N) ≤ 2^(−w−5)` when `2^b ≤ q` and
`(4N+1) b ≥ w + 5`. -/
theorem atanTerm_le_half_pow {q b N w : ℕ} (hq : 2 ^ b ≤ q) (h : w + 5 ≤ (4 * N + 1) * b) :
    atanTerm q (2 * N) ≤ (1 / 2 : ℝ) ^ (w + 5) := by
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    exact_mod_cast this.trans hq
  have hqr : (2 : ℝ) ^ b ≤ q := by exact_mod_cast hq
  refine (atanTerm_le hq1 (2 * N)).trans ?_
  calc (1 / (q : ℝ)) ^ (2 * (2 * N) + 1) ≤ (1 / (2 : ℝ) ^ b) ^ (2 * (2 * N) + 1) := by
        gcongr
    _ = (1 / 2 : ℝ) ^ ((4 * N + 1) * b) := by
        rw [one_div_pow, ← pow_mul, mul_comm, one_div_pow, show 2 * (2 * N) + 1 = 4 * N + 1 by ring]
    _ ≤ (1 / 2 : ℝ) ^ (w + 5) := pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- **Machin's formula**: `π = 16 arctan(1/5) − 4 arctan(1/239)`. -/
theorem pi_eq_machin : Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
  have := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  rw [one_div, one_div]
  linarith

end Azurite.BZ
