/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.EllipticEAGM
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Brent–Zimmermann §4.8.2: Salamin's formula for `π`

The Brent–Salamin (Gauss–Legendre) algorithm rests on Salamin's formula: with the AGM
iteration `(a_j, b_j)` started at `(1, 1/√2)` and `c_j² = a_j² − b_j²`,

  `π = 4 AGM(1, 1/√2)² / (1 − ∑_{j≥1} 2^(j+1) c_j²)`                      (`salamin_formula`).

Proof: at `k = k' = 1/√2`, Gauss's formula for `E` (`ellipticE_eq_AGM_sum`) gives
`E = (1 − S) K` with `S = ∑_{j≥0} 2^(j−1) c_j² = 1/4 + T/4`, `T = ∑_{j≥1} 2^(j+1) c_j²`
(`c_0² = 1/2`); the Legendre relation `2EK − K² = π/2` (`legendre_relation_sqrt_half`) becomes
`K² (1 − T)/2 = π/2`; and Gauss's theorem `K = π/(2 AGM)` (`ellipticK_salaminB0`) turns this
into `π (1 − T) = 4 AGM²` (`salamin_identity`), whence the denominator is positive
(`salamin_denominator_pos`) and the formula follows.

Also here: `agmCsq a b j = a_j² − b_j²` with the cancellation-free form
`c_{j+1} = (a_j − b_j)/2` (`agmCsq_succ`), the starting value `salaminB0 = 1/√2` and its facts,
and `summable_salaminSum`.

**The iterate and its error bound.**  With `s_N = 1/2 − ∑_{j=1}^{N} 2^j c_j²` (`salaminS`,
recurrence `s_{N+1} = s_N − 2^(N+1)((a_N − b_N)/2)²`, `salaminS_succ`) the Brent–Salamin
iterate is `π_N = 2 a_{N+1}²/s_N` (`salaminApprox`).  Writing `s_N = s_∞ + r_N` with
`s_∞ = (1 − T)/2 = 2 AGM²/π > 1/3` (`salaminS_eq`, `salaminS_limit_gt`,
`pi_eq_div_salaminS_limit`) and the tail `r_N = ∑_{j≥N} 2^(j+1) c_{j+1}²` (`salaminTail`), the
quarter-decay of the gap gives `r_N ≤ (4/7) 2^N (a_N − b_N)²` (`salaminTail_le`), and
`a_{N+1}² − AGM² ≤ (3/8)(a_N − b_N)²` from the quadratic gap bound; hence for `N ≥ 1`

  `−(48/7) 2^N (a_N − b_N)² ≤ π_N − π ≤ (9/4)(a_N − b_N)²`
  (`le_salaminApprox_sub_pi`, `salaminApprox_sub_pi_le`),

so `|π_N − π| ≤ 7 · 2^N (a_N − b_N)²` (`abs_salaminApprox_sub_pi_le`): the error is bounded by
a quantity the algorithm computes anyway, which makes a floating-point implementation
self-validating; `π_N → π` (`tendsto_salaminApprox`).

Not formalized (next): the floating-point enclosure of the iteration and the correctly rounded
`π` (`AzFloat`).
-/

namespace Azurite

namespace BZ

open Real Filter Topology

/-! ### `c_j²` along the AGM -/

/-- `c_j² = a_j² − b_j²`. -/
noncomputable def agmCsq (a b : ℝ) (j : ℕ) : ℝ := agmA a b j ^ 2 - agmB a b j ^ 2

variable {a b : ℝ}

/-- The cancellation-free form `c_{j+1} = (a_j − b_j)/2`. -/
theorem agmCsq_succ (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    agmCsq a b (j + 1) = ((agmA a b j - agmB a b j) / 2) ^ 2 := by
  obtain ⟨hA, hB⟩ := agm_pos ha hb j
  rw [agmCsq, agmA_succ, agmB_succ, Real.sq_sqrt (by positivity)]
  ring

/-! ### The starting value `1/√2` -/

/-- The Brent–Salamin starting value `b₀ = 1/√2 = k = k'`. -/
noncomputable def salaminB0 : ℝ := 1 / Real.sqrt 2

theorem salaminB0_pos : 0 < salaminB0 := by unfold salaminB0; positivity

theorem salaminB0_lt_one : salaminB0 < 1 := by
  unfold salaminB0
  rw [div_lt_one (by positivity), Real.lt_sqrt zero_le_one]
  norm_num

theorem salaminB0_sq : salaminB0 ^ 2 = 1 / 2 := by
  unfold salaminB0
  rw [div_pow, one_pow, Real.sq_sqrt zero_le_two]

/-- `1/√2` is its own complementary modulus. -/
theorem sqrt_one_sub_salaminB0_sq : Real.sqrt (1 - salaminB0 ^ 2) = salaminB0 := by
  rw [salaminB0_sq, show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.sqrt_inv, salaminB0, one_div]

/-- Gauss's theorem at `1/√2`: `K(1/√2) = π/(2 AGM(1, 1/√2))`. -/
theorem ellipticK_salaminB0 : ellipticK salaminB0 = π / (2 * AGM 1 salaminB0) := by
  have h := one_div_AGM_one salaminB0_pos salaminB0_lt_one.le
  rw [sqrt_one_sub_salaminB0_sq] at h
  have hM : 0 < AGM 1 salaminB0 := AGM_one_pos salaminB0_pos
  field_simp at h ⊢
  linarith

/-! ### Salamin's formula -/

/-- `T = ∑_{j≥1} 2^(j+1) c_j²` for the AGM started at `(1, 1/√2)` (indexed from `0`). -/
noncomputable def salaminSum : ℝ := ∑' j : ℕ, 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1)

theorem summable_salaminSum :
    Summable fun j : ℕ => 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1) := by
  have h := summable_agm_c_sq one_pos salaminB0_pos salaminB0_lt_one.le
  have h2 := (summable_nat_add_iff (f := fun j : ℕ =>
    2 ^ j / 2 * (agmA 1 salaminB0 j ^ 2 - agmB 1 salaminB0 j ^ 2)) 1).mpr h
  refine (h2.mul_left 4).congr fun j => ?_
  simp only [agmCsq]
  ring

/-- Salamin's identity: `π (1 − ∑_{j≥1} 2^(j+1) c_j²) = 4 AGM(1, 1/√2)²`. -/
theorem salamin_identity : π * (1 - salaminSum) = 4 * AGM 1 salaminB0 ^ 2 := by
  have hE := ellipticE_eq_AGM_sum salaminB0_pos salaminB0_lt_one
  rw [sqrt_one_sub_salaminB0_sq] at hE
  have hL : 2 * ellipticE salaminB0 * ellipticK salaminB0 - ellipticK salaminB0 ^ 2 = π / 2 :=
    legendre_relation_sqrt_half
  have hK := ellipticK_salaminB0
  have hS := summable_agm_c_sq one_pos salaminB0_pos salaminB0_lt_one.le
  have hsplit := hS.tsum_eq_zero_add
  have htail : ∑' j : ℕ, 2 ^ (j + 1) / 2
      * (agmA 1 salaminB0 (j + 1) ^ 2 - agmB 1 salaminB0 (j + 1) ^ 2) = salaminSum / 4 := by
    rw [salaminSum, ← tsum_div_const]
    refine tsum_congr fun j => ?_
    simp only [agmCsq]
    ring
  simp only [agmA_zero, agmB_zero, one_pow, salaminB0_sq, pow_zero] at hsplit
  rw [htail] at hsplit
  rw [hsplit] at hE
  have hM : 0 < AGM 1 salaminB0 := AGM_one_pos salaminB0_pos
  rw [hE, hK] at hL
  field_simp at hL
  linear_combination (1 / 4 : ℝ) * hL

theorem salamin_denominator_pos : 0 < 1 - salaminSum := by
  have hM : 0 < AGM 1 salaminB0 := AGM_one_pos salaminB0_pos
  have : 0 < π * (1 - salaminSum) := by rw [salamin_identity]; positivity
  exact pos_of_mul_pos_right this Real.pi_pos.le

/-- **Salamin's formula**: `π = 4 AGM(1, 1/√2)² / (1 − ∑_{j≥1} 2^(j+1) c_j²)`. -/
theorem salamin_formula : π = 4 * AGM 1 salaminB0 ^ 2 / (1 - salaminSum) := by
  rw [eq_div_iff salamin_denominator_pos.ne', salamin_identity]

/-! ### The Brent–Salamin iterate -/

local notation "sA" => agmA 1 salaminB0
local notation "sB" => agmB 1 salaminB0

theorem salamin_agm_pos (n : ℕ) : 0 < sA n ∧ 0 < sB n := agm_pos one_pos salaminB0_pos n

theorem salaminB0_gt : 2 / 3 < salaminB0 := by
  unfold salaminB0
  rw [lt_div_iff₀ (by positivity)]
  have : Real.sqrt 2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

theorem salamin_agmA_one : sA 1 = (1 + salaminB0) / 2 := by rw [agmA_succ, agmA_zero, agmB_zero]

theorem salamin_agmB_one : sB 1 = Real.sqrt salaminB0 := by
  rw [agmB_succ, agmA_zero, agmB_zero, one_mul]

theorem salamin_agmB_one_sq : sB 1 ^ 2 = salaminB0 := by
  rw [salamin_agmB_one, Real.sq_sqrt salaminB0_pos.le]

theorem salamin_agmB_one_gt : 2 / 3 < sB 1 := by
  rw [salamin_agmB_one]
  have h0 := salaminB0_pos
  have h1 := salaminB0_lt_one
  calc 2 / 3 < salaminB0 := salaminB0_gt
    _ ≤ Real.sqrt salaminB0 := (Real.le_sqrt' h0).mpr (by nlinarith)

/-- `a_n ≤ 1` for `n ≥ 1`. -/
theorem salamin_agmA_le_one {n : ℕ} (hn : 1 ≤ n) : sA n ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  calc sA (m + 1) ≤ sA 1 := by simpa using agmA_antitone one_pos salaminB0_pos (Nat.zero_le m)
    _ = (1 + salaminB0) / 2 := salamin_agmA_one
    _ ≤ 1 := by linarith [salaminB0_lt_one]

/-- `b_n > 2/3` for `n ≥ 1`. -/
theorem salamin_agmB_gt {n : ℕ} (hn : 1 ≤ n) : 2 / 3 < sB n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  calc 2 / 3 < sB 1 := salamin_agmB_one_gt
    _ ≤ sB (m + 1) := by simpa using agmB_monotone one_pos salaminB0_pos (Nat.zero_le m)

/-- The gap is in the quarter-decay regime from the start: `a_n − b_n ≤ 2 b_1` for `n ≥ 1`. -/
theorem salamin_gap_le_two_mul {n : ℕ} (hn : 1 ≤ n) : sA n - sB n ≤ 2 * sB 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := agm_gap_le_half_pow one_pos salaminB0_pos m
  have hA1 := salamin_agmA_le_one le_rfl
  have hB1 := salamin_agmB_one_gt
  have h2 : (sA 1 - sB 1) / 2 ^ m ≤ sA 1 - sB 1 :=
    div_le_self (sub_nonneg.mpr (agmB_le_agmA one_pos salaminB0_pos le_rfl))
      (one_le_pow₀ (by norm_num))
  linarith

/-- `s_N = 1/2 − ∑_{j=1}^{N} 2^j c_j²`. -/
noncomputable def salaminS (N : ℕ) : ℝ :=
  1 / 2 - ∑ j ∈ Finset.range N, 2 ^ (j + 1) * agmCsq 1 salaminB0 (j + 1)

theorem salaminS_zero : salaminS 0 = 1 / 2 := by simp [salaminS]

/-- The recurrence the algorithm runs: `s_{N+1} = s_N − 2^(N+1) ((a_N − b_N)/2)²`. -/
theorem salaminS_succ (N : ℕ) :
    salaminS (N + 1) = salaminS N - 2 ^ (N + 1) * ((sA N - sB N) / 2) ^ 2 := by
  rw [salaminS, salaminS, Finset.sum_range_succ, agmCsq_succ one_pos salaminB0_pos]
  ring

/-- The Brent–Salamin iterate `π_N = 2 a_{N+1}²/s_N`. -/
noncomputable def salaminApprox (N : ℕ) : ℝ := 2 * sA (N + 1) ^ 2 / salaminS N

/-- The tail `r_N = ∑_{j≥N} 2^(j+1) c_{j+1}²`, so that `s_N = s_∞ + r_N`. -/
noncomputable def salaminTail (N : ℕ) : ℝ :=
  ∑' i : ℕ, 2 ^ (i + N + 1) * agmCsq 1 salaminB0 (i + N + 1)

theorem summable_salaminSum_add (N : ℕ) :
    Summable fun i : ℕ => 2 ^ (i + N + 2) * agmCsq 1 salaminB0 (i + N + 1) :=
  (summable_nat_add_iff (f := fun j : ℕ => 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1)) N).mpr
    summable_salaminSum

theorem summable_salaminTail (N : ℕ) :
    Summable fun i : ℕ => 2 ^ (i + N + 1) * agmCsq 1 salaminB0 (i + N + 1) := by
  refine ((summable_salaminSum_add N).div_const 2).congr fun i => ?_
  ring

theorem agmCsq_succ_nonneg (ha : 0 < a) (hb : 0 < b) (j : ℕ) : 0 ≤ agmCsq a b (j + 1) := by
  rw [agmCsq_succ ha hb]; positivity

theorem salaminTail_nonneg (N : ℕ) : 0 ≤ salaminTail N :=
  tsum_nonneg fun i => mul_nonneg (by positivity) (agmCsq_succ_nonneg one_pos salaminB0_pos _)

/-- `s_N = (1 − T)/2 + r_N`. -/
theorem salaminS_eq (N : ℕ) : salaminS N = (1 - salaminSum) / 2 + salaminTail N := by
  have h : (∑ i ∈ Finset.range N, 2 ^ (i + 2) * agmCsq 1 salaminB0 (i + 1))
      + ∑' i : ℕ, 2 ^ (i + N + 2) * agmCsq 1 salaminB0 (i + N + 1) = salaminSum :=
    Summable.sum_add_tsum_nat_add' (f := fun j : ℕ => 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1))
      (k := N) (summable_salaminSum_add N)
  have e1 : ∑ j ∈ Finset.range N, 2 ^ (j + 1) * agmCsq 1 salaminB0 (j + 1)
      = (∑ j ∈ Finset.range N, 2 ^ (j + 2) * agmCsq 1 salaminB0 (j + 1)) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : salaminTail N
      = (∑' i : ℕ, 2 ^ (i + N + 2) * agmCsq 1 salaminB0 (i + N + 1)) / 2 := by
    rw [salaminTail, ← tsum_div_const]
    exact tsum_congr fun i => by ring
  rw [salaminS, e1, e2]
  linarith

/-- `s_∞ = (1 − T)/2 = 2 AGM²/π > 1/3`. -/
theorem salaminS_limit_gt : 1 / 3 < (1 - salaminSum) / 2 := by
  have hM := AGM_one_pos salaminB0_pos
  have hb1 : sB 1 ≤ AGM 1 salaminB0 := agmB_le_AGM one_pos salaminB0_pos le_rfl
  have hM2 : sB 1 ^ 2 ≤ AGM 1 salaminB0 ^ 2 := pow_le_pow_left₀ (salamin_agm_pos 1).2.le hb1 2
  rw [salamin_agmB_one_sq] at hM2
  have hid := salamin_identity
  have hD := salamin_denominator_pos
  have hpi := Real.pi_lt_four
  have hb0 := salaminB0_gt
  nlinarith

theorem salaminS_gt (N : ℕ) : 1 / 3 < salaminS N := by
  rw [salaminS_eq]
  linarith [salaminS_limit_gt, salaminTail_nonneg N]

/-- `π = 2 AGM²/s_∞`. -/
theorem pi_eq_div_salaminS_limit :
    π = 2 * AGM 1 salaminB0 ^ 2 / ((1 - salaminSum) / 2) := by
  have hD := salamin_denominator_pos
  have hid := salamin_identity
  rw [eq_div_iff (by positivity)]
  linarith

/-- The geometric tail bound: for `N ≥ 1`, `r_N ≤ (4/7) 2^N (a_N − b_N)²`. -/
theorem salaminTail_le {N : ℕ} (hN : 1 ≤ N) :
    salaminTail N ≤ 4 / 7 * 2 ^ N * (sA N - sB N) ^ 2 := by
  have hgap := salamin_gap_le_two_mul hN
  have hg0 : 0 ≤ sA N - sB N := sub_nonneg.mpr (agmB_le_agmA one_pos salaminB0_pos hN)
  have hterm : ∀ i : ℕ, 2 ^ (i + N + 1) * agmCsq 1 salaminB0 (i + N + 1)
      ≤ 2 ^ N / 2 * (sA N - sB N) ^ 2 * (1 / 8 : ℝ) ^ i := by
    intro i
    rw [agmCsq_succ one_pos salaminB0_pos]
    have h1 := agm_gap_add_le one_pos salaminB0_pos hN hgap i
    rw [add_comm N i] at h1
    have hgi : 0 ≤ sA (i + N) - sB (i + N) :=
      sub_nonneg.mpr (agmB_le_agmA one_pos salaminB0_pos (by omega))
    have h2 : ((sA (i + N) - sB (i + N)) / 2) ^ 2 ≤ ((sA N - sB N) / 4 ^ i / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc 2 ^ (i + N + 1) * ((sA (i + N) - sB (i + N)) / 2) ^ 2
        ≤ 2 ^ (i + N + 1) * ((sA N - sB N) / 4 ^ i / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ N / 2 * (sA N - sB N) ^ 2 * (1 / 8 : ℝ) ^ i := by
          rw [show (4 : ℝ) ^ i = 2 ^ i * 2 ^ i by rw [← mul_pow]; norm_num,
            show (1 / 8 : ℝ) ^ i = 1 / (2 ^ i * 2 ^ i * 2 ^ i) by
              rw [one_div_pow, ← mul_pow, ← mul_pow]; norm_num,
            pow_add, pow_add]
          field_simp
  have hsum : Summable fun i : ℕ => 2 ^ N / 2 * (sA N - sB N) ^ 2 * (1 / 8 : ℝ) ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc salaminTail N ≤ ∑' i : ℕ, 2 ^ N / 2 * (sA N - sB N) ^ 2 * (1 / 8 : ℝ) ^ i :=
        Summable.tsum_le_tsum hterm (summable_salaminTail N) hsum
    _ = 2 ^ N / 2 * (sA N - sB N) ^ 2 * (8 / 7) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
    _ = 4 / 7 * 2 ^ N * (sA N - sB N) ^ 2 := by ring

/-- Upper bound: `π_N − π ≤ (9/4)(a_N − b_N)²` for `N ≥ 1`. -/
theorem salaminApprox_sub_pi_le {N : ℕ} (hN : 1 ≤ N) :
    salaminApprox N - π ≤ 9 / 4 * (sA N - sB N) ^ 2 := by
  have hM := AGM_one_pos salaminB0_pos
  have hs := salaminS_gt N
  have hsInf := salaminS_limit_gt
  have hsge : (1 - salaminSum) / 2 ≤ salaminS N := by
    rw [salaminS_eq]; linarith [salaminTail_nonneg N]
  obtain ⟨hA1, hB1⟩ := salamin_agm_pos (N + 1)
  have hMA : AGM 1 salaminB0 ≤ sA (N + 1) := AGM_le_agmA one_pos salaminB0_pos (by omega)
  have hBM : sB (N + 1) ≤ AGM 1 salaminB0 := agmB_le_AGM one_pos salaminB0_pos (by omega)
  have hAle : sA (N + 1) ≤ 1 := salamin_agmA_le_one (by omega)
  have hBgt : 2 / 3 < sB N := salamin_agmB_gt hN
  have hgap := agm_gap_succ_le_sq one_pos salaminB0_pos hN
  have hg0 : 0 ≤ sA N - sB N := sub_nonneg.mpr (agmB_le_agmA one_pos salaminB0_pos hN)
  have h1 : 2 * AGM 1 salaminB0 ^ 2 / salaminS N
      ≤ 2 * AGM 1 salaminB0 ^ 2 / ((1 - salaminSum) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hsge
  have h2 : sA (N + 1) ^ 2 - AGM 1 salaminB0 ^ 2 ≤ 3 / 8 * (sA N - sB N) ^ 2 := by
    have e : sA (N + 1) ^ 2 - AGM 1 salaminB0 ^ 2
        = (sA (N + 1) - AGM 1 salaminB0) * (sA (N + 1) + AGM 1 salaminB0) := by ring
    have h3 : sA (N + 1) - AGM 1 salaminB0 ≤ sA (N + 1) - sB (N + 1) := by linarith
    have h4 : sA (N + 1) + AGM 1 salaminB0 ≤ 2 := by linarith
    have h6 : (sA N - sB N) ^ 2 / (8 * sB N) ≤ (sA N - sB N) ^ 2 / (16 / 3) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    rw [e]
    calc (sA (N + 1) - AGM 1 salaminB0) * (sA (N + 1) + AGM 1 salaminB0)
        ≤ (sA N - sB N) ^ 2 / (16 / 3) * 2 :=
          mul_le_mul (h3.trans (hgap.trans h6)) h4 (by linarith) (by positivity)
      _ = 3 / 8 * (sA N - sB N) ^ 2 := by ring
  rw [salaminApprox, pi_eq_div_salaminS_limit]
  calc 2 * sA (N + 1) ^ 2 / salaminS N - 2 * AGM 1 salaminB0 ^ 2 / ((1 - salaminSum) / 2)
      ≤ 2 * sA (N + 1) ^ 2 / salaminS N - 2 * AGM 1 salaminB0 ^ 2 / salaminS N := by linarith
    _ = 2 * (sA (N + 1) ^ 2 - AGM 1 salaminB0 ^ 2) / salaminS N := by ring
    _ ≤ 2 * (3 / 8 * (sA N - sB N) ^ 2) / salaminS N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) (by linarith)
    _ ≤ 2 * (3 / 8 * (sA N - sB N) ^ 2) / (1 / 3) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hs.le
    _ = 9 / 4 * (sA N - sB N) ^ 2 := by ring

/-- Lower bound: `π_N − π ≥ −(48/7) 2^N (a_N − b_N)²` for `N ≥ 1`. -/
theorem le_salaminApprox_sub_pi {N : ℕ} (hN : 1 ≤ N) :
    -(48 / 7 * 2 ^ N * (sA N - sB N) ^ 2) ≤ salaminApprox N - π := by
  have hM := AGM_one_pos salaminB0_pos
  have hs := salaminS_gt N
  have hsInf := salaminS_limit_gt
  have hr0 := salaminTail_nonneg N
  have hsN := salaminS_eq N
  obtain ⟨hA1, hB1⟩ := salamin_agm_pos (N + 1)
  have hMA : AGM 1 salaminB0 ≤ sA (N + 1) := AGM_le_agmA one_pos salaminB0_pos (by omega)
  have hπ := pi_eq_div_salaminS_limit
  have h1 : 2 * AGM 1 salaminB0 ^ 2 / salaminS N ≤ 2 * sA (N + 1) ^ 2 / salaminS N :=
    div_le_div_of_nonneg_right (by nlinarith) (by linarith)
  have e : 2 * AGM 1 salaminB0 ^ 2 / salaminS N - 2 * AGM 1 salaminB0 ^ 2 / ((1 - salaminSum) / 2)
      = -(2 * AGM 1 salaminB0 ^ 2 / ((1 - salaminSum) / 2)) * (salaminTail N / salaminS N) := by
    set u := (1 - salaminSum) / 2 with hu
    have hu0 : u ≠ 0 := by linarith
    have hur : u + salaminTail N ≠ 0 := by linarith
    rw [hsN]
    field_simp
    ring
  rw [← hπ] at e
  have h2 : π * salaminTail N / salaminS N ≤ 48 / 7 * 2 ^ N * (sA N - sB N) ^ 2 := by
    calc π * salaminTail N / salaminS N ≤ 4 * (4 / 7 * 2 ^ N * (sA N - sB N) ^ 2) / (1 / 3) :=
          div_le_div₀ (by positivity)
            (mul_le_mul Real.pi_lt_four.le (salaminTail_le hN) hr0 (by norm_num)) (by norm_num)
            hs.le
      _ = 48 / 7 * 2 ^ N * (sA N - sB N) ^ 2 := by ring
  calc -(48 / 7 * 2 ^ N * (sA N - sB N) ^ 2) ≤ -(π * salaminTail N / salaminS N) := by linarith
    _ = 2 * AGM 1 salaminB0 ^ 2 / salaminS N - π := by rw [e]; ring
    _ ≤ 2 * sA (N + 1) ^ 2 / salaminS N - π := by linarith
    _ = salaminApprox N - π := rfl

/-- **The self-validating error bound of the Brent–Salamin iterate**: for `N ≥ 1`,
`|π_N − π| ≤ 7 · 2^N (a_N − b_N)²`. -/
theorem abs_salaminApprox_sub_pi_le {N : ℕ} (hN : 1 ≤ N) :
    |salaminApprox N - π| ≤ 7 * 2 ^ N * (sA N - sB N) ^ 2 := by
  have h1 := salaminApprox_sub_pi_le hN
  have h2 := le_salaminApprox_sub_pi hN
  have hg := sq_nonneg (sA N - sB N)
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hprod : (sA N - sB N) ^ 2 ≤ 2 ^ N * (sA N - sB N) ^ 2 := by nlinarith
  have hpos : 0 ≤ 2 ^ N * (sA N - sB N) ^ 2 := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- `π_N → π`. -/
theorem tendsto_salaminApprox : Tendsto salaminApprox atTop (𝓝 π) := by
  have h1 := tendsto_two_pow_mul_agm_gap one_pos salaminB0_pos
  have h2 : Tendsto (fun N => sA N - sB N) atTop (𝓝 0) := by
    have := tendsto_agm_gap one_pos salaminB0_pos
    rwa [← tendsto_add_atTop_iff_nat 1]
  have h3 : Tendsto (fun N => 7 * (2 ^ N * (sA N - sB N)) * (sA N - sB N)) atTop (𝓝 0) := by
    simpa using (h1.const_mul 7).mul h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ h3
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  exact (abs_salaminApprox_sub_pi_le hN).trans (le_of_eq (by ring))

end BZ

end Azurite
