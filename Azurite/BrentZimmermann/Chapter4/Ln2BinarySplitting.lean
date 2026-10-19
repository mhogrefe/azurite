/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Cast.Field

/-!
# Brent–Zimmermann §4.9.1 (applied): `ln 2` by a Machin-like `atanh` formula

The constant `ln 2` for `AzFloat` is computed from

  `ln 2 = 18 atanh(1/26) − 2 atanh(1/4801) + 8 atanh(1/8749)`,
  `atanh(1/q) = ∑_{k≥0} 1/((2k+1) q^(2k+1)) = (1/2) ln((q+1)/(q−1))`,

each series summed exactly by binary splitting (MCA §4.9.1), so that the only approximation is
the truncation, whose error is controlled exactly: for `q ≥ 2` the terms shrink by at least `1/4`
per step and the tail after `N` terms lies in `[0, (4/3) t_N]`.  The identity is the rational
equation `(27/25)^9 (8750/8748)^4 / (4802/4800) = 2` under `ln`.  The formula needs about `0.19`
terms per bit (against `0.32` for `2 atanh(1/3)`), and the three sums are independent.

What is formalized:

* `atanhTerm q k = 1/((2k+1) q^(2k+1))`, `atanhInv q = ∑ atanhTerm q k`, and
  `atanhInv_eq : atanhInv q = ln((q+1)/(q−1))/2` for `q > 1` (Mathlib's
  `Real.hasSum_log_one_add_inv` with `a = (q−1)/2`).
* The exact bracket: `0 ≤ atanhInv q − ∑_{k<N} t_k ≤ (4/3) t_N` for `q ≥ 2`
  (`sum_le_atanhInv`, `atanhInv_sub_sum_le`), and `t_N ≤ (1/q)^(2N+1)` (`atanhTerm_le`).
* Exact rational partial sums for natural `q`: `∑_{k<N} t_k = atanhNum q N / atanhDen q N` with
  `atanhDen q N = q^(2N+1) ∏_{j<N} (2j+1)` (`sum_atanhTerm_eq_div`).
* The Machin-like identity `log_two_eq_atanh` and the bracket `log_two_mem_Icc`:
  `ln 2 ∈ [18 S₁ − 2 (S₂ + (4/3) t₂) + 8 S₃, 18 (S₁ + (4/3) t₁) − 2 S₂ + 8 (S₃ + (4/3) t₃)]`
  for any truncation orders `N₁, N₂, N₃`, of width `(4/3)(18 t₁ + 2 t₂ + 8 t₃)`.

Not formalized here: the binary-splitting evaluator over `AzNat` and the `AzFloat` constant
(next steps), and the irrationality of `ln 2` (not in Mathlib; the rounding loop takes fuel).
-/

namespace Azurite

namespace BZ

open Finset

/-! ### The series `atanh(1/q)` -/

/-- `t_k = 1/((2k+1) q^(2k+1))`. -/
noncomputable def atanhTerm (q : ℝ) (k : ℕ) : ℝ := 1 / ((2 * k + 1) * q ^ (2 * k + 1))

/-- `atanh(1/q) = ∑_k t_k`. -/
noncomputable def atanhInv (q : ℝ) : ℝ := ∑' k : ℕ, atanhTerm q k

variable {q : ℝ}

theorem atanhTerm_pos (hq : 0 < q) (k : ℕ) : 0 < atanhTerm q k := by unfold atanhTerm; positivity

/-- `atanh(1/q) = (1/2) ln((q+1)/(q−1))` as a sum, for `q > 1`. -/
theorem hasSum_atanhTerm (hq : 1 < q) :
    HasSum (atanhTerm q) (Real.log ((q + 1) / (q - 1)) / 2) := by
  have ha : 0 < (q - 1) / 2 := by linarith
  have h := (Real.hasSum_log_one_add_inv ha).div_const 2
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have e1 : (2 * ((q - 1) / 2) + 1) = q := by ring
  have e2 : 1 + ((q - 1) / 2)⁻¹ = (q + 1) / (q - 1) := by field_simp; ring
  rw [e1, e2] at h
  refine h.congr_fun fun k => ?_
  rw [atanhTerm, one_div_pow]
  field_simp

theorem summable_atanhTerm (hq : 1 < q) : Summable (atanhTerm q) := (hasSum_atanhTerm hq).summable

theorem atanhInv_eq (hq : 1 < q) : atanhInv q = Real.log ((q + 1) / (q - 1)) / 2 :=
  (hasSum_atanhTerm hq).tsum_eq

/-! ### The exact bracket -/

/-- `t_{N+i} ≤ t_N / 4^i` for `q ≥ 2`. -/
theorem atanhTerm_add_le (hq : 2 ≤ q) (N i : ℕ) : atanhTerm q (N + i) ≤ atanhTerm q N / 4 ^ i := by
  have hq0 : 0 < q := by linarith
  unfold atanhTerm
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity)
  have h4 : (4 : ℝ) ^ i ≤ q ^ (2 * i) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by nlinarith) i
  have hN : 2 * (N : ℝ) + 1 ≤ 2 * ((N + i : ℕ) : ℝ) + 1 := by
    push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  calc (2 * (N : ℝ) + 1) * q ^ (2 * N + 1) * 4 ^ i
      ≤ (2 * ((N + i : ℕ) : ℝ) + 1) * q ^ (2 * N + 1) * q ^ (2 * i) := by gcongr
    _ = (2 * ((N + i : ℕ) : ℝ) + 1) * q ^ (2 * (N + i) + 1) := by
        rw [mul_assoc, ← pow_add, show 2 * N + 1 + 2 * i = 2 * (N + i) + 1 by ring]

/-- The partial sums are lower bounds: `∑_{k<N} t_k ≤ atanh(1/q)`. -/
theorem sum_le_atanhInv (hq : 2 ≤ q) (N : ℕ) : ∑ k ∈ range N, atanhTerm q k ≤ atanhInv q :=
  Summable.sum_le_tsum (range N) (fun k _ => (atanhTerm_pos (by linarith) k).le)
    (summable_atanhTerm (by linarith))

/-- The tail is at most `(4/3) t_N`: `atanh(1/q) − ∑_{k<N} t_k ≤ (4/3) t_N` for `q ≥ 2`. -/
theorem atanhInv_sub_sum_le (hq : 2 ≤ q) (N : ℕ) :
    atanhInv q - ∑ k ∈ range N, atanhTerm q k ≤ 4 / 3 * atanhTerm q N := by
  have hs := summable_atanhTerm (by linarith : 1 < q)
  have hq0 : 0 < q := by linarith
  rw [atanhInv, ← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hgeo : Summable fun i : ℕ => atanhTerm q N / 4 ^ i := by
    simpa [div_eq_mul_inv, inv_pow] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left
        (atanhTerm q N)
  calc ∑' i : ℕ, atanhTerm q (i + N) ≤ ∑' i : ℕ, atanhTerm q N / 4 ^ i :=
        Summable.tsum_le_tsum (fun i => by rw [add_comm]; exact atanhTerm_add_le hq N i)
          ((summable_nat_add_iff N).mpr hs) hgeo
    _ = atanhTerm q N * ∑' i : ℕ, (1 / 4 : ℝ) ^ i := by
        rw [← tsum_mul_left]; exact tsum_congr fun i => by rw [one_div_pow, div_eq_mul_one_div]
    _ = 4 / 3 * atanhTerm q N := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num; ring

/-- `t_N ≤ (1/q)^(2N+1)` for `q ≥ 1`. -/
theorem atanhTerm_le (hq : 1 ≤ q) (N : ℕ) : atanhTerm q N ≤ (1 / q) ^ (2 * N + 1) := by
  have hq0 : 0 < q := by linarith
  rw [atanhTerm, one_div_pow]
  apply one_div_le_one_div_of_le (by positivity)
  have : (1 : ℝ) ≤ 2 * N + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  nlinarith [pow_pos hq0 (2 * N + 1)]

/-! ### Exact rational partial sums -/

/-- `∏_{j<N} (2j+1)`. -/
def oddProd (N : ℕ) : ℕ := ∏ j ∈ range N, (2 * j + 1)

theorem oddProd_pos (N : ℕ) : 0 < oddProd N := prod_pos fun j _ => by omega

theorem dvd_oddProd {k N : ℕ} (hk : k < N) : 2 * k + 1 ∣ oddProd N :=
  dvd_prod_of_mem _ (mem_range.mpr hk)

/-- The common denominator `q^(2N+1) ∏_{j<N} (2j+1)` of `∑_{k<N} t_k`. -/
def atanhDen (q N : ℕ) : ℕ := q ^ (2 * N + 1) * oddProd N

/-- The numerator `∑_{k<N} q^(2(N−k)) · (∏_{j<N}(2j+1))/(2k+1)` of `∑_{k<N} t_k`. -/
def atanhNum (q N : ℕ) : ℕ := ∑ k ∈ range N, q ^ (2 * (N - k)) * (oddProd N / (2 * k + 1))

theorem atanhDen_pos {q : ℕ} (hq : 0 < q) (N : ℕ) : 0 < atanhDen q N := by
  unfold atanhDen; have := oddProd_pos N; positivity

/-- `∑_{k<N} t_k(q) = atanhNum q N / atanhDen q N` for natural `q > 0`. -/
theorem sum_atanhTerm_eq_div {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ∑ k ∈ range N, atanhTerm q k = (atanhNum q N : ℝ) / atanhDen q N := by
  unfold atanhNum atanhDen
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hB : (oddProd N : ℝ) ≠ 0 := by exact_mod_cast (oddProd_pos N).ne'
  push_cast
  rw [Finset.sum_div]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  have hk0 : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_div (dvd_oddProd hk) hk0, atanhTerm,
    show 2 * N + 1 = (2 * k + 1) + 2 * (N - k) by omega, pow_add]
  push_cast
  field_simp
  ring

/-! ### The Machin-like formula -/

/-- `ln 2 = 9 ln(27/25) − ln(4802/4800) + 4 ln(8750/8748)`: the rational identity
`(27/25)^9 (8750/8748)^4 / (4802/4800) = 2` under `ln`. -/
theorem log_two_eq_machin :
    Real.log 2 = 9 * Real.log (27 / 25) - Real.log (4802 / 4800) + 4 * Real.log (8750 / 8748) := by
  have h : ((27 : ℝ) / 25) ^ 9 * (8750 / 8748) ^ 4 / (4802 / 4800) = 2 := by norm_num
  rw [← h, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **`ln 2 = 18 atanh(1/26) − 2 atanh(1/4801) + 8 atanh(1/8749)`.** -/
theorem log_two_eq_atanh :
    Real.log 2 = 18 * atanhInv 26 - 2 * atanhInv 4801 + 8 * atanhInv 8749 := by
  rw [atanhInv_eq (by norm_num), atanhInv_eq (by norm_num), atanhInv_eq (by norm_num),
    log_two_eq_machin]
  norm_num
  ring

/-- **The exact bracket for `ln 2`**: with `S_q = ∑_{k<N_q} t_k(q)` and `t_q = t_{N_q}(q)`,
`18 S₁ − 2 (S₂ + (4/3) t₂) + 8 S₃ ≤ ln 2 ≤ 18 (S₁ + (4/3) t₁) − 2 S₂ + 8 (S₃ + (4/3) t₃)`. -/
theorem log_two_mem_Icc (N₁ N₂ N₃ : ℕ) :
    Real.log 2 ∈ Set.Icc
      (18 * ∑ k ∈ range N₁, atanhTerm 26 k
        - 2 * (∑ k ∈ range N₂, atanhTerm 4801 k + 4 / 3 * atanhTerm 4801 N₂)
        + 8 * ∑ k ∈ range N₃, atanhTerm 8749 k)
      (18 * (∑ k ∈ range N₁, atanhTerm 26 k + 4 / 3 * atanhTerm 26 N₁)
        - 2 * ∑ k ∈ range N₂, atanhTerm 4801 k
        + 8 * (∑ k ∈ range N₃, atanhTerm 8749 k + 4 / 3 * atanhTerm 8749 N₃)) := by
  rw [log_two_eq_atanh]
  have h1l := sum_le_atanhInv (by norm_num : (2 : ℝ) ≤ 26) N₁
  have h1u := atanhInv_sub_sum_le (by norm_num : (2 : ℝ) ≤ 26) N₁
  have h2l := sum_le_atanhInv (by norm_num : (2 : ℝ) ≤ 4801) N₂
  have h2u := atanhInv_sub_sum_le (by norm_num : (2 : ℝ) ≤ 4801) N₂
  have h3l := sum_le_atanhInv (by norm_num : (2 : ℝ) ≤ 8749) N₃
  have h3u := atanhInv_sub_sum_le (by norm_num : (2 : ℝ) ≤ 8749) N₃
  constructor <;> linarith

/-- The width of the bracket: `(4/3)(18 t₁ + 2 t₂ + 8 t₃)`. -/
theorem log_two_bracket_width (N₁ N₂ N₃ : ℕ) :
    (18 * (∑ k ∈ range N₁, atanhTerm 26 k + 4 / 3 * atanhTerm 26 N₁)
        - 2 * ∑ k ∈ range N₂, atanhTerm 4801 k
        + 8 * (∑ k ∈ range N₃, atanhTerm 8749 k + 4 / 3 * atanhTerm 8749 N₃))
      - (18 * ∑ k ∈ range N₁, atanhTerm 26 k
        - 2 * (∑ k ∈ range N₂, atanhTerm 4801 k + 4 / 3 * atanhTerm 4801 N₂)
        + 8 * ∑ k ∈ range N₃, atanhTerm 8749 k)
      = 4 / 3 * (18 * atanhTerm 26 N₁ + 2 * atanhTerm 4801 N₂ + 8 * atanhTerm 8749 N₃) := by
  ring

end BZ

end Azurite
