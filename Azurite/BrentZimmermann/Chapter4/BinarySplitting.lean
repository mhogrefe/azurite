/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.ComplexAGM
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Brent–Zimmermann §4.9: Binary splitting (introduction)

The AGM algorithms for `arctan`, `sin`, `cos` carry a large constant in their `O(M(n) log n)`
bound (§4.8.4), so algorithms with cost `O((log n)^α M(n))`, `α ≥ 1`, can win over a large range
of precisions.  *The idea*: for rational `x = p/q` with small `p, q` and `|x| ≤ 1/2`,

  `arctan(p/q) ≈ ∑_{0≤j≤n/2} (−1)^j p^(2j+1)/((2j+1) q^(2j+1))`

(the pasted text has `q^(2k+1)`; the exponent is `2j+1`), an exact rational `P/Q` with
`log |Q| = O(n log n)` (for `exp`, `∼ n/ln n` terms and `log |Q| = O(n)`).  It is computed by
divide and conquer: `P/Q = P₁/Q₁ + P₂/Q₂ = (P₁Q₂ + P₂Q₁)/(Q₁Q₂)`, recursively — "binary
splitting"; only fast multiplication profits from the balanced products.  *Complexity* (4.80):
`∑_{k=1}^{⌈lg n⌉} 2^k M(2^(−k) n log n) = O((log n)^α M(n))`, `α = 2` in the FFT range (`α ≤ 2`
in general, Exercise 4.47); working to precision `n` at the top levels saves a little but keeps
`α = 2`.

What is formalized (all proven):

* `arctanTerm`, `hasSum_arctanTerm` (Mathlib's `Real.hasSum_arctan`), the tail bound
  `abs_arctan_sub_sum_le` (`|arctan x − ∑_{j<N}| ≤ |x|^(2N+1)/((2N+1)(1 − x²))`) and the
  precision statement `abs_arctan_sub_sum_le_two_pow`: for `|x| ≤ 1/2` the terms `j ≤ n/2` give
  `arctan x` to within `2^(−n)`.
* The rational structure: `arctanNum`/`arctanDen` with
  `sum_arctanTerm_div_eq : ∑_{j<N} term_j(p/q) = P/Q`, `Q = q^(2N+1) ∏_{j<N}(2j+1)`, and the size
  bound `log_arctanDen_le : log Q ≤ (2N+1) log q + N log(2N)` — `O(n log n)` for `N ∼ n/2`; for
  `exp`, `log_factorial_mul_pow_le : log(N! q^N) ≤ N log N + N log q` — `O(n)` when `N log N ≤ n`.
* Binary splitting itself: `div_add_div_eq` (the two-piece combination) and the general
  `sum_div_eq_sum_mul_prod_erase_div` (`∑ num_i/den_i = (∑ num_i ∏_{j≠i} den_j)/∏ den_j`).
* (4.80) in the quasi-linear model `M(m) = m lg m` (`quasiLinearCost`):
  `two_pow_mul_quasiLinearCost_div_le` (`2^k M(m/2^k) ≤ M(m)`), `binary_splitting_cost_le`
  (`∑_{k=1}^{L} 2^k M(n lg n/2^k) ≤ L · 2 lg n · M(n)`), `clog_le_logb_add_one`
  (`⌈lg n⌉ ≤ lg n + 1`), and `binary_splitting_cost`: with `L = ⌈lg n⌉` the sum is
  `≤ 4 (lg n)² M(n)`, i.e. `α = 2`.

Not formalized: `α ≤ 2` for other multiplication algorithms (Exercise 4.47, cost model per
algorithm), the saving from precision `n` at the top levels, mixed multiplication algorithms by
size; the algorithm itself is deferred (theory first).
-/

namespace Azurite

namespace BZ

open Finset Real

variable {x : ℝ}

/-! ### The arctan series and its truncation -/

/-- The `j`-th term `(−1)^j x^(2j+1)/(2j+1)` of the arctan series. -/
noncomputable def arctanTerm (x : ℝ) (j : ℕ) : ℝ := (-1) ^ j * x ^ (2 * j + 1) / (2 * j + 1)

theorem hasSum_arctanTerm (hx : |x| < 1) : HasSum (arctanTerm x) (Real.arctan x) := by
  have h := Real.hasSum_arctan (x := x) (by rwa [Real.norm_eq_abs])
  have e : arctanTerm x = fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
    funext n
    simp [arctanTerm]
  rw [e]
  exact h

/-- `|arctan x − ∑_{j<N} (−1)^j x^(2j+1)/(2j+1)| ≤ |x|^(2N+1)/((2N+1)(1 − x²))` for `|x| < 1`. -/
theorem abs_arctan_sub_sum_le (hx : |x| < 1) (N : ℕ) :
    |Real.arctan x - ∑ j ∈ range N, arctanTerm x j|
      ≤ |x| ^ (2 * N + 1) / ((2 * N + 1) * (1 - x ^ 2)) := by
  have hs := (hasSum_arctanTerm hx).summable
  have hx2 : x ^ 2 < 1 := by rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg x) hx two_ne_zero
  have hx2' : 0 ≤ x ^ 2 := sq_nonneg x
  rw [← (hasSum_arctanTerm hx).tsum_eq, ← Summable.sum_add_tsum_nat_add' (f := arctanTerm x)
    (k := N) ((summable_nat_add_iff (f := arctanTerm x) N).mpr hs), add_sub_cancel_left]
  have hterm : ∀ j : ℕ,
      ‖arctanTerm x (j + N)‖ ≤ |x| ^ (2 * N + 1) / (2 * N + 1) * (x ^ 2) ^ j := by
    intro j
    have hjN : (0 : ℝ) < 2 * ((j + N : ℕ) : ℝ) + 1 := by positivity
    rw [Real.norm_eq_abs, arctanTerm, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_pow, abs_of_pos hjN, show 2 * (j + N) + 1 = (2 * N + 1) + 2 * j by ring,
      pow_add, pow_mul, sq_abs]
    calc |x| ^ (2 * N + 1) * (x ^ 2) ^ j / (2 * ((j + N : ℕ) : ℝ) + 1)
        ≤ |x| ^ (2 * N + 1) * (x ^ 2) ^ j / (2 * N + 1) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by push_cast; linarith)
      _ = _ := by ring
  have hgeo : Summable fun j : ℕ => |x| ^ (2 * N + 1) / (2 * N + 1) * (x ^ 2) ^ j :=
    (summable_geometric_of_lt_one hx2' hx2).mul_left _
  have hnorm : Summable fun j : ℕ => ‖arctanTerm x (j + N)‖ :=
    hgeo.of_nonneg_of_le (fun j => norm_nonneg _) hterm
  calc |∑' j : ℕ, arctanTerm x (j + N)| ≤ ∑' j : ℕ, ‖arctanTerm x (j + N)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, |x| ^ (2 * N + 1) / (2 * N + 1) * (x ^ 2) ^ j := hnorm.tsum_le_tsum hterm hgeo
    _ = |x| ^ (2 * N + 1) / (2 * N + 1) * (1 - x ^ 2)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hx2' hx2]
    _ = _ := by rw [← div_eq_mul_inv, div_div]

/-- For `|x| ≤ 1/2`, the `n/2 + 1` terms `j ≤ n/2` give `arctan x` to within `2^(−n)`. -/
theorem abs_arctan_sub_sum_le_two_pow (hx : |x| ≤ 1 / 2) (n : ℕ) :
    |Real.arctan x - ∑ j ∈ range (n / 2 + 1), arctanTerm x j| ≤ (1 / 2) ^ n := by
  have hx1 : |x| < 1 := by linarith
  refine (abs_arctan_sub_sum_le hx1 _).trans ?_
  have hx2 : x ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg x]
  have hn : n + 2 ≤ 2 * (n / 2 + 1) + 1 := by omega
  have hpow : |x| ^ (2 * (n / 2 + 1) + 1) ≤ (1 / 2) ^ (n + 2) :=
    calc |x| ^ (2 * (n / 2 + 1) + 1) ≤ (1 / 2) ^ (2 * (n / 2 + 1) + 1) :=
          pow_le_pow_left₀ (abs_nonneg x) hx _
      _ ≤ (1 / 2) ^ (n + 2) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hden : (3 / 4 : ℝ) ≤ (2 * ((n / 2 + 1 : ℕ) : ℝ) + 1) * (1 - x ^ 2) := by
    have h1 : (1 : ℝ) ≤ 2 * ((n / 2 + 1 : ℕ) : ℝ) + 1 := by
      linarith [(Nat.cast_nonneg (n / 2 + 1) : (0 : ℝ) ≤ (n / 2 + 1 : ℕ))]
    nlinarith
  calc _ ≤ (1 / 2 : ℝ) ^ (n + 2) / (3 / 4) := div_le_div₀ (by positivity) hpow (by norm_num) hden
    _ = (1 / 2) ^ n / 3 := by ring
    _ ≤ (1 / 2) ^ n := by linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

/-! ### The rational `P/Q` -/

/-- The common denominator `Q = q^(2N+1) ∏_{j<N} (2j+1)` of the first `N` terms at `p/q`. -/
def arctanDen (q N : ℕ) : ℕ := q ^ (2 * N + 1) * ∏ j ∈ range N, (2 * j + 1)

/-- The matching integer numerator `P`. -/
def arctanNum (p : ℤ) (q N : ℕ) : ℤ :=
  ∑ j ∈ range N, (-1) ^ j * p ^ (2 * j + 1) * (q : ℤ) ^ (2 * N - 2 * j)
    * ∏ i ∈ (range N).erase j, (2 * (i : ℤ) + 1)

theorem arctanDen_pos {q N : ℕ} (hq : 0 < q) : 0 < arctanDen q N := by
  unfold arctanDen
  exact mul_pos (pow_pos hq _) (prod_pos fun j _ => by omega)

/-- The first `N` terms of the arctan series at `p/q` sum to `P/Q`. -/
theorem sum_arctanTerm_div_eq {p : ℤ} {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ∑ j ∈ range N, arctanTerm ((p : ℝ) / q) j = (arctanNum p q N : ℝ) / (arctanDen q N : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold arctanNum arctanDen
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun j hj => ?_
  have hjN : j < N := mem_range.mp hj
  rw [← mul_prod_erase (range N) (fun i => 2 * (i : ℝ) + 1) hj,
    show 2 * N + 1 = (2 * j + 1) + (2 * N - 2 * j) by omega, pow_add]
  have hprod : (0 : ℝ) < ∏ i ∈ (range N).erase j, (2 * (i : ℝ) + 1) :=
    prod_pos fun i _ => by positivity
  unfold arctanTerm
  rw [div_pow]
  field_simp
  ring

/-- `log Q ≤ (2N+1) log q + N log(2N)` for `q, N ≥ 1`: `log Q = O(n log n)` when `N ∼ n/2`. -/
theorem log_arctanDen_le {q N : ℕ} (hq : 1 ≤ q) :
    Real.log (arctanDen q N) ≤ (2 * N + 1) * Real.log q + N * Real.log (2 * N) := by
  unfold arctanDen
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpos : (0 : ℝ) < ∏ j ∈ range N, (2 * (j : ℝ) + 1) := prod_pos fun j _ => by positivity
  push_cast
  rw [Real.log_mul (by positivity) hpos.ne', Real.log_pow]
  have hprod : ∏ j ∈ range N, (2 * (j : ℝ) + 1) ≤ (2 * N) ^ N := by
    calc ∏ j ∈ range N, (2 * (j : ℝ) + 1) ≤ ∏ _j ∈ range N, (2 * (N : ℝ)) :=
          Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j hj => by
            have : (j : ℝ) + 1 ≤ N := by exact_mod_cast mem_range.mp hj
            linarith)
      _ = (2 * N) ^ N := by rw [prod_const, card_range]
  have := Real.log_le_log hpos hprod
  rw [Real.log_pow] at this
  push_cast
  linarith

/-- For `exp`: the denominator `N! q^N` has `log(N! q^N) ≤ N log N + N log q`. -/
theorem log_factorial_mul_pow_le {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) :
    Real.log ((N.factorial : ℝ) * (q : ℝ) ^ N) ≤ N * Real.log N + N * Real.log q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hfact : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have := Real.log_le_log (by positivity) hfact
  rw [Real.log_pow] at this
  linarith

/-- With `N log N ≤ n` terms (`N ∼ n/ln n`), the `exp` denominator has `log Q ≤ n + N log q`. -/
theorem log_factorial_mul_pow_le' {q N : ℕ} {n : ℝ} (hq : 1 ≤ q) (hN : 1 ≤ N)
    (h : (N : ℝ) * Real.log N ≤ n) :
    Real.log ((N.factorial : ℝ) * (q : ℝ) ^ N) ≤ n + N * Real.log q :=
  (log_factorial_mul_pow_le hq hN).trans (by linarith)

/-! ### Divide and conquer -/

/-- Combining two partial fractions: `P₁/Q₁ + P₂/Q₂ = (P₁Q₂ + P₂Q₁)/(Q₁Q₂)`. -/
theorem div_add_div_eq {K : Type*} [Field K] {P₁ P₂ Q₁ Q₂ : K} (h₁ : Q₁ ≠ 0) (h₂ : Q₂ ≠ 0) :
    P₁ / Q₁ + P₂ / Q₂ = (P₁ * Q₂ + P₂ * Q₁) / (Q₁ * Q₂) := by
  rw [div_add_div _ _ h₁ h₂]
  ring

/-- Binary splitting on a finite family: `∑ num_i/den_i = (∑ num_i ∏_{j≠i} den_j)/∏ den_j`. -/
theorem sum_div_eq_sum_mul_prod_erase_div {ι K : Type*} [DecidableEq ι] [Field K] (s : Finset ι)
    (num den : ι → K) (hden : ∀ i ∈ s, den i ≠ 0) :
    ∑ i ∈ s, num i / den i = (∑ i ∈ s, num i * ∏ j ∈ s.erase i, den j) / ∏ j ∈ s, den j := by
  rw [sum_div]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_prod_erase s den hi]
  have h1 : den i ≠ 0 := hden i hi
  have h2 : ∏ j ∈ s.erase i, den j ≠ 0 :=
    prod_ne_zero_iff.mpr fun j hj => hden j (mem_of_mem_erase hj)
  field_simp

/-! ### The cost (4.80) in the quasi-linear model -/

/-- The quasi-linear cost model `M(m) = m lg m`. -/
noncomputable def quasiLinearCost (m : ℝ) : ℝ := m * Real.logb 2 m

/-- `2^k M(m/2^k) ≤ M(m)` for `m ≥ 1`. -/
theorem two_pow_mul_quasiLinearCost_div_le {m : ℝ} (hm : 1 ≤ m) (k : ℕ) :
    2 ^ k * quasiLinearCost (m / 2 ^ k) ≤ quasiLinearCost m := by
  unfold quasiLinearCost
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rw [Real.logb_div (by positivity) h2k.ne', Real.logb_pow, Real.logb_self_eq_one one_lt_two]
  rw [show (2 : ℝ) ^ k * (m / 2 ^ k * (Real.logb 2 m - k * 1)) = m * Real.logb 2 m - m * k by
    field_simp]
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- `lg n ≤ n`. -/
theorem logb_two_natCast_le_self {n : ℕ} (hn : 1 ≤ n) : Real.logb 2 n ≤ n := by
  rw [Real.logb_le_iff_le_rpow one_lt_two (by exact_mod_cast hn), Real.rpow_natCast]
  exact_mod_cast Nat.lt_two_pow_self.le

/-- Each level of the binary splitting costs at most `2 lg n · M(n)`, so `L` levels cost at most
`L · 2 lg n · M(n)`. -/
theorem binary_splitting_cost_le {n : ℕ} (hn : 2 ≤ n) (L : ℕ) :
    ∑ k ∈ Icc 1 L, 2 ^ k * quasiLinearCost (n * Real.logb 2 n / 2 ^ k)
      ≤ L * (2 * Real.logb 2 n * quasiLinearCost n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlg : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]
    exact_mod_cast hn
  have hm : 1 ≤ (n : ℝ) * Real.logb 2 n := by nlinarith
  have hterm : ∀ k ∈ Icc 1 L, 2 ^ k * quasiLinearCost (n * Real.logb 2 n / 2 ^ k)
      ≤ 2 * Real.logb 2 n * quasiLinearCost n := by
    intro k _
    refine (two_pow_mul_quasiLinearCost_div_le hm k).trans ?_
    unfold quasiLinearCost
    have hlglg : Real.logb 2 (Real.logb 2 n) ≤ Real.logb 2 n :=
      Real.logb_le_logb_of_le one_lt_two (by linarith) (logb_two_natCast_le_self (by omega))
    rw [Real.logb_mul (by positivity) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hlglg (by positivity : (0 : ℝ) ≤ n * Real.logb 2 n)]
  calc _ ≤ ∑ _k ∈ Icc 1 L, 2 * Real.logb 2 n * quasiLinearCost n := sum_le_sum hterm
    _ = _ := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- `⌈lg n⌉ ≤ lg n + 1`. -/
theorem clog_le_logb_add_one {n : ℕ} (hn : 2 ≤ n) : (Nat.clog 2 n : ℝ) ≤ Real.logb 2 n + 1 := by
  have h := Nat.pow_pred_clog_lt_self (b := 2) one_lt_two (by omega : 1 < n)
  have hpos : 0 < Nat.clog 2 n := Nat.clog_pos one_lt_two (by omega)
  have h' : ((Nat.clog 2 n).pred : ℝ) < Real.logb 2 n := by
    rw [Real.lt_logb_iff_rpow_lt one_lt_two (by positivity), Real.rpow_natCast]
    exact_mod_cast h
  have e : ((Nat.clog 2 n : ℕ) : ℝ) = ((Nat.clog 2 n).pred : ℝ) + 1 := by
    rw [← Nat.cast_succ, Nat.succ_pred_eq_of_pos hpos]
  linarith

/-- (4.80) with `α = 2`: in the quasi-linear model, `∑_{k=1}^{⌈lg n⌉} 2^k M(n lg n/2^k) ≤
4 (lg n)² M(n)`. -/
theorem binary_splitting_cost {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Icc 1 (Nat.clog 2 n), 2 ^ k * quasiLinearCost (n * Real.logb 2 n / 2 ^ k)
      ≤ 4 * Real.logb 2 n ^ 2 * quasiLinearCost n := by
  refine (binary_splitting_cost_le hn _).trans ?_
  have hL := clog_le_logb_add_one hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlg : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]
    exact_mod_cast hn
  have hM : 0 ≤ quasiLinearCost n := mul_nonneg (by linarith) (by linarith)
  have hL' : (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 n := by linarith
  calc (Nat.clog 2 n : ℝ) * (2 * Real.logb 2 n * quasiLinearCost n)
      ≤ 2 * Real.logb 2 n * (2 * Real.logb 2 n * quasiLinearCost n) :=
        mul_le_mul_of_nonneg_right hL' (mul_nonneg (by linarith) hM)
    _ = 4 * Real.logb 2 n ^ 2 * quasiLinearCost n := by ring

end BZ

end Azurite
