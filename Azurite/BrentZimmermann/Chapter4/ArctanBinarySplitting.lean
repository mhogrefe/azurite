/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.BinarySplitting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Brent–Zimmermann §4.9 (continued): repeated application of binary splitting

For `x ∈ (0, 1/4)` approximate `x` by a rational `p/q ≤ x < (p+1)/q`; by the addition formula
(4.17), `arctan x = arctan(p/q) + arctan δ` with `δ = (x − p/q)/(1 + px/q) = (qx − p)/(q + px)`,
and `|δ| < |x − p/q| < 1/q`, so the idea can be repeated on `δ`.  With about `lg n` rationals
`p_i/q_i`, `q_i = 2^(2^i)`, each `arctan(p_i/q_i)` costs `O((log n)^α M(n))` and the total is
`O((log n)^(α+1) M(n))`: `0 ≤ p_i < 2^(2^(i−1))`, so `p_i` has at most `2^(i−1)` bits, `p_i/q_i`
has value `O(2^(−2^(i−1)))` and size `O(2^i)`.  `α + 1` is `2` or `3`; the constants are small and
the method is useful to at least `10⁶` decimal places.  Generalization: the Chudnovsky
"bit-burst" algorithm for solutions of linear differential equations (§4.9.2).

What is formalized (all proven):

* `arctan_sub_arctan` (`arctan a − arctan b = arctan((a − b)/(1 + ab))` for `ab > −1`) and the
  reduction `arctan_eq_arctan_rat_add`: `arctan x = arctan(p/q) + arctan((qx − p)/(q + px))`;
  the bounds `delta_nonneg_le` (`0 ≤ δ ≤ x − p/q`) and `delta_lt_inv` (`δ < 1/q`).
* The iteration with `Q_i = 2^(2^(i+1))` (so `Q₀ = 4`, `Q_{i+1} = Q_i²`): remainders
  `bitBurstRem` (`r₀ = x`, `r_{i+1} = (Q_{i+1} r_i − p_i)/(Q_{i+1} + p_i r_i)`) and numerators
  `bitBurstNum` (`p_i = ⌊Q_{i+1} r_i⌋`); invariants `bitBurstRem_bounds` (`0 ≤ r_i < 1/Q_i`),
  `bitBurstNum_nonneg`, `bitBurstNum_lt` (`p_i < Q_i = √Q_{i+1}`, i.e. at most `2^(i+1)` bits),
  `bitBurstNum_div_lt` (`p_i/Q_{i+1} < 1/Q_i`).
* `arctan_eq_sum_bitBurst`: `arctan x = ∑_{i<L} arctan(p_i/Q_{i+1}) + arctan r_L`;
  `arctan_le_self`; `arctan_bitBurstRem_lt` (`arctan r_L < 1/Q_L = 2^(−2^(L+1))`); the precision
  statements `abs_arctan_sub_sum_bitBurst_le` (`n ≤ 2^(L+1)` ⇒ error `≤ 2^(−n)`) and
  `abs_arctan_sub_sum_bitBurst_clog_le` (`L = ⌈lg n⌉` rationals suffice).
* The `α + 1` cost in the quasi-linear model: `repeated_binary_splitting_cost`
  (`⌈lg n⌉ · 4 (lg n)² M(n) ≤ 8 (lg n)³ M(n)`).

Not formalized: the `10⁶`-digits practicality remark, the bit-burst generalization (§4.9.2).
-/

namespace Azurite

namespace BZ

open Finset Real

variable {x : ℝ}

/-! ### One reduction step -/

/-- `arctan a − arctan b = arctan((a − b)/(1 + ab))` for `ab > −1`. -/
theorem arctan_sub_arctan {a b : ℝ} (h : -1 < a * b) :
    Real.arctan a - Real.arctan b = Real.arctan ((a - b) / (1 + a * b)) := by
  have := Real.arctan_add (x := a) (y := -b) (by nlinarith)
  rw [Real.arctan_neg, ← sub_eq_add_neg] at this
  rw [this]
  congr 1
  ring

/-- The reduction: `arctan x = arctan(p/q) + arctan((qx − p)/(q + px))` for `p, x ≥ 0`, `q > 0`. -/
theorem arctan_eq_arctan_rat_add {p : ℤ} {q : ℕ} (hp : 0 ≤ p) (hq : 0 < q) (hx : 0 ≤ x) :
    Real.arctan x = Real.arctan (p / q) + Real.arctan ((q * x - p) / (q + p * x)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp' : (0 : ℝ) ≤ p := by exact_mod_cast hp
  have hxp : 0 ≤ x * ((p : ℝ) / q) := by positivity
  have h := arctan_sub_arctan (a := x) (b := (p : ℝ) / q) (by linarith)
  have e : (x - (p : ℝ) / q) / (1 + x * ((p : ℝ) / q)) = (q * x - p) / (q + p * x) := by
    field_simp
  rw [e] at h
  linarith

/-- `0 ≤ δ ≤ x − p/q` when `p/q ≤ x`. -/
theorem delta_nonneg_le {p : ℤ} {q : ℕ} (hp : 0 ≤ p) (hq : 0 < q) (hx : 0 ≤ x)
    (hpx : (p : ℝ) / q ≤ x) :
    0 ≤ (q * x - p) / (q + p * x) ∧ (q * x - p) / (q + p * x) ≤ x - p / q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp' : (0 : ℝ) ≤ p := by exact_mod_cast hp
  have hnum : 0 ≤ (q : ℝ) * x - p := by rw [div_le_iff₀ hq'] at hpx; linarith
  have hden : (q : ℝ) ≤ q + p * x := by nlinarith
  constructor
  · exact div_nonneg hnum (by linarith)
  · calc ((q : ℝ) * x - p) / (q + p * x) ≤ (q * x - p) / q :=
          div_le_div_of_nonneg_left hnum hq' hden
      _ = x - p / q := by field_simp

/-- `δ < 1/q` when `p/q ≤ x < (p+1)/q`. -/
theorem delta_lt_inv {p : ℤ} {q : ℕ} (hp : 0 ≤ p) (hq : 0 < q) (hx : 0 ≤ x)
    (hpx : (p : ℝ) / q ≤ x) (hx1 : x < (p + 1) / q) :
    (q * x - p) / (q + p * x) < 1 / q := by
  have h1 : x - (p : ℝ) / q < 1 / q := by
    rw [add_div] at hx1
    linarith
  exact lt_of_le_of_lt (delta_nonneg_le hp hq hx hpx).2 h1

/-! ### The iteration with `q_i = 2^(2^i)` -/

/-- `Q_i = 2^(2^(i+1))`: `Q₀ = 4`, `Q₁ = 16`, …, `Q_{i+1} = Q_i²`. -/
def bitBurstQ (i : ℕ) : ℕ := 2 ^ 2 ^ (i + 1)

theorem bitBurstQ_pos (i : ℕ) : 0 < bitBurstQ i := by unfold bitBurstQ; positivity

theorem bitBurstQ_succ (i : ℕ) : bitBurstQ (i + 1) = bitBurstQ i ^ 2 := by
  unfold bitBurstQ
  rw [← pow_mul, pow_succ 2 (i + 1), mul_comm]

/-- The remainders: `r₀ = x` and
`r_{i+1} = (Q_{i+1} r_i − ⌊Q_{i+1} r_i⌋)/(Q_{i+1} + ⌊Q_{i+1} r_i⌋ r_i)`. -/
noncomputable def bitBurstRem (x : ℝ) : ℕ → ℝ
  | 0 => x
  | i + 1 =>
    ((bitBurstQ (i + 1) : ℝ) * bitBurstRem x i - ⌊(bitBurstQ (i + 1) : ℝ) * bitBurstRem x i⌋)
      / (bitBurstQ (i + 1) + ⌊(bitBurstQ (i + 1) : ℝ) * bitBurstRem x i⌋ * bitBurstRem x i)

/-- The numerators `p_i = ⌊Q_{i+1} r_i⌋`. -/
noncomputable def bitBurstNum (x : ℝ) (i : ℕ) : ℤ := ⌊(bitBurstQ (i + 1) : ℝ) * bitBurstRem x i⌋

theorem bitBurstRem_zero : bitBurstRem x 0 = x := rfl

theorem bitBurstRem_succ (i : ℕ) :
    bitBurstRem x (i + 1) = ((bitBurstQ (i + 1) : ℝ) * bitBurstRem x i - bitBurstNum x i)
      / (bitBurstQ (i + 1) + bitBurstNum x i * bitBurstRem x i) := rfl

/-- The invariant `0 ≤ r_i < 1/Q_i` for `0 ≤ x < 1/4`. -/
theorem bitBurstRem_bounds (hx0 : 0 ≤ x) (hx : x < 1 / 4) (i : ℕ) :
    0 ≤ bitBurstRem x i ∧ bitBurstRem x i < 1 / (bitBurstQ i : ℝ) := by
  induction i with
  | zero => exact ⟨hx0, by simpa [bitBurstRem_zero, bitBurstQ] using hx⟩
  | succ i ih =>
    obtain ⟨h0, -⟩ := ih
    have hq := bitBurstQ_pos (i + 1)
    have hq' : (0 : ℝ) < bitBurstQ (i + 1) := by exact_mod_cast hq
    have hp : 0 ≤ bitBurstNum x i := Int.floor_nonneg.mpr (by positivity)
    have hpx : (bitBurstNum x i : ℝ) / bitBurstQ (i + 1) ≤ bitBurstRem x i := by
      rw [div_le_iff₀ hq', mul_comm]
      exact Int.floor_le _
    have hx1 : bitBurstRem x i < ((bitBurstNum x i : ℝ) + 1) / bitBurstQ (i + 1) := by
      rw [lt_div_iff₀ hq', mul_comm]
      exact Int.lt_floor_add_one _
    rw [bitBurstRem_succ]
    exact ⟨(delta_nonneg_le hp hq h0 hpx).1, delta_lt_inv hp hq h0 hpx hx1⟩

theorem bitBurstNum_nonneg (hx0 : 0 ≤ x) (hx : x < 1 / 4) (i : ℕ) : 0 ≤ bitBurstNum x i :=
  Int.floor_nonneg.mpr (mul_nonneg (by positivity) (bitBurstRem_bounds hx0 hx i).1)

/-- `p_i < Q_i = √Q_{i+1}`: the numerator has at most `2^(i+1)` bits. -/
theorem bitBurstNum_lt (hx0 : 0 ≤ x) (hx : x < 1 / 4) (i : ℕ) :
    bitBurstNum x i < bitBurstQ i := by
  have hQ : (0 : ℝ) < bitBurstQ i := by exact_mod_cast bitBurstQ_pos i
  have hr := (bitBurstRem_bounds hx0 hx i).2
  have h1 : (bitBurstNum x i : ℝ) ≤ bitBurstQ (i + 1) * bitBurstRem x i := Int.floor_le _
  have h2 : (bitBurstQ (i + 1) : ℝ) * bitBurstRem x i < bitBurstQ i := by
    rw [bitBurstQ_succ]
    push_cast
    rw [lt_div_iff₀ hQ] at hr
    nlinarith
  exact_mod_cast h1.trans_lt h2

/-- The value `p_i/Q_{i+1} < 1/Q_i = 2^(−2^(i+1))`. -/
theorem bitBurstNum_div_lt (hx0 : 0 ≤ x) (hx : x < 1 / 4) (i : ℕ) :
    (bitBurstNum x i : ℝ) / bitBurstQ (i + 1) < 1 / bitBurstQ i := by
  have hq' : (0 : ℝ) < bitBurstQ (i + 1) := by exact_mod_cast bitBurstQ_pos (i + 1)
  calc (bitBurstNum x i : ℝ) / bitBurstQ (i + 1) ≤ bitBurstRem x i := by
        rw [div_le_iff₀ hq', mul_comm]
        exact Int.floor_le _
    _ < 1 / bitBurstQ i := (bitBurstRem_bounds hx0 hx i).2

/-- `arctan x = ∑_{i<L} arctan(p_i/Q_{i+1}) + arctan r_L`. -/
theorem arctan_eq_sum_bitBurst (hx0 : 0 ≤ x) (hx : x < 1 / 4) (L : ℕ) :
    Real.arctan x = ∑ i ∈ range L, Real.arctan ((bitBurstNum x i : ℝ) / bitBurstQ (i + 1))
      + Real.arctan (bitBurstRem x L) := by
  induction L with
  | zero => simp [bitBurstRem_zero]
  | succ L ih =>
    rw [sum_range_succ, ih, add_assoc, bitBurstRem_succ]
    congr 1
    exact arctan_eq_arctan_rat_add (bitBurstNum_nonneg hx0 hx L) (bitBurstQ_pos (L + 1))
      (bitBurstRem_bounds hx0 hx L).1

/-- `arctan t ≤ t` for `t ≥ 0`. -/
theorem arctan_le_self {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  have h1 : 0 ≤ Real.arctan t := Real.arctan_nonneg.mpr ht
  have h2 := Real.le_tan h1 (Real.arctan_lt_pi_div_two t)
  rwa [Real.tan_arctan] at h2

/-- `arctan r_L < 1/Q_L = 2^(−2^(L+1))`. -/
theorem arctan_bitBurstRem_lt (hx0 : 0 ≤ x) (hx : x < 1 / 4) (L : ℕ) :
    Real.arctan (bitBurstRem x L) < 1 / (bitBurstQ L : ℝ) :=
  lt_of_le_of_lt (arctan_le_self (bitBurstRem_bounds hx0 hx L).1) (bitBurstRem_bounds hx0 hx L).2

/-- With `n ≤ 2^(L+1)`, the `L` rationals give `arctan x` to within `2^(−n)`. -/
theorem abs_arctan_sub_sum_bitBurst_le (hx0 : 0 ≤ x) (hx : x < 1 / 4) {L n : ℕ}
    (hn : n ≤ 2 ^ (L + 1)) :
    |Real.arctan x - ∑ i ∈ range L, Real.arctan ((bitBurstNum x i : ℝ) / bitBurstQ (i + 1))|
      ≤ (1 / 2) ^ n := by
  rw [arctan_eq_sum_bitBurst hx0 hx L, add_sub_cancel_left]
  have h0 : 0 ≤ Real.arctan (bitBurstRem x L) :=
    Real.arctan_nonneg.mpr (bitBurstRem_bounds hx0 hx L).1
  rw [abs_of_nonneg h0]
  refine (arctan_bitBurstRem_lt hx0 hx L).le.trans ?_
  rw [bitBurstQ, one_div]
  push_cast
  rw [← inv_pow, ← one_div]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn

/-- About `lg n` rationals suffice: with `L = ⌈lg n⌉`, the error is `≤ 2^(−n)`. -/
theorem abs_arctan_sub_sum_bitBurst_clog_le (hx0 : 0 ≤ x) (hx : x < 1 / 4) (n : ℕ) :
    |Real.arctan x - ∑ i ∈ range (Nat.clog 2 n),
        Real.arctan ((bitBurstNum x i : ℝ) / bitBurstQ (i + 1))| ≤ (1 / 2) ^ n :=
  abs_arctan_sub_sum_bitBurst_le hx0 hx
    ((Nat.le_pow_clog one_lt_two n).trans (Nat.pow_le_pow_right two_pos (Nat.le_succ _)))

/-! ### The `α + 1` cost -/

/-- `⌈lg n⌉` binary splittings of cost `4 (lg n)² M(n)` each cost at most `8 (lg n)³ M(n)`:
`α + 1 = 3` in the quasi-linear model. -/
theorem repeated_binary_splitting_cost {n : ℕ} (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) * (4 * Real.logb 2 n ^ 2 * quasiLinearCost n)
      ≤ 8 * Real.logb 2 n ^ 3 * quasiLinearCost n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlg : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]
    exact_mod_cast hn
  have hM : 0 ≤ quasiLinearCost n := mul_nonneg (by linarith) (by linarith)
  have hL : (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 n := by linarith [clog_le_logb_add_one hn]
  calc (Nat.clog 2 n : ℝ) * (4 * Real.logb 2 n ^ 2 * quasiLinearCost n)
      ≤ 2 * Real.logb 2 n * (4 * Real.logb 2 n ^ 2 * quasiLinearCost n) :=
        mul_le_mul_of_nonneg_right hL (by positivity)
    _ = 8 * Real.logb 2 n ^ 3 * quasiLinearCost n := by ring

end BZ

end Azurite
