/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.TangentNumbers
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Brent–Zimmermann §4.7.2 (continued): Algorithm TangentNumbers and growth

Using the recurrence (4.63) on the `P_n`, but skipping the coefficients known to vanish, gives
the in-place Algorithm 4.3 for `T_1, …, T_m`:

```
T_1 ← 1
for k from 2 to m do T_k ← (k − 1) T_{k−1}          -- T_k = (k − 1)!
for k from 2 to m do
  for j from k to m do
    T_j ← (j − k) T_{j−1} + (j − k + 2) T_j
return T_1, …, T_m
```

It uses only non-negative integers (so it is numerically stable in floating point: no
cancellation).  The tangent numbers grow like `(2k − 1)! (2/π)^(2k)` because `tan` has poles at
`±π/2`; precisely

  `T_k / (2k−1)! = 2^(2k+1) (1 − 2^(−2k)) ζ(2k) / π^(2k)`,                                   (4.64)

where `(1 − 2^(−s)) ζ(s) = 1 + 3^(−s) + 5^(−s) + …` is the odd zeta function; the Bernoulli numbers
grow more slowly (singularities at `±2πi`):

  `(−1)^(k−1) B_{2k} / (2k)! = 2 ζ(2k) / (2π)^(2k)`,                                        (4.65)

and since `ζ(2k) = 1 + O(4^(−k))`,

  `|B_{2k}| ∼ 2 (2k)! / (2π)^(2k)`.                                                           (4.66)

What is formalized:

* A model of Algorithm 4.3 over `ℕ`: the initial row `tangentInit j = (j − 1)!`, one update
  `tangentStep`, the inner loop `tangentPass k a s` (`s` steps, `j = k, …, k + s − 1`), the outer
  loop `tangentOuter m a r` (`r` passes, `k = 2, …, r + 1`), and `tangentNumbersModel m`.
  The loop invariant: before pass `k` the row holds `p_{j+k−3, j−k+2}` (for `j ≥ k`) and the
  finished `T_j` (for `j < k`); after `s` steps of pass `k` the entries `j < k + s` hold
  `p_{j+k−2, j−k+1}` (`tangentPass_spec`); after all passes every entry is a tangent number
  (`tangentOuter_spec`), so `tangentNumbersModel_eq`: `tangentNumbersModel m j = T_j` for
  `1 ≤ j ≤ m`; `tangentNumbersModel_three` (`1, 2, 16`).
* The odd zeta function `oddZeta s = ∑ (2n+1)^(−s)` and `one_sub_two_rpow_neg_mul_zetaReal`
  (`(1 − 2^(−s)) ζ(s) = oddZeta s` for `s > 1`).
* (4.64) `tangentNumber_div_factorial_eq_zeta` (and `_eq_oddZeta`), from (4.62) and (4.65);
  (4.65) `neg_one_pow_mul_bernoulli_div_factorial` (a restatement of `scaledBernoulli_eq_zeta`).
* `zetaReal_two_mul_sub_one_le` (`ζ(2k) − 1 ≤ 8/4^k`, the `O(4^(−k))`), `tendsto_zetaReal_two_mul`
  (`ζ(2k) → 1`), and the asymptotic equivalences (4.66) `abs_bernoulli_isEquivalent` and
  `tangentNumber_isEquivalent` (`T_k ∼ 2 (2k−1)! (2/π)^(2k)`).

Not formalized: the overflow/floating-point remarks, Algorithm SecantNumbers (Exercise 4.40),
Exercises 4.41, §4.10.  The model is a specification, not the `AzNat` implementation.
-/

namespace Azurite

namespace BZ

open Finset Polynomial Filter Topology Asymptotics

/-! ### Algorithm 4.3 as a model over `ℕ` -/

/-- The initial row of Algorithm 4.3: `T_j ← (j − 1)!` (`T_1 = 1`, `T_k = (k − 1) T_{k−1}`). -/
def tangentInit (j : ℕ) : ℕ := (j - 1).factorial

/-- One update `T_j ← (j − k) T_{j−1} + (j − k + 2) T_j`. -/
def tangentStep (k j : ℕ) (a : ℕ → ℕ) : ℕ → ℕ :=
  Function.update a j ((j - k) * a (j - 1) + (j - k + 2) * a j)

/-- The inner loop of pass `k` after `s` steps (`j = k, …, k + s − 1`). -/
def tangentPass (k : ℕ) (a : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => a
  | s + 1 => tangentStep k (k + s) (tangentPass k a s)

/-- The outer loop after `r` passes (`k = 2, …, r + 1`) on a row of length `m`. -/
def tangentOuter (m : ℕ) (a : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => a
  | r + 1 => tangentPass (r + 2) (tangentOuter m a r) (m + 1 - (r + 2))

/-- Algorithm 4.3: the row after the passes `k = 2, …, m`. -/
def tangentNumbersModel (m : ℕ) : ℕ → ℕ := tangentOuter m tangentInit (m - 1)

/-- The invariant of pass `k`: entries below `k` are finished tangent numbers, entries
`j < k + s` hold `p_{j+k−2, j−k+1}`, entries `j ≥ k + s` still hold `p_{j+k−3, j−k+2}`. -/
theorem tangentPass_spec {k m : ℕ} (hk : 2 ≤ k) (a : ℕ → ℕ)
    (hfin : ∀ j, 1 ≤ j → j < k → (a j : ℤ) = tangentNumber j)
    (hrow : ∀ j, k ≤ j → j ≤ m → (a j : ℤ) = (tanDerivPoly (j + k - 3)).coeff (j - k + 2))
    (s : ℕ) :
    (∀ j, 1 ≤ j → j < k → (tangentPass k a s j : ℤ) = tangentNumber j)
      ∧ (∀ j, k ≤ j → j < k + s → j ≤ m →
          (tangentPass k a s j : ℤ) = (tanDerivPoly (j + k - 2)).coeff (j - k + 1))
      ∧ (∀ j, k + s ≤ j → j ≤ m →
          (tangentPass k a s j : ℤ) = (tanDerivPoly (j + k - 3)).coeff (j - k + 2)) := by
  induction s with
  | zero =>
    refine ⟨hfin, fun j _ hj _ => absurd hj (by omega), fun j hj hjm => hrow j (by omega) hjm⟩
  | succ s ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    simp only [tangentPass, tangentStep]
    refine ⟨fun j h1 hj => ?_, fun j hkj hj hjm => ?_, fun j hj hjm => ?_⟩
    · rw [Function.update_of_ne (by omega)]
      exact ih1 j h1 hj
    · rcases eq_or_ne j (k + s) with rfl | hne
      · have h3 := ih3 (k + s) le_rfl hjm
        have hrec := coeff_tanDerivPoly_succ (k + s + k - 3) s
        rw [show k + s + k - 3 + 1 = k + s + k - 2 by omega] at hrec
        rw [Function.update_self, Nat.add_sub_cancel_left]
        push_cast
        rw [h3, hrec, show k + s - k + 2 = s + 2 by omega]
        rcases Nat.eq_zero_or_pos s with rfl | hs
        · simp
        · have h2 := ih2 (k + s - 1) (by omega) (by omega) (by omega)
          rw [h2, show k + s - 1 + k - 2 = k + s + k - 3 by omega,
            show k + s - 1 - k + 1 = s by omega]
      · rw [Function.update_of_ne hne]
        exact ih2 j hkj (by omega) hjm
    · rw [Function.update_of_ne (by omega)]
      exact ih3 j (by omega) hjm

/-- After `r` passes (`k = 2, …, r + 1`): the entries `j ≤ r + 1` are tangent numbers, the rest
hold `p_{j+r−1, j−r}`. -/
theorem tangentOuter_spec (m : ℕ) : ∀ r, r + 1 ≤ m →
    (∀ j, 1 ≤ j → j < r + 2 → (tangentOuter m tangentInit r j : ℤ) = tangentNumber j)
      ∧ (∀ j, r + 2 ≤ j → j ≤ m →
          (tangentOuter m tangentInit r j : ℤ)
            = (tanDerivPoly (j + (r + 2) - 3)).coeff (j - (r + 2) + 2)) := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨fun j h1 hj => ?_, fun j hj _ => ?_⟩
    · obtain rfl : j = 1 := by omega
      simp [tangentOuter, tangentInit, tangentNumber_one]
    · simp only [tangentOuter, tangentInit]
      rw [show j + (0 + 2) - 3 = j - 1 by omega, show j - (0 + 2) + 2 = j - 1 + 1 by omega,
        coeff_tanDerivPoly_top]
  | succ r ih =>
    intro hr
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hs := tangentPass_spec (k := r + 2) (m := m) (by omega) (tangentOuter m tangentInit r)
      ih1 ih2 (m + 1 - (r + 2))
    obtain ⟨h1, h2, _⟩ := hs
    simp only [tangentOuter]
    refine ⟨fun j hj1 hj => ?_, fun j hj hjm => ?_⟩
    · rcases Nat.lt_or_ge j (r + 2) with hlt | hge
      · exact h1 j hj1 hlt
      · obtain rfl : j = r + 2 := by omega
        rw [h2 (r + 2) le_rfl (by omega) (by omega), tangentNumber,
          show 2 * (r + 2) - 1 = 2 * r + 2 + 1 by omega, coeff_tanDerivPoly_succ_zero,
          show r + 2 + (r + 2) - 2 = 2 * r + 2 by omega, show r + 2 - (r + 2) + 1 = 1 by omega]
    · rw [h2 j (by omega) (by omega) hjm, show j + (r + 2) - 2 = j + (r + 1 + 2) - 3 by omega,
        show j - (r + 2) + 1 = j - (r + 1 + 2) + 2 by omega]

/-- Correctness of Algorithm 4.3: the model computes the tangent numbers. -/
theorem tangentNumbersModel_eq {m : ℕ} (hm : 1 ≤ m) {j : ℕ} (h1 : 1 ≤ j) (hjm : j ≤ m) :
    (tangentNumbersModel m j : ℤ) = tangentNumber j :=
  (tangentOuter_spec m (m - 1) (by omega)).1 j h1 (by omega)

theorem tangentNumbersModel_three :
    tangentNumbersModel 3 1 = 1 ∧ tangentNumbersModel 3 2 = 2 ∧ tangentNumbersModel 3 3 = 16 := by
  have h1 := tangentNumbersModel_eq (m := 3) (by norm_num) (j := 1) (by norm_num) (by norm_num)
  have h2 := tangentNumbersModel_eq (m := 3) (by norm_num) (j := 2) (by norm_num) (by norm_num)
  have h3 := tangentNumbersModel_eq (m := 3) (by norm_num) (j := 3) (by norm_num) (by norm_num)
  rw [tangentNumber_one] at h1
  rw [tangentNumber_two] at h2
  rw [tangentNumber_three] at h3
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-! ### The odd zeta function and (4.65) -/

/-- The odd zeta function `∑_{n≥0} (2n+1)^(−s) = (1 − 2^(−s)) ζ(s)`. -/
noncomputable def oddZeta (s : ℝ) : ℝ := ∑' n : ℕ, (((2 * n + 1 : ℕ) : ℝ) ^ s)⁻¹

theorem one_sub_two_rpow_neg_mul_zetaReal {s : ℝ} (hs : 1 < s) :
    (1 - (2 : ℝ) ^ (-s)) * zetaReal s = oddZeta s := by
  have hsum : Summable fun n : ℕ => ((n : ℝ) ^ s)⁻¹ := Real.summable_nat_rpow_inv.mpr hs
  have he : HasSum (fun n : ℕ => (((2 * n : ℕ) : ℝ) ^ s)⁻¹) ((2 : ℝ) ^ (-s) * zetaReal s) := by
    have := hsum.hasSum.mul_left ((2 : ℝ) ^ (-s))
    refine this.congr_fun fun n => ?_
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (Nat.cast_nonneg n), mul_inv,
      Real.rpow_neg (by norm_num)]
  have ho : HasSum (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ) ^ s)⁻¹) (oddZeta s) :=
    (hsum.comp_injective (i := fun n : ℕ => 2 * n + 1) fun a b h => by simpa using h).hasSum
  have h := HasSum.even_add_odd (f := fun n : ℕ => ((n : ℝ) ^ s)⁻¹) he ho
  have h2 : zetaReal s = (2 : ℝ) ^ (-s) * zetaReal s + oddZeta s := hsum.hasSum.unique h
  linear_combination h2

/-- (4.65): `(−1)^(k−1) B_{2k} / (2k)! = 2 ζ(2k) / (2π)^(2k)` for `k ≥ 1`. -/
theorem neg_one_pow_mul_bernoulli_div_factorial {k : ℕ} (hk : 1 ≤ k) :
    (-1) ^ (k - 1) * (bernoulli (2 * k) : ℝ) / (2 * k).factorial
      = 2 * zetaReal (2 * k) / (2 * Real.pi) ^ (2 * k) := by
  have h := scaledBernoulli_eq_zeta hk
  unfold scaledBernoulli at h
  push_cast at h
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hsq : ((-1 : ℝ) ^ k') ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [show (-1 : ℝ) ^ (k' + 1 + 1) = (-1) ^ k' by rw [pow_succ, pow_succ]; ring] at h
  have hf : ((2 * (k' + 1)).factorial : ℝ) ≠ 0 := by positivity
  rw [mul_div_assoc, h]
  linear_combination
    (2 * zetaReal (2 * ((k' + 1 : ℕ) : ℝ)) / (2 * Real.pi) ^ (2 * (k' + 1))) * hsq

/-! ### (4.64) and the growth of the tangent numbers -/

/-- (4.64): `T_k / (2k−1)! = 2^(2k+1) (1 − 2^(−2k)) ζ(2k) / π^(2k)`. -/
theorem tangentNumber_div_factorial_eq_zeta (k : ℕ) :
    (tangentNumber (k + 1) : ℝ) / (2 * (k + 1) - 1).factorial
      = 2 ^ (2 * (k + 1) + 1) * (1 - ((2 : ℝ) ^ (2 * (k + 1)))⁻¹) * zetaReal (2 * (k + 1))
        / Real.pi ^ (2 * (k + 1)) := by
  have hT := congrArg (Rat.cast : ℚ → ℝ) (tangentNumber_eq_bernoulli k)
  push_cast at hT
  have hB := bernoulli_two_mul_eq_zeta (k := k + 1) (by omega)
  rw [show (-1 : ℝ) ^ (k + 1 + 1) = (-1) ^ k by rw [pow_succ, pow_succ]; ring] at hB
  have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  -- `B (−1)^k` without the sign
  have hB' : (bernoulli (2 * (k + 1)) : ℝ) * (-1) ^ k
      = 2 * (2 * (k + 1)).factorial * zetaReal (2 * ((k + 1 : ℕ) : ℝ))
        / (2 * Real.pi) ^ (2 * (k + 1)) := by
    rw [hB]
    linear_combination (2 * (2 * (k + 1)).factorial * zetaReal (2 * ((k + 1 : ℕ) : ℝ))
      / (2 * Real.pi) ^ (2 * (k + 1))) * hsq
  have h2k : (2 * ((k : ℝ) + 1)) ≠ 0 := by positivity
  have hTZ : (tangentNumber (k + 1) : ℝ) * (2 * (k + 1))
      = 4 ^ (k + 1) * (4 ^ (k + 1) - 1) * (2 * (2 * (k + 1)).factorial
        * zetaReal (2 * ((k + 1 : ℕ) : ℝ)) / (2 * Real.pi) ^ (2 * (k + 1))) := by
    rw [← hB', hT]
    field_simp
  have hT' : (tangentNumber (k + 1) : ℝ) = 4 ^ (k + 1) * (4 ^ (k + 1) - 1)
      * (2 * (2 * (k + 1)).factorial * zetaReal (2 * ((k + 1 : ℕ) : ℝ))
        / (2 * Real.pi) ^ (2 * (k + 1))) / (2 * (k + 1)) := (eq_div_iff h2k).mpr hTZ
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  have hfac : ((2 * (k + 1)).factorial : ℝ) = (2 * (k + 1)) * (2 * k + 1).factorial := by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have h4 : (4 : ℝ) ^ (k + 1) = 2 ^ (2 * (k + 1)) := by rw [pow_mul]; norm_num
  rw [hT', hfac, h4, mul_pow]
  have hπ : (0 : ℝ) < Real.pi ^ (2 * (k + 1)) := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (2 * (k + 1)) := by positivity
  have hf : (0 : ℝ) < (2 * k + 1).factorial := by positivity
  push_cast
  field_simp
  ring

/-- (4.64) with the odd zeta function: `T_k / (2k−1)! = 2^(2k+1) oddZeta(2k) / π^(2k)`. -/
theorem tangentNumber_div_factorial_eq_oddZeta (k : ℕ) :
    (tangentNumber (k + 1) : ℝ) / (2 * (k + 1) - 1).factorial
      = 2 ^ (2 * (k + 1) + 1) * oddZeta (2 * (k + 1)) / Real.pi ^ (2 * (k + 1)) := by
  have hs : (1 : ℝ) < 2 * ((k : ℝ) + 1) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [tangentNumber_div_factorial_eq_zeta, mul_assoc, ← one_sub_two_rpow_neg_mul_zetaReal hs,
    Real.rpow_neg (by norm_num), show (2 : ℝ) ^ (2 * ((k : ℝ) + 1)) = 2 ^ (2 * (k + 1)) by
      rw [show (2 : ℝ) * ((k : ℝ) + 1) = ((2 * (k + 1) : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]]

/-- The tail `∑_{n≥2} n^(−2)` is at most `2`. -/
theorem tsum_inv_sq_add_two_le : ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ 2 ≤ 2 := by
  have h2 := hasSum_zeta_two
  have h := Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) (k := 2)
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 2).mpr h2.summable)
  rw [h2.tsum_eq] at h
  have hnn : 0 ≤ ∑ i ∈ range 2, 1 / (i : ℝ) ^ 2 := sum_nonneg fun i _ => by positivity
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  linarith

/-- Termwise: `(n+2)^(−2(k+1)) ≤ 4^(−k) (n+2)^(−2)`. -/
theorem inv_pow_add_two_le (k n : ℕ) :
    ((((n + 2 : ℕ) : ℝ)) ^ (2 * (k + 1)))⁻¹ ≤ 4 / 4 ^ (k + 1) * (1 / ((n + 2 : ℕ) : ℝ) ^ 2) := by
  have hN : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hNpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by linarith
  have h4 : (4 : ℝ) ^ k ≤ ((n + 2 : ℕ) : ℝ) ^ (2 * k) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_left₀ (by norm_num) hN _
  have heq : (4 : ℝ) / 4 ^ (k + 1) * (1 / ((n + 2 : ℕ) : ℝ) ^ 2)
      = (4 ^ k * ((n + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [pow_succ]
    field_simp
  rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, heq]
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right h4 (by positivity))

/-- `ζ(2(k+1)) = 1 + ∑_{n≥2} n^(−2(k+1))`. -/
theorem zetaReal_two_mul_succ_eq (k : ℕ) :
    zetaReal (2 * ((k + 1 : ℕ) : ℝ))
      = 1 + ∑' n : ℕ, ((((n + 2 : ℕ) : ℝ)) ^ (2 * (k + 1)))⁻¹ := by
  have hcast : (2 : ℝ) * ((k + 1 : ℕ) : ℝ) = ((2 * (k + 1) : ℕ) : ℝ) := by push_cast; ring
  have hs : Summable fun n : ℕ => ((n : ℝ) ^ (2 * ((k + 1 : ℕ) : ℝ)))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
  unfold zetaReal
  rw [← Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => ((n : ℝ) ^ (2 * ((k + 1 : ℕ) : ℝ)))⁻¹)
    (k := 2) ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (2 * ((k + 1 : ℕ) : ℝ)))⁻¹) 2).mpr
      hs), sum_range_succ, sum_range_one]
  simp only [hcast, Real.rpow_natCast, Nat.cast_zero, Nat.cast_one, one_pow, inv_one]
  rw [zero_pow (by omega), inv_zero, zero_add]

/-- `ζ(2k) − 1 ≤ 8 / 4^k` for `k ≥ 1` (the `O(4^(−k))` in the text). -/
theorem zetaReal_two_mul_sub_one_le {k : ℕ} (hk : 1 ≤ k) : zetaReal (2 * k) - 1 ≤ 8 / 4 ^ k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [zetaReal_two_mul_succ_eq, add_sub_cancel_left]
  have hs : Summable fun n : ℕ => ((((n + 2 : ℕ) : ℝ)) ^ (2 * (k' + 1)))⁻¹ := by
    have := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (2 * ((k' + 1 : ℕ) : ℝ)))⁻¹) 2).mpr
      (Real.summable_nat_rpow_inv.mpr
        (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k'] : (1 : ℝ) < 2 * ((k' + 1 : ℕ) : ℝ)))
    refine this.congr fun n => ?_
    rw [show (2 : ℝ) * ((k' + 1 : ℕ) : ℝ) = ((2 * (k' + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hsum2 : Summable fun n : ℕ => 4 / 4 ^ (k' + 1) * (1 / ((n + 2 : ℕ) : ℝ) ^ 2) :=
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 2).mpr
      hasSum_zeta_two.summable).mul_left _
  calc ∑' n : ℕ, ((((n + 2 : ℕ) : ℝ)) ^ (2 * (k' + 1)))⁻¹
      ≤ ∑' n : ℕ, 4 / 4 ^ (k' + 1) * (1 / ((n + 2 : ℕ) : ℝ) ^ 2) :=
        hs.tsum_le_tsum (inv_pow_add_two_le k') hsum2
    _ = 4 / 4 ^ (k' + 1) * ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := tsum_mul_left
    _ ≤ 4 / 4 ^ (k' + 1) * 2 := by gcongr; exact tsum_inv_sq_add_two_le
    _ = 8 / 4 ^ (k' + 1) := by ring

/-- `ζ(2k) → 1` as `k → ∞`. -/
theorem tendsto_zetaReal_two_mul : Tendsto (fun k : ℕ => zetaReal (2 * k)) atTop (𝓝 1) := by
  have h8 : Tendsto (fun k : ℕ => 1 + 8 / (4 : ℝ) ^ k) atTop (𝓝 (1 + 8 * 0)) := by
    refine tendsto_const_nhds.add ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).const_mul 8
    refine this.congr fun k => ?_
    rw [one_div_pow]
    ring
  rw [mul_zero, add_zero] at h8
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h8 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk using one_le_zetaReal_two_mul hk
  · filter_upwards [eventually_ge_atTop 1] with k hk
    linarith [zetaReal_two_mul_sub_one_le hk]

/-- (4.66): `|B_{2k}| ∼ 2 (2k)! / (2π)^(2k)`. -/
theorem abs_bernoulli_isEquivalent :
    (fun k : ℕ => |(bernoulli (2 * k) : ℝ)|)
      ~[atTop] fun k : ℕ => 2 * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) := by
  refine isEquivalent_of_tendsto_one (tendsto_zetaReal_two_mul.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with k hk
  simp only [Pi.div_apply]
  rw [bernoulli_two_mul_eq_zeta hk, abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_two, abs_of_pos (by positivity : (0 : ℝ) < (2 * k).factorial),
    abs_of_nonneg (by linarith [one_le_zetaReal_two_mul hk] : (0 : ℝ) ≤ zetaReal (2 * k)),
    abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi) ^ (2 * k))]
  have hf : (0 : ℝ) < (2 * k).factorial := by positivity
  have hp : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) := by positivity
  field_simp

/-- `T_k ∼ 2 (2k−1)! (2/π)^(2k)`: the tangent numbers grow like `(2k−1)! (2/π)^(2k)`. -/
theorem tangentNumber_isEquivalent :
    (fun k : ℕ => (tangentNumber k : ℝ))
      ~[atTop] fun k : ℕ => 2 * (2 * k - 1).factorial * (2 / Real.pi) ^ (2 * k) := by
  refine isEquivalent_of_tendsto_one ?_
  -- the ratio is `(1 − 4^(−k)) ζ(2k)`
  have hlim : Tendsto (fun k : ℕ => (1 - ((2 : ℝ) ^ (2 * k))⁻¹) * zetaReal (2 * k)) atTop
      (𝓝 ((1 - 0) * 1)) := by
    refine (tendsto_const_nhds.sub ?_).mul tendsto_zetaReal_two_mul
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
    refine this.congr fun k => ?_
    rw [one_div_pow, pow_mul, one_div]
    norm_num
  rw [sub_zero, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  simp only [Pi.div_apply]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := tangentNumber_div_factorial_eq_zeta k'
  have hf : (0 : ℝ) < (2 * (k' + 1) - 1).factorial := by positivity
  have hπ : (0 : ℝ) < Real.pi ^ (2 * (k' + 1)) := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (2 * (k' + 1)) := by positivity
  rw [div_eq_iff hf.ne'] at h
  rw [h, div_pow, pow_succ (2 : ℝ) (2 * (k' + 1))]
  push_cast
  field_simp

end BZ

end Azurite
