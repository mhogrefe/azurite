/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.RepeatedDoubling
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Brent–Zimmermann §4.4: Power series (introduction)

After argument reduction one evaluates a power series, such as `exp x = ∑ x^j/j!` or
`ln(1 + x) = ∑ (−1)^j x^(j+1)/(j+1)`.  Notation: `x` the point, `n` the target precision, `d` the
number of terms.  The instructive example is `exp x` for `|x| ≤ 1`:

  `exp x = ∑_{j<d} x^j/j! + R_d(x)`,  `|R_d(x)| ≤ |x|^d exp|x| / d! ≤ e / d!`,            (4.21)

so `d ~ n / lg n` terms suffice (Stirling) and Horner costs `O(n M(n) / log n)`.  Forward summation
generates `t_j = x t_{j−1} / j`, `S_j = S_{j−1} + t_j` and stops when `|t_d| < 2^(−n) / e`, so `d`
need not be known in advance (unlike backward summation).  With correctly rounded operations,
`◦(x op y) = (x op y)(1 + δ)`, `|δ| ≤ ε = 2^(−n)`: `|tc_j − t_j| / |t_j| ≤ 2jε + O(ε²)` and
`|Ŝ_d − S_d| ≤ (d + 2) e ε + O(ε²) = O(nε)`, so `ε = O(2^(−n)/n)` suffices: about `lg n` guard
digits.  The working precision can be reduced for small terms.  For large `x > 0` the terms grow
until `j ≈ |x|`, so `Ω(|x|)` terms are needed; for large negative `x` the largest term is
`≈ exp|x| / √(2π|x|)` against a result `exp(−|x|)`: about `2|x| / log 2` guard digits
("catastrophic cancellation"), avoided by `exp x = 1/exp(−x)`.  For `erf` the two series (4.22)
and (4.23) are mathematically but not numerically equivalent — (4.23) has no cancellation; for
large `|x|` both need `Ω(x²)` terms and the asymptotic expansion of `erfc` (§4.5) is preferable.

What is formalized:

* `hasSum_exp_series`, `hasSum_log_one_add_series` — the expansions of `exp` and `ln(1 + x)`
  (`|x| < 1`) from Mathlib.
* `abs_exp_sub_sum_le` — the remainder bound of (4.21), `|R_d(x)| ≤ |x|^d/d! · exp|x|`, for every
  `x`; `abs_exp_sub_sum_le_of_abs_le_one` (`≤ e/d!`), `exp_series_terms_suffice`
  (`2^n e ≤ d!` gives `|R_d| ≤ 2^(−n)`), `exp_series_stop` (the stopping rule: `|t_d| < 2^(−n)/e`
  gives `|R_d| < 2^(−n)`).
* `expPartial`, `expPartial_succ` — the forward recurrence (`expTerm_succ` is in §4.3.2).
* `roundedExpTerm`, `roundedExpTerm_eq`, `abs_roundedExpTerm_sub_le` — the terms computed with
  a relative rounding error `θ_j` per step (`|θ_j| ≤ 3ε` covers the multiplication and the
  division): `|tc_j − t_j| ≤ 6jε |t_j|` for `3jε ≤ 1`.
* `roundedSum`, `roundedSum_sub_le` — forward summation with a relative error `σ_j` per
  addition: the generic bound `|Ŝ_d − S_d| ≤ (1+ε)^d (η ∑|t_j| + d ε (M + (1+η) T))`.
* `exp_roundedSum_error` — for `|x| ≤ 1`: `|Ŝ_d − S_d| ≤ 46 d ε` once `6dε ≤ 1`, and
  `exp_guard_digits`: `ε ≤ 2^(−n) / (46 d)` gives `|Ŝ_d − S_d| ≤ 2^(−n)` — the `lg n` guard digits.
* `guard_digits_of_neg` — `logb 2 (exp (2|x|)) = 2|x| / log 2`, the bits lost to cancellation
  (§4.3.2 gave the factor).

Not formalized: Stirling (`d ~ n/lg n`), the Horner cost, the Stirling estimate of the largest
term, the `erf` series (no `erf` in Mathlib; (4.22)/(4.23) await the asymptotic-expansion
section), the arctan and sinh expansions (not in Mathlib).
-/

namespace Azurite

namespace BZ

open Finset Real

/-! ### The expansions -/

/-- `exp x = ∑ x^j / j!`. -/
theorem hasSum_exp_series (x : ℝ) : HasSum (fun j : ℕ => x ^ j / j.factorial) (exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- `ln(1 + x) = ∑ (−1)^j x^(j+1) / (j + 1)` for `|x| < 1`. -/
theorem hasSum_log_one_add_series {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j : ℕ => (-1) ^ j * x ^ (j + 1) / (j + 1)) (log (1 + x)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by rwa [abs_neg])
  rw [sub_neg_eq_add] at h
  have h' := h.neg
  rw [neg_neg] at h'
  convert h' using 1
  funext j
  rw [neg_pow, pow_succ]
  ring

/-! ### The remainder of the exponential series, (4.21) -/

/-- The remainder bound `|exp x − ∑_{j<d} x^j/j!| ≤ |x|^d / d! · exp |x|`, for every `x`. -/
theorem abs_exp_sub_sum_le (x : ℝ) (d : ℕ) :
    |exp x - ∑ j ∈ range d, x ^ j / j.factorial| ≤ |x| ^ d / d.factorial * exp |x| := by
  have hs := hasSum_exp_series x
  have hsum := hs.summable
  have hsh : Summable (fun n : ℕ => x ^ (n + d) / (n + d).factorial) :=
    hsum.comp_injective (add_left_injective d)
  have hsplit := Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => x ^ n / n.factorial) (k := d) hsh
  rw [hs.tsum_eq] at hsplit
  have htail : exp x - ∑ j ∈ range d, x ^ j / j.factorial
      = ∑' n : ℕ, x ^ (n + d) / (n + d).factorial := by
    linarith
  have hsa := hasSum_exp_series |x|
  have hsabs : Summable (fun n : ℕ => |x| ^ n / n.factorial) := hsa.summable
  have hb : ∀ n : ℕ, |x ^ (n + d) / (n + d).factorial|
      ≤ |x| ^ d / d.factorial * (|x| ^ n / n.factorial) := by
    intro n
    have hfpos : (0 : ℝ) < (n + d).factorial := by exact_mod_cast (n + d).factorial_pos
    rw [abs_div, abs_pow, abs_of_pos hfpos, pow_add, div_le_iff₀ hfpos]
    have hdiv : (d.factorial * n.factorial : ℝ) ≤ (n + d).factorial := by
      have := Nat.factorial_mul_factorial_dvd_factorial_add d n
      rw [add_comm] at this
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) this
    have hd : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
    have hn : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    calc |x| ^ n * |x| ^ d
        = |x| ^ d / d.factorial * (|x| ^ n / n.factorial) * (d.factorial * n.factorial) := by
          field_simp
      _ ≤ |x| ^ d / d.factorial * (|x| ^ n / n.factorial) * (n + d).factorial := by
          gcongr
  have hsb : Summable (fun n : ℕ => |x| ^ d / d.factorial * (|x| ^ n / n.factorial)) :=
    hsabs.mul_left _
  rw [htail]
  calc |∑' n : ℕ, x ^ (n + d) / (n + d).factorial|
      ≤ ∑' n : ℕ, |x ^ (n + d) / (n + d).factorial| := by
        have := norm_tsum_le_tsum_norm hsh.norm
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' n : ℕ, |x| ^ d / d.factorial * (|x| ^ n / n.factorial) :=
        hsh.abs.tsum_le_tsum hb hsb
    _ = |x| ^ d / d.factorial * exp |x| := by rw [tsum_mul_left, hsa.tsum_eq]

/-- For `|x| ≤ 1`, `|R_d(x)| ≤ e / d!`. -/
theorem abs_exp_sub_sum_le_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) (d : ℕ) :
    |exp x - ∑ j ∈ range d, x ^ j / j.factorial| ≤ exp 1 / d.factorial := by
  refine (abs_exp_sub_sum_le x d).trans ?_
  have hd : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  calc |x| ^ d / d.factorial * exp |x| ≤ 1 ^ d / d.factorial * exp 1 := by gcongr
    _ = exp 1 / d.factorial := by ring

/-- `d` terms suffice for `n` bits as soon as `2^n e ≤ d!`. -/
theorem exp_series_terms_suffice {x : ℝ} (hx : |x| ≤ 1) {d n : ℕ}
    (hd : (2 : ℝ) ^ n * exp 1 ≤ d.factorial) :
    |exp x - ∑ j ∈ range d, x ^ j / j.factorial| ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  refine (abs_exp_sub_sum_le_of_abs_le_one hx d).trans ?_
  have hdpos : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  rw [zpow_neg, zpow_natCast, div_le_iff₀ hdpos]
  calc exp 1 = (2 : ℝ) ^ n * exp 1 / 2 ^ n := by field_simp
    _ ≤ d.factorial / 2 ^ n := by gcongr
    _ = ((2 : ℝ) ^ n)⁻¹ * d.factorial := by ring

/-- The stopping rule of forward summation: for `|x| ≤ 1`, once the next term satisfies
`|t_d| < 2^(−n) / e`, the remainder is below `2^(−n)`. -/
theorem exp_series_stop {x : ℝ} (hx : |x| ≤ 1) {d n : ℕ}
    (ht : |expTerm x d| < (2 : ℝ) ^ (-(n : ℤ)) / exp 1) :
    |exp x - ∑ j ∈ range d, x ^ j / j.factorial| < (2 : ℝ) ^ (-(n : ℤ)) := by
  have h := abs_exp_sub_sum_le x d
  have hdpos : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have ht' : |expTerm x d| = |x| ^ d / d.factorial := by
    unfold expTerm; rw [abs_div, abs_pow, abs_of_pos hdpos]
  rw [ht'] at ht
  calc |exp x - ∑ j ∈ range d, x ^ j / j.factorial| ≤ |x| ^ d / d.factorial * exp |x| := h
    _ ≤ |x| ^ d / d.factorial * exp 1 := by gcongr
    _ < (2 : ℝ) ^ (-(n : ℤ)) / exp 1 * exp 1 :=
        mul_lt_mul_of_pos_right ht (exp_pos 1)
    _ = (2 : ℝ) ^ (-(n : ℤ)) := div_mul_cancel₀ _ (exp_pos 1).ne'

/-! ### Forward summation and its rounding errors -/

/-- The partial sums `S_j = ∑_{i≤j} t_i`. -/
noncomputable def expPartial (x : ℝ) (j : ℕ) : ℝ := ∑ i ∈ range (j + 1), expTerm x i

theorem expPartial_succ (x : ℝ) (j : ℕ) :
    expPartial x (j + 1) = expPartial x j + expTerm x (j + 1) := by
  unfold expPartial; rw [sum_range_succ]

/-- The terms as computed, `tc_0 = 1` and `tc_j = (tc_{j−1} x / j)(1 + θ_j)`, where `θ_j` is the
relative error of the multiplication and the division together. -/
noncomputable def roundedExpTerm (x : ℝ) (θ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => roundedExpTerm x θ j * x / (j + 1) * (1 + θ (j + 1))

/-- `tc_j = t_j ∏_{i<j} (1 + θ_{i+1})`. -/
theorem roundedExpTerm_eq (x : ℝ) (θ : ℕ → ℝ) (j : ℕ) :
    roundedExpTerm x θ j = expTerm x j * ∏ i ∈ range j, (1 + θ (i + 1)) := by
  induction j with
  | zero => simp [roundedExpTerm, expTerm]
  | succ j ih =>
    rw [roundedExpTerm, ih, expTerm_succ, prod_range_succ]
    ring

/-- `|tc_j − t_j| ≤ 6 j ε |t_j|` when every `|θ_i| ≤ 3ε` and `3 j ε ≤ 1`. -/
theorem abs_roundedExpTerm_sub_le (x : ℝ) {θ : ℕ → ℝ} {ε : ℝ} (hθ : ∀ i, |θ i| ≤ 3 * ε) {j : ℕ}
    (hj : 3 * j * ε ≤ 1) :
    |roundedExpTerm x θ j - expTerm x j| ≤ 6 * j * ε * |expTerm x j| := by
  have hε0 : 0 ≤ ε := by linarith [abs_nonneg (θ 0), hθ 0]
  rw [roundedExpTerm_eq, ← mul_sub_one, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have h1 := abs_prod_one_add_pow_sub_one_le (fun i => θ (i + 1)) (fun _ => 1) j
  have h2 := prod_one_add_abs_pow_le_exp (fun i => θ (i + 1)) (fun _ => 1) j
  simp only [pow_one, Nat.cast_one, one_mul] at h1 h2
  have hS : ∑ i ∈ range j, |θ (i + 1)| ≤ 3 * j * ε := by
    calc ∑ i ∈ range j, |θ (i + 1)| ≤ ∑ _i ∈ range j, 3 * ε := sum_le_sum fun i _ => hθ (i + 1)
      _ = 3 * j * ε := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hS0 : 0 ≤ ∑ i ∈ range j, |θ (i + 1)| := sum_nonneg fun i _ => abs_nonneg _
  calc |∏ i ∈ range j, (1 + θ (i + 1)) - 1| ≤ ∏ i ∈ range j, (1 + |θ (i + 1)|) - 1 := h1
    _ ≤ exp (∑ i ∈ range j, |θ (i + 1)|) - 1 := by linarith
    _ ≤ 2 * ∑ i ∈ range j, |θ (i + 1)| := exp_sub_one_le_two_mul hS0 (hS.trans hj)
    _ ≤ 2 * (3 * j * ε) := by gcongr
    _ = 6 * j * ε := by ring

/-- Forward summation as computed: `Ŝ_0 = tc_0`, `Ŝ_{j+1} = (Ŝ_j + tc_{j+1})(1 + σ_{j+1})`. -/
noncomputable def roundedSum (tc σ : ℕ → ℝ) : ℕ → ℝ
  | 0 => tc 0
  | j + 1 => (roundedSum tc σ j + tc (j + 1)) * (1 + σ (j + 1))

/-- The generic forward-summation error: with `|σ_j| ≤ ε`, `|tc_j − t_j| ≤ η |t_j|`,
`|∑_{i≤j} t_i| ≤ M` and `|t_j| ≤ T` for all `j`,
`|Ŝ_d − S_d| ≤ (1 + ε)^d (η ∑_{j≤d} |t_j| + d ε (M + (1 + η) T))`. -/
theorem roundedSum_sub_le (t tc σ : ℕ → ℝ) {ε η M T : ℝ} (hη0 : 0 ≤ η) (hσ : ∀ j, |σ j| ≤ ε)
    (htc : ∀ j, |tc j - t j| ≤ η * |t j|) (hM : ∀ j, |∑ i ∈ range (j + 1), t i| ≤ M)
    (hT : ∀ j, |t j| ≤ T) (d : ℕ) :
    |roundedSum tc σ d - ∑ i ∈ range (d + 1), t i|
      ≤ (1 + ε) ^ d * (η * ∑ i ∈ range (d + 1), |t i| + d * ε * (M + (1 + η) * T)) := by
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hσ 0)
  have hT0 : 0 ≤ T := le_trans (abs_nonneg _) (hT 0)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  induction d with
  | zero =>
    simp only [roundedSum, zero_add, sum_range_one, pow_zero, one_mul, Nat.cast_zero, zero_mul,
      add_zero]
    exact htc 0
  | succ d ih =>
    set A := roundedSum tc σ d - ∑ i ∈ range (d + 1), t i with hA
    set X := η * ∑ i ∈ range (d + 1), |t i| + d * ε * (M + (1 + η) * T) with hX
    have hX0 : 0 ≤ X := by positivity
    -- the recurrence for the error
    have hrec : roundedSum tc σ (d + 1) - ∑ i ∈ range (d + 1 + 1), t i
        = A + (tc (d + 1) - t (d + 1))
          + σ (d + 1) * (∑ i ∈ range (d + 1), t i + A + tc (d + 1)) := by
      rw [roundedSum, sum_range_succ _ (d + 1), hA]; ring
    have htcb : |tc (d + 1)| ≤ (1 + η) * T := by
      calc |tc (d + 1)| = |t (d + 1) + (tc (d + 1) - t (d + 1))| := by ring_nf
        _ ≤ |t (d + 1)| + |tc (d + 1) - t (d + 1)| := abs_add_le _ _
        _ ≤ T + η * T := by
            gcongr
            · exact hT _
            · exact (htc _).trans (by gcongr; exact hT _)
        _ = (1 + η) * T := by ring
    have hstep : |roundedSum tc σ (d + 1) - ∑ i ∈ range (d + 1 + 1), t i|
        ≤ (1 + ε) * |A| + η * |t (d + 1)| + ε * (M + (1 + η) * T) := by
      rw [hrec]
      calc |A + (tc (d + 1) - t (d + 1)) + σ (d + 1) * (∑ i ∈ range (d + 1), t i + A + tc (d + 1))|
          ≤ |A| + |tc (d + 1) - t (d + 1)|
            + |σ (d + 1)| * (|∑ i ∈ range (d + 1), t i| + |A| + |tc (d + 1)|) := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            · exact abs_add_le _ _
            · rw [abs_mul]
              gcongr
              exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
        _ ≤ |A| + η * |t (d + 1)| + ε * (M + |A| + (1 + η) * T) := by
            gcongr
            · exact htc _
            · exact hσ _
            · exact hM _
        _ = (1 + ε) * |A| + η * |t (d + 1)| + ε * (M + (1 + η) * T) := by ring
    have hpow : (1 : ℝ) ≤ (1 + ε) ^ (d + 1) := one_le_pow₀ (by linarith)
    calc |roundedSum tc σ (d + 1) - ∑ i ∈ range (d + 1 + 1), t i|
        ≤ (1 + ε) * |A| + η * |t (d + 1)| + ε * (M + (1 + η) * T) := hstep
      _ ≤ (1 + ε) * ((1 + ε) ^ d * X) + η * |t (d + 1)| + ε * (M + (1 + η) * T) := by
          gcongr
      _ ≤ (1 + ε) ^ (d + 1) * X
          + (1 + ε) ^ (d + 1) * (η * |t (d + 1)| + ε * (M + (1 + η) * T)) := by
          have h0 : 0 ≤ η * |t (d + 1)| + ε * (M + (1 + η) * T) := by positivity
          have h2 := le_mul_of_one_le_left h0 hpow
          have h1 : (1 + ε) * ((1 + ε) ^ d * X) = (1 + ε) ^ (d + 1) * X := by ring
          linarith
      _ = (1 + ε) ^ (d + 1) * (η * ∑ i ∈ range (d + 1 + 1), |t i|
            + (d + 1 : ℕ) * ε * (M + (1 + η) * T)) := by
          rw [sum_range_succ _ (d + 1), hX]; push_cast; ring

/-- Forward summation of the exponential series for `|x| ≤ 1` with correctly rounded
operations (`|θ_j| ≤ 3ε` for the terms, `|σ_j| ≤ ε` for the additions): once `6dε ≤ 1`,
`|Ŝ_d − S_d| ≤ 46 d ε`. -/
theorem exp_roundedSum_error {x : ℝ} (hx : |x| ≤ 1) {θ σ : ℕ → ℝ} {ε : ℝ}
    (hθ : ∀ i, |θ i| ≤ 3 * ε) (hσ : ∀ j, |σ j| ≤ ε) {d : ℕ} (hd : 6 * d * ε ≤ 1) :
    |roundedSum (roundedExpTerm x θ) σ d - expPartial x d| ≤ 46 * d * ε := by
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hσ 0)
  -- uniform bounds on the terms and partial sums
  have hT : ∀ j, |expTerm x j| ≤ 1 := by
    intro j
    unfold expTerm
    have hf : (1 : ℝ) ≤ j.factorial := by exact_mod_cast j.factorial_pos
    have hfpos : (0 : ℝ) < j.factorial := by linarith
    rw [abs_div, abs_pow, abs_of_pos hfpos, div_le_one hfpos]
    exact (pow_le_one₀ (abs_nonneg _) hx).trans hf
  have hM : ∀ j, |∑ i ∈ range (j + 1), expTerm x i| ≤ exp 1 := by
    intro j
    calc |∑ i ∈ range (j + 1), expTerm x i| ≤ ∑ i ∈ range (j + 1), |expTerm x i| :=
          abs_sum_le_sum_abs _ _
      _ ≤ exp |x| := sum_abs_expTerm_le x _
      _ ≤ exp 1 := exp_le_exp.mpr hx
  -- the per-term relative error, uniform in `j ≤ d`: `6 j ε ≤ 6 d ε`
  have htc : ∀ j, |roundedExpTerm x θ j - expTerm x j| ≤ 6 * d * ε * |expTerm x j| ∨ d < j := by
    intro j
    by_cases hj : j ≤ d
    · left
      have hj' : 3 * j * ε ≤ 1 := by
        calc 3 * (j : ℝ) * ε ≤ 3 * d * ε := by gcongr
          _ ≤ 6 * d * ε := by nlinarith
          _ ≤ 1 := hd
      calc |roundedExpTerm x θ j - expTerm x j| ≤ 6 * j * ε * |expTerm x j| :=
            abs_roundedExpTerm_sub_le x hθ hj'
        _ ≤ 6 * d * ε * |expTerm x j| := by gcongr
    · right; omega
  -- the generic bound needs the term bound for all `j`; truncate the computed terms beyond `d`
  set tc : ℕ → ℝ := fun j => if j ≤ d then roundedExpTerm x θ j else expTerm x j with htc_def
  have htc' : ∀ j, |tc j - expTerm x j| ≤ 6 * d * ε * |expTerm x j| := by
    intro j
    by_cases hj : j ≤ d
    · simp only [htc_def, hj, ↓reduceIte]
      rcases htc j with h | h
      · exact h
      · omega
    · simp only [htc_def, hj, ↓reduceIte, sub_self, abs_zero]; positivity
  have hsame : roundedSum tc σ d = roundedSum (roundedExpTerm x θ) σ d := by
    have : ∀ j ≤ d, roundedSum tc σ j = roundedSum (roundedExpTerm x θ) σ j := by
      intro j
      induction j with
      | zero => intro _; simp [roundedSum, htc_def]
      | succ j ih =>
        intro hj
        rw [roundedSum, roundedSum, ih (by omega)]
        simp only [htc_def, hj, ↓reduceIte]
    exact this d le_rfl
  have hsum : ∑ i ∈ range (d + 1), |expTerm x i| ≤ exp 1 :=
    (sum_abs_expTerm_le x _).trans (exp_le_exp.mpr hx)
  have hgen := roundedSum_sub_le (expTerm x) tc σ (by positivity) hσ htc' hM hT d
  rw [hsame] at hgen
  have he : exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hdε : 0 ≤ (d : ℝ) * ε := by positivity
  have hdε1 : (d : ℝ) * ε ≤ 1 := by nlinarith
  have hpow : (1 + ε) ^ d ≤ 2 := by
    calc (1 + ε) ^ d ≤ exp ε ^ d :=
          pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp ε]) d
      _ = exp (d * ε) := by rw [← Real.exp_nat_mul]
      _ ≤ 2 := by linarith [exp_sub_one_le_two_mul hdε hdε1]
  have hinner : 6 * d * ε * ∑ i ∈ range (d + 1), |expTerm x i|
      + d * ε * (exp 1 + (1 + 6 * d * ε) * 1) ≤ 6 * d * ε * 3 + d * ε * (3 + 2) := by
    have h1 : 6 * d * ε * ∑ i ∈ range (d + 1), |expTerm x i| ≤ 6 * d * ε * 3 :=
      mul_le_mul_of_nonneg_left (hsum.trans he) (by positivity)
    have h2 : d * ε * (exp 1 + (1 + 6 * d * ε) * 1) ≤ d * ε * (3 + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hdε
    linarith
  unfold expPartial
  calc |roundedSum (roundedExpTerm x θ) σ d - ∑ i ∈ range (d + 1), expTerm x i|
      ≤ (1 + ε) ^ d * (6 * d * ε * ∑ i ∈ range (d + 1), |expTerm x i|
          + d * ε * (exp 1 + (1 + 6 * d * ε) * 1)) := hgen
    _ ≤ 2 * (6 * d * ε * 3 + d * ε * (3 + 2)) :=
        mul_le_mul hpow hinner (by positivity) (by norm_num)
    _ = 46 * d * ε := by ring

/-- The guard digits: `ε ≤ 2^(−n) / (46 d)` gives `|Ŝ_d − S_d| ≤ 2^(−n)`; with `d = O(n)` this is
`ε = O(2^(−n) / n)`, about `lg n` extra bits of working precision. -/
theorem exp_guard_digits {x : ℝ} (hx : |x| ≤ 1) {θ σ : ℕ → ℝ} {ε : ℝ} {d n : ℕ}
    (hθ : ∀ i, |θ i| ≤ 3 * ε) (hσ : ∀ j, |σ j| ≤ ε) (hd : 6 * d * ε ≤ 1) (hd0 : 0 < d)
    (hε : ε ≤ (2 : ℝ) ^ (-(n : ℤ)) / (46 * d)) :
    |roundedSum (roundedExpTerm x θ) σ d - expPartial x d| ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  refine (exp_roundedSum_error hx hθ hσ hd).trans ?_
  have hd' : (0 : ℝ) < 46 * d := by positivity
  calc 46 * (d : ℝ) * ε ≤ 46 * d * ((2 : ℝ) ^ (-(n : ℤ)) / (46 * d)) := by gcongr
    _ = (2 : ℝ) ^ (-(n : ℤ)) := by field_simp

/-- The guard digits lost to cancellation for negative `x` (§4.3.2): the factor `exp (2|x|)` is
`2|x| / log 2` bits. -/
theorem guard_digits_of_neg (x : ℝ) : Real.logb 2 (exp (2 * |x|)) = 2 * |x| / Real.log 2 := by
  rw [Real.logb, Real.log_exp]

end BZ

end Azurite
