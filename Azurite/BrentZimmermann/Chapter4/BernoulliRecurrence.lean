/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.BesselRecurrence
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.NumberTheory.Bernoulli

/-!
# Brent–Zimmermann §4.7.2: Evaluation of Bernoulli and tangent numbers

The Bernoulli numbers `B_k` and the scaled Bernoulli numbers `C_k = B_{2k}/(2k)!` (needed in
(4.35) and (4.38)) have the generating functions

  `∑_{k≥0} B_k x^k/k! = x/(e^x − 1)`,                                                        (4.56)

  `∑_{k≥0} C_k x^(2k) = x/(e^x − 1) + x/2 = (x/2)/tanh(x/2)`.                                (4.57)

Multiplying by `e^x − 1` and equating coefficients gives the recurrences

  `B_0 = 1`,  `∑_{j=0}^{k} C(k+1, j) B_j = 0` for `k > 0`,                                    (4.58)

  `∑_{j=0}^{k} C_j/(2k+1−2j)! = 1/(2 (2k)!)`,                                                 (4.59)

and multiplying (4.57) by `sinh(x/2)/x` instead gives the numerically stable

  `∑_{j=0}^{k} C_j/((2k+1−2j)! 4^(k−j)) = 1/((2k)! 4^k)`.                                     (4.60)

Forward evaluation of (4.58)/(4.59) in precision `n` has relative error of order `4^k 2^(−n)`
(Exercise 4.35); (4.60) only `O(k² 2^(−n))`.

What is formalized (all proven, in `ℚ` and in `ℚ⟦X⟧`):

* `scaledBernoulli k = bernoulli (2k) / (2k)!` (`C_k`); `scaledBernoulli_zero`, `_one`.
* (4.56) is Mathlib's `bernoulliPowerSeries_mul_exp_sub_one`.  (4.57):
  `scaledBernoulliPowerSeries = bernoulliPowerSeries ℚ + C (1/2) X`, whose coefficients are
  `C_k` at `x^(2k)` and `0` at odd powers (`coeff_scaledBernoulliPowerSeries_even/odd`, using
  `B_1 = −1/2` and `B_{2j+1} = 0`), with `scaledBernoulliPowerSeries_mul_exp_sub_one`
  (`S (e^x − 1) = x + (x/2)(e^x − 1)`); and the real identity `div_exp_sub_one_add_half`
  (`x/(e^x − 1) + x/2 = (x/2)/tanh(x/2)` for `x ≠ 0`, via `tanh(x/2) = (e^x − 1)/(e^x + 1)`).
* (4.58): `bernoulli_recurrence` (from Mathlib's `sum_bernoulli`).
* (4.59): `scaledBernoulli_rec`, for `k ≥ 1` (at `k = 0` the sum is `C_0 = 1`, not `1/2`), by
  extracting the coefficient of `x^(2k+1)` from `S (e^x − 1)`
  (`coeff_scaledBernoulliPowerSeries_mul` splits the antidiagonal sum into even and odd
  indices with `sum_range_two_mul`).
* (4.60): `scaledBernoulli_rec_stable`, for all `k`, from
  `scaledBernoulliPowerSeries_mul_sinh` (`S (e^(x/2) − e^(−x/2)) = (x/2)(e^(x/2) + e^(−x/2))`,
  i.e. (4.57) times `2 sinh(x/2)`, obtained from (4.57) by multiplying with `e^(−x/2)` through
  `PowerSeries.exp_mul_exp_eq_exp_add`) at the coefficient of `x^(2k+1)`.
* The size of `C_k`: `scaledBernoulli_eq_zeta` (`C_k = (−1)^(k+1) 2 ζ(2k)/(2π)^(2k)`) and
  `abs_scaledBernoulli_le` (`|C_k| ≤ (π²/3)/(2π)^(2k)`), the quantities behind the stability
  remarks.

Not formalized: convergence of (4.56)/(4.57) as real power series (radius `2π`; not in
Mathlib), the rounding-error analysis (`4^k 2^(−n)` versus `O(k² 2^(−n))`, Exercise 4.35), and
the tangent numbers (the section title; they appear in later chunks).
-/

namespace Azurite

namespace BZ

open Finset PowerSeries

/-! ### The scaled Bernoulli numbers and the generating functions (4.56), (4.57) -/

/-- The scaled Bernoulli numbers `C_k = B_{2k}/(2k)!`. -/
def scaledBernoulli (k : ℕ) : ℚ := bernoulli (2 * k) / (2 * k).factorial

theorem scaledBernoulli_zero : scaledBernoulli 0 = 1 := by simp [scaledBernoulli]

theorem scaledBernoulli_one : scaledBernoulli 1 = 1 / 12 := by
  simp [scaledBernoulli, bernoulli_two]; norm_num

/-- Even/odd split of a sum over `range (2m)`. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ j ∈ range m, f (2 * j) + ∑ j ∈ range m, f (2 * j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    abel

theorem algebraMap_rat_rat (q : ℚ) : algebraMap ℚ ℚ q = q := rfl

/-- (4.57) as a formal power series: `x/(e^x − 1) + x/2`, whose coefficients are
`C_k` at `x^(2k)` and `0` at the odd powers. -/
noncomputable def scaledBernoulliPowerSeries : PowerSeries ℚ :=
  bernoulliPowerSeries ℚ + C (1 / 2 : ℚ) * X

theorem coeff_scaledBernoulliPowerSeries_even (j : ℕ) :
    coeff (2 * j) scaledBernoulliPowerSeries = scaledBernoulli j := by
  unfold scaledBernoulliPowerSeries bernoulliPowerSeries scaledBernoulli
  rw [map_add, coeff_mk, coeff_C_mul, coeff_X, ite_eq_right (by omega), mul_zero, add_zero,
    algebraMap_rat_rat]

theorem coeff_scaledBernoulliPowerSeries_odd (j : ℕ) :
    coeff (2 * j + 1) scaledBernoulliPowerSeries = 0 := by
  unfold scaledBernoulliPowerSeries bernoulliPowerSeries
  rw [map_add, coeff_mk, coeff_C_mul, coeff_X, algebraMap_rat_rat]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [bernoulli_one]
    norm_num
  · rw [bernoulli_eq_zero_of_odd ⟨j, rfl⟩ (by omega), ite_eq_right (by omega)]
    simp

/-- (4.57) times `e^x − 1`: `S (e^x − 1) = x + (x/2)(e^x − 1)` (from (4.56)). -/
theorem scaledBernoulliPowerSeries_mul_exp_sub_one :
    scaledBernoulliPowerSeries * (exp ℚ - 1) = X + C (1 / 2 : ℚ) * X * (exp ℚ - 1) := by
  unfold scaledBernoulliPowerSeries
  rw [add_mul, bernoulliPowerSeries_mul_exp_sub_one]

/-- `tanh(x/2) = (e^x − 1)/(e^x + 1)`. -/
theorem tanh_half_eq (x : ℝ) : Real.tanh (x / 2) = (Real.exp x - 1) / (Real.exp x + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  have hu : 0 < Real.exp (x / 2) := Real.exp_pos _
  have hx : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [hx]
  field_simp

/-- The closed form in (4.57): `x/(e^x − 1) + x/2 = (x/2)/tanh(x/2)` for `x ≠ 0`. -/
theorem div_exp_sub_one_add_half {x : ℝ} (hx : x ≠ 0) :
    x / (Real.exp x - 1) + x / 2 = (x / 2) / Real.tanh (x / 2) := by
  have h1 : Real.exp x - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hx (Real.exp_eq_one_iff x |>.mp h)
  have h2 : Real.exp x + 1 ≠ 0 := by positivity
  rw [tanh_half_eq, div_div_eq_mul_div]
  field_simp
  ring

/-! ### The recurrences (4.58) and (4.59) -/

/-- (4.58): `∑_{j=0}^{k} C(k+1, j) B_j = 0` for `k > 0` (Mathlib's `sum_bernoulli`). -/
theorem bernoulli_recurrence {k : ℕ} (hk : 0 < k) :
    ∑ j ∈ range (k + 1), ((k + 1).choose j : ℚ) * bernoulli j = 0 := by
  rw [sum_bernoulli, ite_eq_right (by omega)]

/-- The coefficients of `e^x − 1`. -/
theorem coeff_exp_sub_one (m : ℕ) :
    coeff m (exp ℚ - 1) = if m = 0 then 0 else 1 / (m.factorial : ℚ) := by
  rw [map_sub, coeff_exp, coeff_one, algebraMap_rat_rat]
  split_ifs with h <;> simp [h]

/-- The coefficient of `x^(2k+1)` in `S ψ`: only the even coefficients `C_j` of `S` enter. -/
theorem coeff_scaledBernoulliPowerSeries_mul (ψ : PowerSeries ℚ) (k : ℕ) :
    coeff (2 * k + 1) (scaledBernoulliPowerSeries * ψ)
      = ∑ j ∈ range (k + 1), scaledBernoulli j * coeff (2 * k + 1 - 2 * j) ψ := by
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, sum_range_two_mul,
    show ∑ j ∈ range (k + 1), coeff (2 * j + 1) scaledBernoulliPowerSeries
        * coeff (2 * k + 1 - (2 * j + 1)) ψ = 0 from
      sum_eq_zero fun j _ => by rw [coeff_scaledBernoulliPowerSeries_odd, zero_mul], add_zero]
  exact sum_congr rfl fun j _ => by rw [coeff_scaledBernoulliPowerSeries_even]

/-- (4.59): `∑_{j=0}^{k} C_j/(2k+1−2j)! = 1/(2 (2k)!)` for `k ≥ 1`. -/
theorem scaledBernoulli_rec {k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ range (k + 1), scaledBernoulli j / ((2 * k + 1 - 2 * j).factorial : ℚ)
      = 1 / (2 * (2 * k).factorial) := by
  have h := congrArg (coeff (2 * k + 1)) scaledBernoulliPowerSeries_mul_exp_sub_one
  rw [coeff_scaledBernoulliPowerSeries_mul, map_add, coeff_X, ite_eq_right (by omega), mul_assoc,
    coeff_C_mul, coeff_succ_X_mul, coeff_exp_sub_one, ite_eq_right (by omega), zero_add] at h
  have h2 : ∑ j ∈ range (k + 1), scaledBernoulli j / ((2 * k + 1 - 2 * j).factorial : ℚ)
      = ∑ j ∈ range (k + 1), scaledBernoulli j * coeff (2 * k + 1 - 2 * j) (exp ℚ - 1) :=
    sum_congr rfl fun j hj => by
      have := mem_range.mp hj
      rw [coeff_exp_sub_one, ite_eq_right (by omega), div_eq_mul_one_div]
  rw [h2, h]
  ring

/-! ### The stable recurrence (4.60) -/

theorem coeff_rescale_exp (a : ℚ) (m : ℕ) :
    coeff m (rescale a (exp ℚ)) = a ^ m / m.factorial := by
  rw [coeff_rescale, coeff_exp, algebraMap_rat_rat]
  ring

/-- `(e^x − 1) e^(−x/2) = e^(x/2) − e^(−x/2)`. -/
theorem exp_sub_one_mul_rescale_neg_half :
    (exp ℚ - 1) * rescale (-1 / 2 : ℚ) (exp ℚ)
      = rescale (1 / 2 : ℚ) (exp ℚ) - rescale (-1 / 2 : ℚ) (exp ℚ) := by
  have h := exp_mul_exp_eq_exp_add (1 : ℚ) (-1 / 2)
  rw [rescale_one, RingHom.id_apply, show (1 : ℚ) + -1 / 2 = 1 / 2 by norm_num] at h
  rw [sub_mul, one_mul, h]

/-- (4.57) times `2 sinh(x/2)`: `S (e^(x/2) − e^(−x/2)) = (x/2)(e^(x/2) + e^(−x/2))`, i.e.
`(x/2)/tanh(x/2) · 2 sinh(x/2) = x cosh(x/2)`. -/
theorem scaledBernoulliPowerSeries_mul_sinh :
    scaledBernoulliPowerSeries * (rescale (1 / 2 : ℚ) (exp ℚ) - rescale (-1 / 2 : ℚ) (exp ℚ))
      = C (1 / 2 : ℚ) * X * (rescale (1 / 2 : ℚ) (exp ℚ) + rescale (-1 / 2 : ℚ) (exp ℚ)) := by
  have h1 := scaledBernoulliPowerSeries_mul_exp_sub_one
  have h2 := exp_sub_one_mul_rescale_neg_half
  have hc : C (1 / 2 : ℚ) * 2 = (1 : PowerSeries ℚ) := by
    rw [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  set S := scaledBernoulliPowerSeries
  set Ep := rescale (1 / 2 : ℚ) (exp ℚ)
  set Em := rescale (-1 / 2 : ℚ) (exp ℚ)
  linear_combination Em * h1 + (C (1 / 2 : ℚ) * X - S) * h2 - X * Em * hc

/-- (4.60): `∑_{j=0}^{k} C_j/((2k+1−2j)! 4^(k−j)) = 1/((2k)! 4^k)`, for all `k`. -/
theorem scaledBernoulli_rec_stable (k : ℕ) :
    ∑ j ∈ range (k + 1), scaledBernoulli j / (((2 * k + 1 - 2 * j).factorial : ℚ) * 4 ^ (k - j))
      = 1 / (((2 * k).factorial : ℚ) * 4 ^ k) := by
  have h := congrArg (coeff (2 * k + 1)) scaledBernoulliPowerSeries_mul_sinh
  rw [coeff_scaledBernoulliPowerSeries_mul, mul_assoc, coeff_C_mul, coeff_succ_X_mul, map_add,
    coeff_rescale_exp, coeff_rescale_exp, div_pow, div_pow, one_pow, Even.neg_one_pow ⟨k, by ring⟩,
    pow_mul] at h
  have h2 : ∀ j ∈ range (k + 1),
      scaledBernoulli j * coeff (2 * k + 1 - 2 * j)
          (rescale (1 / 2 : ℚ) (exp ℚ) - rescale (-1 / 2 : ℚ) (exp ℚ))
        = scaledBernoulli j / (((2 * k + 1 - 2 * j).factorial : ℚ) * 4 ^ (k - j)) := by
    intro j hj
    have hj' := mem_range.mp hj
    rw [map_sub, coeff_rescale_exp, coeff_rescale_exp,
      show 2 * k + 1 - 2 * j = 2 * (k - j) + 1 by omega, div_pow, div_pow, one_pow,
      Odd.neg_one_pow ⟨k - j, rfl⟩, pow_succ, pow_mul, show (4 : ℚ) = 2 ^ 2 by norm_num]
    ring
  rw [sum_congr rfl h2] at h
  rw [h, show (4 : ℚ) = 2 ^ 2 by norm_num]
  ring

/-! ### The size of `C_k` -/

/-- `C_k = (−1)^(k+1) · 2 ζ(2k) / (2π)^(2k)` for `k ≥ 1` (from `B_{2k}` in terms of `ζ(2k)`). -/
theorem scaledBernoulli_eq_zeta {k : ℕ} (hk : 1 ≤ k) :
    (scaledBernoulli k : ℝ)
      = (-1) ^ (k + 1) * 2 * zetaReal (2 * k) / (2 * Real.pi) ^ (2 * k) := by
  unfold scaledBernoulli
  push_cast
  rw [bernoulli_two_mul_eq_zeta hk]
  have hf : (0 : ℝ) < (2 * k).factorial := by positivity
  field_simp

/-- `|C_k| ≤ (π²/3)/(2π)^(2k)` for `k ≥ 1`: the scaled Bernoulli numbers decay like `(2π)^(−2k)`,
which is what makes the forward recurrences (4.58)/(4.59) ill-conditioned. -/
theorem abs_scaledBernoulli_le {k : ℕ} (hk : 1 ≤ k) :
    |(scaledBernoulli k : ℝ)| ≤ (Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * k) := by
  rw [scaledBernoulli_eq_zeta hk, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_two, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi) ^ (2 * k)),
    abs_of_nonneg (by linarith [one_le_zetaReal_two_mul hk] : (0 : ℝ) ≤ zetaReal (2 * k))]
  have hζ := zetaReal_two_mul_le hk
  have hp : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) := by positivity
  rw [div_le_div_iff_of_pos_right hp]
  linarith

end BZ

end Azurite
