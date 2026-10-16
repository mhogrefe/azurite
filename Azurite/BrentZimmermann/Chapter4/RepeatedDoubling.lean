/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.ArgumentReduction
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Brent–Zimmermann §4.3.1–4.3.2: Repeated doubling, and loss of precision

**§4.3.1.**  Applying the doubling formula `k` times, `exp x = exp(x/2^k)^(2^k)`: for `|x| = Θ(1)`
the argument becomes `O(2^(−k))`, where the power series converges faster, at the cost of `k`
squarings to reconstruct the result.  With the obvious series evaluation the optimal `k` is of
order `√n`, for a total `O(√n · M(n))` (improved in §4.4.3); the optimal `k` also depends on the
size of `x` (Exercise 4.5).

**§4.3.2.**  Alternating series lose precision by cancellation: the terms `x^k/k!` of `exp x` for
`x = −10` grow in magnitude until `k > |x|`, and summing 51 terms at ten digits leaves only about
three correct digits.  The cure is `exp x = 1 / exp(−x)`, so that the series summed has no sign
changes; for other functions a related series without sign changes may exist (`erf`, §4.4).

What is formalized: the faster convergence of the series at the reduced argument
(`abs_exp_sub_sum_div_two_pow_le`); the loss of `k` bits in the `k` squarings, as an exact
model of the reconstruction with a relative error in every squaring (`squareSeq`,
`squareSeq_eq`, `abs_squareSeq_sub_exp_le`: the final relative error is at most twice
`2^k |ε| + ∑ 2^(k−1−i) |θ_i|`, i.e. about `2^(k+1)` times the per-step error); the behaviour of
the terms of the exponential series (`expTerm_succ`, `expTerm_le_succ`, `expTerm_succ_le`); the
cancellation bound (`abs_sum_perturbed_le`, `sum_abs_expTerm_le`, `relative_loss_of_neg`: a
per-term relative perturbation `η` costs `η exp(2|x|)` relative error for `x < 0`, but only `η`
for `x ≥ 0`), with `exp_twenty_gt` quantifying the example (`exp 20 > 10^8`); and the identity
`exp_eq_inv_exp_neg`.  Not formalized: the `O(√n M(n))` cost statement (no cost model).
-/

namespace Azurite

namespace BZ

open Finset Real

/-! ### §4.3.1: faster convergence at the reduced argument -/

/-- At the reduced argument `x / 2^k` the series of `exp` with `N ≥ 1` terms has error at most
`(|x| / 2^k)^N (N + 1) / (N! N)`, as long as `|x| / 2^k ≤ 1`. -/
theorem abs_exp_sub_sum_div_two_pow_le {x : ℝ} {k N : ℕ} (hN : 0 < N) (hx : |x| / 2 ^ k ≤ 1) :
    |exp (x / 2 ^ k) - ∑ m ∈ range N, (x / 2 ^ k) ^ m / m.factorial|
      ≤ (|x| / 2 ^ k) ^ N * ((N + 1 : ℕ) / (N.factorial * N : ℝ)) := by
  have h : |x / 2 ^ k| = |x| / 2 ^ k := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]
  have := Real.exp_bound (x := x / 2 ^ k) (by rwa [h]) hN
  rwa [h] at this

/-! ### §4.3.1: the error of the `k` squarings -/

/-- `|(1 + a)^e − 1| ≤ (1 + |a|)^e − 1`. -/
theorem abs_one_add_pow_sub_one_le (a : ℝ) (e : ℕ) : |(1 + a) ^ e - 1| ≤ (1 + |a|) ^ e - 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hid : (1 + a) ^ (e + 1) - 1 = ((1 + a) ^ e - 1) * (1 + a) + a := by ring
    have h1 : |1 + a| ≤ 1 + |a| := (abs_add_le _ _).trans (by rw [abs_one])
    rw [hid]
    calc |((1 + a) ^ e - 1) * (1 + a) + a| ≤ |(1 + a) ^ e - 1| * |1 + a| + |a| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ ((1 + |a|) ^ e - 1) * (1 + |a|) + |a| := by
          gcongr
          exact sub_nonneg.mpr (one_le_pow₀ (by linarith [abs_nonneg a]))
      _ = (1 + |a|) ^ (e + 1) - 1 := by ring

/-- `|∏_{i<n} (1 + a_i)^(e_i) − 1| ≤ ∏_{i<n} (1 + |a_i|)^(e_i) − 1`. -/
theorem abs_prod_one_add_pow_sub_one_le (a : ℕ → ℝ) (e : ℕ → ℕ) (n : ℕ) :
    |∏ i ∈ range n, (1 + a i) ^ e i - 1| ≤ ∏ i ∈ range n, (1 + |a i|) ^ e i - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, prod_range_succ]
    set P := ∏ i ∈ range n, (1 + a i) ^ e i
    set Q := (1 + a n) ^ e n
    set P' := ∏ i ∈ range n, (1 + |a i|) ^ e i
    set Q' := (1 + |a n|) ^ e n
    have hQ : |Q| ≤ Q' := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans (by simp)) _
    have hQ1 : |Q - 1| ≤ Q' - 1 := abs_one_add_pow_sub_one_le _ _
    have hP'1 : 1 ≤ P' := one_le_prod₀ fun i _ => one_le_pow₀ (by linarith [abs_nonneg (a i)])
    have hid : P * Q - 1 = (P - 1) * Q + (Q - 1) := by ring
    rw [hid]
    calc |(P - 1) * Q + (Q - 1)| ≤ |P - 1| * |Q| + |Q - 1| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (P' - 1) * Q' + (Q' - 1) := by gcongr
      _ = P' * Q' - 1 := by ring

/-- `∏_{i<n} (1 + |a_i|)^(e_i) ≤ exp (∑_{i<n} e_i |a_i|)`. -/
theorem prod_one_add_abs_pow_le_exp (a : ℕ → ℝ) (e : ℕ → ℕ) (n : ℕ) :
    ∏ i ∈ range n, (1 + |a i|) ^ e i ≤ exp (∑ i ∈ range n, (e i : ℝ) * |a i|) := by
  rw [Real.exp_sum]
  gcongr with i _
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by positivity) (by linarith [add_one_le_exp |a i|]) _

/-- `exp S − 1 ≤ 2 S` for `0 ≤ S ≤ 1`. -/
theorem exp_sub_one_le_two_mul {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 1) : exp S - 1 ≤ 2 * S := by
  have h := Real.exp_bound' h0 h1 (n := 1) one_pos
  simp at h
  linarith

/-- The reconstruction by squarings, each squaring carrying a relative error `θ i`:
`s₀ = t`, `s_{i+1} = s_i² (1 + θ_i)`. -/
def squareSeq (t : ℝ) (θ : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | i + 1 => squareSeq t θ i ^ 2 * (1 + θ i)

/-- Closed form: `s_k = t^(2^k) ∏_{i<k} (1 + θ_i)^(2^(k−1−i))`. -/
theorem squareSeq_eq (t : ℝ) (θ : ℕ → ℝ) (k : ℕ) :
    squareSeq t θ k = t ^ (2 ^ k) * ∏ i ∈ range k, (1 + θ i) ^ (2 ^ (k - 1 - i)) := by
  induction k with
  | zero => simp [squareSeq]
  | succ k ih =>
    rw [squareSeq, ih, prod_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, pow_one]
    rw [mul_pow, ← pow_mul, ← prod_pow, ← pow_succ, mul_assoc]
    congr 2
    refine prod_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [← pow_mul, ← pow_succ]
    congr 2
    omega

/-- The error of the `k` squarings: from `t = exp(x/2^k)(1 + ε)` with relative errors `θ_i` in
the squarings, and `S = 2^k |ε| + ∑_{i<k} 2^(k−1−i) |θ_i| ≤ 1`, the result satisfies
`|s_k − exp x| ≤ 2 S · exp x`.  With `|ε|, |θ_i| ≤ η` this is `S ≤ (2^(k+1) − 1) η`: about `k + 1`
bits lost. -/
theorem abs_squareSeq_sub_exp_le (x : ℝ) (k : ℕ) (ε : ℝ) (θ : ℕ → ℝ)
    (hS : (2 ^ k : ℝ) * |ε| + ∑ i ∈ range k, (2 ^ (k - 1 - i) : ℝ) * |θ i| ≤ 1) :
    |squareSeq (exp (x / 2 ^ k) * (1 + ε)) θ k - exp x|
      ≤ 2 * ((2 ^ k : ℝ) * |ε| + ∑ i ∈ range k, (2 ^ (k - 1 - i) : ℝ) * |θ i|) * exp x := by
  set S := (2 ^ k : ℝ) * |ε| + ∑ i ∈ range k, (2 ^ (k - 1 - i) : ℝ) * |θ i| with hS_def
  have hS0 : 0 ≤ S := by positivity
  -- the result is `exp x` times a product of perturbation factors
  have hform : squareSeq (exp (x / 2 ^ k) * (1 + ε)) θ k
      = exp x * ((1 + ε) ^ (2 ^ k) * ∏ i ∈ range k, (1 + θ i) ^ (2 ^ (k - 1 - i))) := by
    rw [squareSeq_eq, mul_pow, ← exp_eq_pow_two_pow, mul_assoc]
  -- the perturbation product as a single `∏ (1 + a_i)^(e_i)` over `range (k + 1)`
  set a : ℕ → ℝ := fun i => if i < k then θ i else ε with ha
  set e : ℕ → ℕ := fun i => if i < k then 2 ^ (k - 1 - i) else 2 ^ k with he
  have hprod : (1 + ε) ^ (2 ^ k) * ∏ i ∈ range k, (1 + θ i) ^ (2 ^ (k - 1 - i))
      = ∏ i ∈ range (k + 1), (1 + a i) ^ e i := by
    rw [prod_range_succ]
    have h1 : ∀ i ∈ range k, (1 + a i) ^ e i = (1 + θ i) ^ (2 ^ (k - 1 - i)) := by
      intro i hi; rw [mem_range] at hi; simp [ha, he, hi]
    have h2 : (1 + a k) ^ e k = (1 + ε) ^ (2 ^ k) := by simp [ha, he]
    rw [prod_congr rfl h1, h2, mul_comm]
  have hsum : ∑ i ∈ range (k + 1), (e i : ℝ) * |a i| = S := by
    rw [sum_range_succ, hS_def]
    have h1 : ∀ i ∈ range k, (e i : ℝ) * |a i| = (2 ^ (k - 1 - i) : ℝ) * |θ i| := by
      intro i hi; rw [mem_range] at hi; simp [ha, he, hi]
    have h2 : (e k : ℝ) * |a k| = (2 ^ k : ℝ) * |ε| := by simp [ha, he]
    rw [sum_congr rfl h1, h2, add_comm]
  rw [hform, hprod, ← mul_sub_one, abs_mul, abs_of_pos (exp_pos x), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (exp_pos x).le
  calc |∏ i ∈ range (k + 1), (1 + a i) ^ e i - 1|
      ≤ ∏ i ∈ range (k + 1), (1 + |a i|) ^ e i - 1 := abs_prod_one_add_pow_sub_one_le a e (k + 1)
    _ ≤ exp (∑ i ∈ range (k + 1), (e i : ℝ) * |a i|) - 1 := by
        linarith [prod_one_add_abs_pow_le_exp a e (k + 1)]
    _ = exp S - 1 := by rw [hsum]
    _ ≤ 2 * S := exp_sub_one_le_two_mul hS0 hS

/-! ### §4.3.2: loss of precision in alternating series -/

/-- The `m`-th term of the exponential series. -/
noncomputable def expTerm (x : ℝ) (m : ℕ) : ℝ := x ^ m / m.factorial

theorem expTerm_succ (x : ℝ) (m : ℕ) : expTerm x (m + 1) = expTerm x m * (x / (m + 1)) := by
  unfold expTerm
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The terms grow in magnitude while `m + 1 ≤ |x|`. -/
theorem expTerm_le_succ {x : ℝ} {m : ℕ} (h : (m : ℝ) + 1 ≤ |x|) :
    |expTerm x m| ≤ |expTerm x (m + 1)| := by
  rw [expTerm_succ, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 1)]
  have : 1 ≤ |x| / (m + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
  calc |expTerm x m| = |expTerm x m| * 1 := (mul_one _).symm
    _ ≤ |expTerm x m| * (|x| / (m + 1)) := mul_le_mul_of_nonneg_left this (abs_nonneg _)

/-- The terms decrease in magnitude once `|x| ≤ m + 1`. -/
theorem expTerm_succ_le {x : ℝ} {m : ℕ} (h : |x| ≤ (m : ℝ) + 1) :
    |expTerm x (m + 1)| ≤ |expTerm x m| := by
  rw [expTerm_succ, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 1)]
  have : |x| / (m + 1) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
  calc |expTerm x m| * (|x| / (m + 1)) ≤ |expTerm x m| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |expTerm x m| := mul_one _

/-- The terms alternate in sign for `x < 0`: `expTerm x m` has the sign of `(−1)^m`. -/
theorem expTerm_neg_eq (x : ℝ) (m : ℕ) : expTerm (-x) m = (-1) ^ m * expTerm x m := by
  unfold expTerm
  rw [neg_pow, mul_div_assoc]

/-- A sum whose terms each carry a relative perturbation `η` moves by at most `η ∑ |t_m|`. -/
theorem abs_sum_perturbed_le {ι : Type*} (s : Finset ι) (t δ : ι → ℝ) {η : ℝ}
    (hδ : ∀ i ∈ s, |δ i| ≤ η * |t i|) :
    |∑ i ∈ s, (t i + δ i) - ∑ i ∈ s, t i| ≤ η * ∑ i ∈ s, |t i| := by
  rw [sum_add_distrib, add_sub_cancel_left, mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hδ)

/-- The sum of the magnitudes of the terms is at most `exp |x|`. -/
theorem sum_abs_expTerm_le (x : ℝ) (N : ℕ) : ∑ m ∈ range N, |expTerm x m| ≤ exp |x| := by
  have : ∀ m, |expTerm x m| = |x| ^ m / m.factorial := fun m => by
    unfold expTerm
    rw [abs_div, abs_pow, abs_of_pos (by exact_mod_cast m.factorial_pos : (0 : ℝ) < m.factorial)]
  simp only [this]
  exact Real.sum_le_exp_of_nonneg (abs_nonneg x) N

/-- For `x ≥ 0` the series has no sign changes and the perturbed sum stays within relative
error `η` of the exact partial sum. -/
theorem abs_sum_perturbed_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (δ : ℕ → ℝ) {η : ℝ}
    (hδ : ∀ m ∈ range N, |δ m| ≤ η * |expTerm x m|) :
    |∑ m ∈ range N, (expTerm x m + δ m) - ∑ m ∈ range N, expTerm x m|
      ≤ η * ∑ m ∈ range N, expTerm x m := by
  refine (abs_sum_perturbed_le _ _ _ hδ).trans (le_of_eq ?_)
  congr 1
  exact sum_congr rfl fun m _ => abs_of_nonneg (by unfold expTerm; positivity)

/-- For `x < 0` the cancellation costs a factor `exp (2|x|)`: the perturbation bound
`η exp |x|` is `η exp(2|x|)` times the value `exp x`. -/
theorem relative_loss_of_neg {x : ℝ} (hx : x ≤ 0) : exp |x| = exp (2 * |x|) * exp x := by
  rw [← exp_add, abs_of_nonpos hx]
  congr 1
  ring

/-- The example `x = −10`: the amplification factor exceeds `10^8`, so ten working digits
leave at most two or three. -/
theorem exp_twenty_gt : (10 : ℝ) ^ 8 < exp 20 := by
  have h := Real.exp_one_gt_d9
  have h2 : (2.7 : ℝ) ^ 20 ≤ exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) (by linarith) 20
  rw [← Real.exp_nat_mul] at h2
  push_cast at h2
  rw [mul_one] at h2
  calc (10 : ℝ) ^ 8 < 2.7 ^ 20 := by norm_num
    _ ≤ exp 20 := h2

/-- The cure: `exp x = 1 / exp (−x)`, so the series summed is the one without sign changes. -/
theorem exp_eq_inv_exp_neg (x : ℝ) : exp x = (exp (-x))⁻¹ := by
  rw [exp_neg, inv_inv]

end BZ

end Azurite
