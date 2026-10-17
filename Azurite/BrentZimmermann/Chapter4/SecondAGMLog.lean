/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.ThetaModular

/-!
# Brent–Zimmermann §4.8.4: Second AGM algorithm for the logarithm

For large `x` put `q = 1/x`, evaluate `θ₂(q⁴)` and `θ₃(q⁴)` from their series, and use
Sasaki–Kanada (4.79) with `q` replaced by `q⁴` (which removes the `q^(1/4)` from `θ₂`):

  `ln x = (π/4)/AGM(θ₂²(q⁴), θ₃²(q⁴))`.

Once `q` is small enough that `O(q³⁶)` is negligible,

  `θ₂(q⁴) = 2q + 2q⁹ + 2q²⁵ + O(q⁴⁹)`,   `θ₃(q⁴) = 1 + 2q⁴ + 2q¹⁶ + O(q³⁶)`,

so `x ≥ 2^(n/36)` suffices (against `x ≥ 2^(n/2)` for the first algorithm), saving about four AGM
iterations.  Implementation note: `AGM(θ₂², θ₃²) = AGM(θ₂² + θ₃², 2θ₂θ₃)/2` avoids the first
square root, and `θ₂² + θ₃²`, `2θ₂θ₃` cost two non-scalar products (Exercise 4.45).  The AGM's
drawbacks (no self-correction, hence full precision throughout; `exp` only through Newton on `ln`;
trigonometric functions need complex arguments or Landen transformations) are discussion.

What is formalized (all proven):

* `nome_log`: every `q ∈ (0, 1)` is a nome, so (4.79) holds for all `0 < q < 1`
  (`sasaki_kanada'`), and `log_eq_pi_div_four_div_AGM`: `ln x = (π/4)/AGM(θ₂²(q⁴), θ₃²(q⁴))`
  for `x > 1`, `q = 1/x`.
* `theta2_pow_four`: `θ₂(q⁴) = q · θ₂Int(q⁴)` (no fractional power), and
  `theta2Int_eq_two_mul_tsum`: `θ₂Int(q) = 2 ∑_{n≥0} q^(n(n+1))`.
* Truncations with explicit tails: `theta3_trunc` (`0 ≤ θ₃(q) − (1 + 2∑_{n<N} q^((n+1)²)) ≤
  2q^((N+1)²)/(1 − q)`), `theta2Int_trunc`; the §4.8.4 forms `theta3_pow_four_trunc`
  (`θ₃(q⁴) = 1 + 2q⁴ + 2q¹⁶ + R₃`, `0 ≤ R₃ ≤ 2q³⁶/(1 − q⁴)`) and `theta2_pow_four_trunc`
  (`θ₂(q⁴) = 2q + 2q⁹ + 2q²⁵ + R₂`, `0 ≤ R₂ ≤ 2q⁴⁹/(1 − q⁴)`).
* The precision condition: `x ≥ 2^(n/36)` gives `q³⁶ ≤ 2^(−n)` (`inv_pow_le_of_two_rpow_le`), so
  both tails are `≤ 2 · 2^(−n)/(1 − q⁴)` (`theta3_pow_four_error_le`, `theta2_pow_four_error_le`).
* `AGM_sq_sq`: `AGM(a², b²) = AGM(a² + b², 2ab)/2`, and the two-product start
  `sq_add_sq_eq_half_add`, `two_mul_mul_eq_half_sub` (Exercise 4.45's identities).
-/

namespace Azurite

namespace BZ

open Filter Topology Finset

variable {q x : ℝ}

/-! ### Every `q ∈ (0, 1)` is a nome -/

theorem nome_log (hq0 : 0 < q) : nome (-Real.log q / Real.pi) = q := by
  unfold nome
  rw [show -(Real.pi * (-Real.log q / Real.pi)) = Real.log q by field_simp, Real.exp_log hq0]

/-- Sasaki–Kanada (4.79) for every `0 < q < 1`. -/
theorem sasaki_kanada' (hq0 : 0 < q) (hq1 : q < 1) :
    Real.log (1 / q) = Real.pi / AGM (theta2 q ^ 2) (theta3 q ^ 2) := by
  have hs : 0 < -Real.log q / Real.pi :=
    div_pos (neg_pos.mpr (Real.log_neg hq0 hq1)) Real.pi_pos
  have h := sasaki_kanada hs
  rwa [nome_log hq0] at h

/-- The second AGM algorithm: `ln x = (π/4)/AGM(θ₂²(q⁴), θ₃²(q⁴))` with `q = 1/x`, `x > 1`. -/
theorem log_eq_pi_div_four_div_AGM (hx : 1 < x) :
    Real.log x = (Real.pi / 4) / AGM (theta2 ((1 / x) ^ 4) ^ 2) (theta3 ((1 / x) ^ 4) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < (1 / x) ^ 4 := by positivity
  have hq1 : (1 / x) ^ 4 < 1 := pow_lt_one₀ (by positivity) ((div_lt_one hx0).mpr hx) (by norm_num)
  have h := sasaki_kanada' hq0 hq1
  have e : Real.log (1 / (1 / x) ^ 4) = 4 * Real.log x := by
    rw [one_div, one_div, inv_pow, inv_inv, Real.log_pow]
    push_cast
    ring
  rw [e] at h
  rw [div_div, mul_comm (4 : ℝ), ← div_div, ← h]
  ring

/-! ### `θ₂(q⁴)` without the fractional power -/

theorem theta2_pow_four (hq0 : 0 ≤ q) (hq1 : q < 1) : theta2 (q ^ 4) = q * theta2Int (q ^ 4) := by
  rw [theta2_eq_rpow_mul (by positivity) (pow_lt_one₀ hq0 hq1 (by norm_num)),
    show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hq0 (by norm_num)]

/-- `θ₂Int(q) = 2 ∑_{n≥0} q^(n(n+1))` for `0 < q < 1`. -/
theorem theta2Int_eq_two_mul_tsum (hq0 : 0 < q) (hq1 : q < 1) :
    theta2Int q = 2 * ∑' n : ℕ, q ^ (n * (n + 1)) := by
  have h1 := theta2_eq_rpow_mul hq0.le hq1
  have hr : 0 < q ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hq0 _
  unfold theta2 at h1
  have : q ^ (1 / 4 : ℝ) * theta2Int q = q ^ (1 / 4 : ℝ) * (2 * ∑' n : ℕ, q ^ (n * (n + 1))) := by
    rw [← h1]; ring
  exact mul_left_cancel₀ hr.ne' this

/-! ### Tails of sparse series -/

/-- If the exponents satisfy `e n ≥ M + n`, the series `∑ q^(e n)` is at most `q^M/(1 − q)`. -/
theorem summable_pow_of_le (hq0 : 0 ≤ q) (hq1 : q < 1) {e : ℕ → ℕ} {M : ℕ}
    (he : ∀ n, M + n ≤ e n) : Summable fun n : ℕ => q ^ e n :=
  ((summable_geometric_of_lt_one hq0 hq1).mul_left (q ^ M)).of_nonneg_of_le
    (fun n => pow_nonneg hq0 _) fun n => by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hq0 hq1.le (he n)

theorem tsum_pow_le_of_le (hq0 : 0 ≤ q) (hq1 : q < 1) {e : ℕ → ℕ} {M : ℕ}
    (he : ∀ n, M + n ≤ e n) : ∑' n : ℕ, q ^ e n ≤ q ^ M / (1 - q) := by
  have hg := (summable_geometric_of_lt_one hq0 hq1).mul_left (q ^ M)
  calc ∑' n : ℕ, q ^ e n ≤ ∑' n : ℕ, q ^ M * q ^ n :=
        (summable_pow_of_le hq0 hq1 he).tsum_le_tsum (fun n => by
          rw [← pow_add]; exact pow_le_pow_of_le_one hq0 hq1.le (he n)) hg
    _ = q ^ M / (1 - q) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

/-- `θ₃(q) = 1 + 2∑_{n<N} q^((n+1)²) + R` with `0 ≤ R ≤ 2q^((N+1)²)/(1 − q)`. -/
theorem theta3_trunc (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    0 ≤ theta3 q - (1 + 2 * ∑ n ∈ range N, q ^ ((n + 1) ^ 2))
      ∧ theta3 q - (1 + 2 * ∑ n ∈ range N, q ^ ((n + 1) ^ 2))
        ≤ 2 * q ^ ((N + 1) ^ 2) / (1 - q) := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have hs := summable_pow_succ_sq hq
  rw [theta3_eq_one_add hq, ← Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => q ^ ((n + 1) ^ 2))
    (k := N) ((summable_nat_add_iff (f := fun n : ℕ => q ^ ((n + 1) ^ 2)) N).mpr hs)]
  have he : ∀ n : ℕ, (N + 1) ^ 2 + n ≤ (n + N + 1) ^ 2 := fun n => by
    have h : (n + N + 1) ^ 2 = (N + 1) ^ 2 + n * (n + 2 * N + 2) := by ring
    rw [h]
    exact Nat.add_le_add_left (Nat.le_mul_of_pos_right n (by omega)) _
  have htail := tsum_pow_le_of_le hq0 hq1 (e := fun n => (n + N + 1) ^ 2) he
  have hnn : 0 ≤ ∑' n : ℕ, q ^ ((n + N + 1) ^ 2) := tsum_nonneg fun n => pow_nonneg hq0 _
  constructor
  · linarith
  · rw [mul_div_assoc]
    linarith

/-- `θ₂Int(q) = 2∑_{n<N} q^(n(n+1)) + R` with `0 ≤ R ≤ 2q^(N(N+1))/(1 − q)`, `0 < q < 1`. -/
theorem theta2Int_trunc (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    0 ≤ theta2Int q - 2 * ∑ n ∈ range N, q ^ (n * (n + 1))
      ∧ theta2Int q - 2 * ∑ n ∈ range N, q ^ (n * (n + 1)) ≤ 2 * q ^ (N * (N + 1)) / (1 - q) := by
  have hs : Summable fun n : ℕ => q ^ (n * (n + 1)) :=
    summable_pow_of_le hq0.le hq1 (e := fun n => n * (n + 1)) (M := 0) fun n => by nlinarith
  rw [theta2Int_eq_two_mul_tsum hq0 hq1, ← Summable.sum_add_tsum_nat_add'
    (f := fun n : ℕ => q ^ (n * (n + 1))) (k := N)
    ((summable_nat_add_iff (f := fun n : ℕ => q ^ (n * (n + 1))) N).mpr hs)]
  have he : ∀ n : ℕ, N * (N + 1) + n ≤ (n + N) * (n + N + 1) := fun n => by nlinarith
  have htail := tsum_pow_le_of_le hq0.le hq1 (e := fun n => (n + N) * (n + N + 1)) he
  have hnn : 0 ≤ ∑' n : ℕ, q ^ ((n + N) * (n + N + 1)) := tsum_nonneg fun n => pow_nonneg hq0.le _
  constructor
  · linarith
  · rw [mul_div_assoc]
    linarith

/-- `θ₃(q⁴) = 1 + 2q⁴ + 2q¹⁶ + R₃` with `0 ≤ R₃ ≤ 2q³⁶/(1 − q⁴)`. -/
theorem theta3_pow_four_trunc (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ theta3 (q ^ 4) - (1 + 2 * q ^ 4 + 2 * q ^ 16)
      ∧ theta3 (q ^ 4) - (1 + 2 * q ^ 4 + 2 * q ^ 16) ≤ 2 * q ^ 36 / (1 - q ^ 4) := by
  have h := theta3_trunc (q := q ^ 4) (by positivity) (pow_lt_one₀ hq0 hq1 (by norm_num)) 2
  simp only [sum_range_succ, sum_range_zero, zero_add] at h
  norm_num [← pow_mul] at h
  constructor
  · linarith [h.1]
  · linarith [h.2]

/-- `θ₂(q⁴) = 2q + 2q⁹ + 2q²⁵ + R₂` with `0 ≤ R₂ ≤ 2q⁴⁹/(1 − q⁴)`. -/
theorem theta2_pow_four_trunc (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ theta2 (q ^ 4) - (2 * q + 2 * q ^ 9 + 2 * q ^ 25)
      ∧ theta2 (q ^ 4) - (2 * q + 2 * q ^ 9 + 2 * q ^ 25) ≤ 2 * q ^ 49 / (1 - q ^ 4) := by
  have h := theta2Int_trunc (q := q ^ 4) (by positivity) (pow_lt_one₀ hq0.le hq1 (by norm_num)) 3
  simp only [sum_range_succ, sum_range_zero, zero_add] at h
  norm_num [← pow_mul] at h
  obtain ⟨h1, h2⟩ := h
  rw [theta2_pow_four hq0.le hq1]
  have hq4 : 0 < 1 - q ^ 4 := by linarith [pow_lt_one₀ hq0.le hq1 (by norm_num : (4 : ℕ) ≠ 0)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 hq0.le]
  · have h3 : q * (theta2Int (q ^ 4) - 2 * (1 + q ^ 8 + q ^ 24)) ≤ q * (2 * q ^ 48 / (1 - q ^ 4)) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0.le
    have e : q * (2 * q ^ 48 / (1 - q ^ 4)) = 2 * q ^ 49 / (1 - q ^ 4) := by
      field_simp
    linarith

/-! ### The precision condition `x ≥ 2^(n/36)` -/

/-- `x ≥ 2^(n/36)` gives `(1/x)^36 ≤ 2^(−n)`. -/
theorem inv_pow_le_of_two_rpow_le {n : ℕ} (hx : (2 : ℝ) ^ ((n : ℝ) / 36) ≤ x) :
    (1 / x) ^ 36 ≤ (2 : ℝ) ^ (-(n : ℝ)) := by
  have h2 : (0 : ℝ) < 2 ^ ((n : ℝ) / 36) := Real.rpow_pos_of_pos two_pos _
  have hx0 : 0 < x := lt_of_lt_of_le h2 hx
  have h36 : ((2 : ℝ) ^ ((n : ℝ) / 36)) ^ 36 = 2 ^ (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    norm_num
  have hpow : (2 : ℝ) ^ (n : ℝ) ≤ x ^ 36 := h36 ▸ pow_le_pow_left₀ h2.le hx 36
  rw [one_div, inv_pow, Real.rpow_neg zero_le_two]
  exact inv_anti₀ (by positivity) hpow

theorem theta3_pow_four_error_le {n : ℕ} (hx1 : 1 < x) (hx : (2 : ℝ) ^ ((n : ℝ) / 36) ≤ x) :
    theta3 ((1 / x) ^ 4) - (1 + 2 * (1 / x) ^ 4 + 2 * (1 / x) ^ 16)
      ≤ 2 * (2 : ℝ) ^ (-(n : ℝ)) / (1 - (1 / x) ^ 4) := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 ≤ 1 / x := by positivity
  have hq1 : 1 / x < 1 := (div_lt_one hx0).mpr hx1
  have hq4 : 0 < 1 - (1 / x) ^ 4 := by linarith [pow_lt_one₀ hq0 hq1 (by norm_num : (4 : ℕ) ≠ 0)]
  refine (theta3_pow_four_trunc hq0 hq1).2.trans ?_
  gcongr
  exact inv_pow_le_of_two_rpow_le hx

theorem theta2_pow_four_error_le {n : ℕ} (hx1 : 1 < x) (hx : (2 : ℝ) ^ ((n : ℝ) / 36) ≤ x) :
    theta2 ((1 / x) ^ 4) - (2 * (1 / x) + 2 * (1 / x) ^ 9 + 2 * (1 / x) ^ 25)
      ≤ 2 * (2 : ℝ) ^ (-(n : ℝ)) / (1 - (1 / x) ^ 4) := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < 1 / x := by positivity
  have hq1 : 1 / x < 1 := (div_lt_one hx0).mpr hx1
  have hq4 : 0 < 1 - (1 / x) ^ 4 := by linarith [pow_lt_one₀ hq0.le hq1 (by norm_num : (4 : ℕ) ≠ 0)]
  refine (theta2_pow_four_trunc hq0 hq1).2.trans ?_
  gcongr
  calc (1 / x) ^ 49 ≤ (1 / x) ^ 36 := pow_le_pow_of_le_one hq0.le hq1.le (by norm_num)
    _ ≤ _ := inv_pow_le_of_two_rpow_le hx

/-! ### Starting the AGM from `θ₂`, `θ₃` without the first square root -/

/-- `AGM(a², b²) = AGM(a² + b², 2ab)/2` for `a, b > 0`. -/
theorem AGM_sq_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    AGM (a ^ 2) (b ^ 2) = AGM (a ^ 2 + b ^ 2) (2 * a * b) / 2 := by
  rw [AGM_step (by positivity) (by positivity),
    show Real.sqrt (a ^ 2 * b ^ 2) = a * b by
      rw [← mul_pow, Real.sqrt_sq (by positivity)],
    show (a ^ 2 + b ^ 2) / 2 = (1 / 2) * (a ^ 2 + b ^ 2) by ring,
    show a * b = (1 / 2) * (2 * a * b) by ring,
    AGM_smul (by norm_num) (by positivity) (by positivity)]
  ring

/-- Exercise 4.45's identities: `a² + b²` and `2ab` from the two squares `(a ± b)²`. -/
theorem sq_add_sq_eq_half_add (a b : ℝ) : a ^ 2 + b ^ 2 = ((a + b) ^ 2 + (a - b) ^ 2) / 2 := by ring

theorem two_mul_mul_eq_half_sub (a b : ℝ) : 2 * a * b = ((a + b) ^ 2 - (a - b) ^ 2) / 2 := by ring

end BZ

end Azurite
