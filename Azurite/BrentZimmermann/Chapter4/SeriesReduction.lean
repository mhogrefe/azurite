/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.CoefficientRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Brent–Zimmermann §4.4.1–4.4.2: Direct evaluation, and power series with argument reduction

**§4.4.1.**  With `|x| ≤ 1/2` and radius of convergence at least `1`, `n + O(1)` terms give error
`O(2^(−n))`, so direct summation costs `O(n M(n))` (`O(n M(n)/log n)` for entire functions).

**§4.4.2.**  Reducing the argument `k + O(1)` times to `|x| < 2^(−k)` leaves `O(n/k)` terms; with
`O(M(n))` per reduction step the total is `O((k + n/k) M(n))`, minimized at `k ~ √n`:
`O(√n M(n))`.  The reductions are `exp x = exp(x/2)²`,
`log1p x = 2 log1p (x / (1 + √(1 + x)))` and `arctan x = 2 arctan (x / (1 + √(1 + x²)))`, the
last two through a square root (`O(M(n))` by Newton, §3.5).  *Symmetries*: `ln(1 + x)` through
`ln((1+y)/(1−y)) = 2 ∑ y^(2j+1)/(2j+1)` with `y = x/(2 + x)` halves the terms and shrinks the
argument (`y < x/2` for `x > 0`), but only once.

* `abs_tail_le_of_abs_le` — the tail bound `|∑_{j≥d} a_j x^j| ≤ A |x|^d / (1 − |x|)` for
  `|a_j| ≤ A`, `|x| < 1`; `terms_suffice_direct` (`|x| ≤ 1/2`: `d ≥ n + 1 + lg A` terms give
  `2^(−n)`, the `n + O(1)`) and `terms_suffice_reduced` (`|x| ≤ 2^(−k)`: `k d ≥ n + 1 + lg A`
  terms, the `O(n/k)`); `exp_terms_suffice_reduced` for the exponential (`k d ≥ n + 2`).
* `two_sqrt_le_add_div` — `2√n ≤ k + n/k`, the arithmetic behind `k ~ √n`.
* `exp_eq_sq_exp_half`, `log_one_add_eq_two_mul_log_one_add`, `arctan_eq_two_mul_arctan`,
  with the shrinking of the argument `div_one_add_sqrt_lt_half`,
  `abs_div_one_add_sqrt_sq_le_half`; `expHalf` and `arctanHalf` as `ArgumentReduction`
  instances (the `log1p` identity needs `x > −1`, so it stays a theorem).
* `symmetricLogVar`, `one_add_div_one_sub_eq`, `hasSum_log_one_add_symmetric`,
  `symmetricLogVar_lt_half`, `abs_symmetricLogVar_lt_one` — the symmetric series.
-/

namespace Azurite

namespace BZ

open Finset Filter Topology Real

/-! ### §4.4.1: how many terms -/

/-- The tail of a power series with bounded coefficients: for `|a_j| ≤ A` and `|x| < 1`,
`|∑_{j≥d} a_j x^j| ≤ A |x|^d / (1 − |x|)`. -/
theorem abs_tail_le_of_abs_le {a : ℕ → ℝ} {A : ℝ} (ha : ∀ j, |a j| ≤ A) {x : ℝ} (hx : |x| < 1)
    (d : ℕ) :
    |∑' j : ℕ, a (j + d) * x ^ (j + d)| ≤ A * |x| ^ d / (1 - |x|) := by
  have hA : 0 ≤ A := le_trans (abs_nonneg _) (ha 0)
  have hgeom : Summable (fun j : ℕ => A * |x| ^ d * |x| ^ j) :=
    (summable_geometric_of_lt_one (abs_nonneg _) hx).mul_left _
  have hb : ∀ j, |a (j + d) * x ^ (j + d)| ≤ A * |x| ^ d * |x| ^ j := by
    intro j
    rw [abs_mul, abs_pow, pow_add, mul_comm (|x| ^ j), ← mul_assoc]
    gcongr
    exact ha _
  have hs : Summable (fun j : ℕ => |a (j + d) * x ^ (j + d)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hb hgeom
  calc |∑' j : ℕ, a (j + d) * x ^ (j + d)| ≤ ∑' j : ℕ, |a (j + d) * x ^ (j + d)| := by
        have := norm_tsum_le_tsum_norm (f := fun j => a (j + d) * x ^ (j + d)) (by
          simpa only [Real.norm_eq_abs] using hs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' j : ℕ, A * |x| ^ d * |x| ^ j := hs.tsum_le_tsum hb hgeom
    _ = A * |x| ^ d / (1 - |x|) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (abs_nonneg _) hx, div_eq_mul_inv]

/-- Direct evaluation at `|x| ≤ 1/2`: `d` terms with `2^d ≥ 2^(n+1) A` leave a tail `≤ 2^(−n)` —
`n + O(1)` terms. -/
theorem terms_suffice_direct {a : ℕ → ℝ} {A : ℝ} (ha : ∀ j, |a j| ≤ A) {x : ℝ} (hx : |x| ≤ 1 / 2)
    {d n : ℕ} (hd : (2 : ℝ) ^ (n + 1) * A ≤ 2 ^ d) :
    |∑' j : ℕ, a (j + d) * x ^ (j + d)| ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  have hA : 0 ≤ A := le_trans (abs_nonneg _) (ha 0)
  have hx1 : |x| < 1 := by linarith
  refine (abs_tail_le_of_abs_le ha hx1 d).trans ?_
  have h1 : 1 / 2 ≤ 1 - |x| := by linarith
  rcases hA.eq_or_lt with h | hApos
  · subst h; simp
  calc A * |x| ^ d / (1 - |x|) ≤ A * (1 / 2) ^ d / (1 / 2) := by gcongr
    _ = 2 * A / 2 ^ d := by rw [one_div_pow]; field_simp
    _ ≤ 2 * A / ((2 : ℝ) ^ (n + 1) * A) := by gcongr
    _ = (2 : ℝ) ^ (-(n : ℤ)) := by rw [zpow_neg, zpow_natCast, pow_succ]; field_simp

/-- After reduction to `|x| ≤ 2^(−k)`: `d` terms with `2^(k d) ≥ 2^(n+1) A` suffice — `O(n/k)`
terms. -/
theorem terms_suffice_reduced {a : ℕ → ℝ} {A : ℝ} (ha : ∀ j, |a j| ≤ A) {k : ℕ} (hk : 1 ≤ k)
    {x : ℝ} (hx : |x| ≤ (2 : ℝ) ^ (-(k : ℤ))) {d n : ℕ}
    (hd : (2 : ℝ) ^ (n + 1) * A ≤ 2 ^ (k * d)) :
    |∑' j : ℕ, a (j + d) * x ^ (j + d)| ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  have hA : 0 ≤ A := le_trans (abs_nonneg _) (ha 0)
  have hk2 : (2 : ℝ) ^ (-(k : ℤ)) ≤ 1 / 2 := by
    calc (2 : ℝ) ^ (-(k : ℤ)) ≤ (2 : ℝ) ^ (-(1 : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  have hx1 : |x| < 1 := by linarith
  refine (abs_tail_le_of_abs_le ha hx1 d).trans ?_
  have h1 : 1 / 2 ≤ 1 - |x| := by linarith
  have hxd : |x| ^ d ≤ ((2 : ℝ) ^ (k * d))⁻¹ := by
    calc |x| ^ d ≤ ((2 : ℝ) ^ (-(k : ℤ))) ^ d := pow_le_pow_left₀ (abs_nonneg _) hx d
      _ = ((2 : ℝ) ^ (k * d))⁻¹ := by
          rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  rcases hA.eq_or_lt with h | hApos
  · subst h; simp
  calc A * |x| ^ d / (1 - |x|) ≤ A * ((2 : ℝ) ^ (k * d))⁻¹ / (1 / 2) := by gcongr
    _ = 2 * A / 2 ^ (k * d) := by field_simp
    _ ≤ 2 * A / ((2 : ℝ) ^ (n + 1) * A) := by gcongr
    _ = (2 : ℝ) ^ (-(n : ℤ)) := by rw [zpow_neg, zpow_natCast, pow_succ]; field_simp

/-- For the exponential after reduction to `|x| ≤ 2^(−k)`, `k d ≥ n + 2` terms give `2^(−n)`. -/
theorem exp_terms_suffice_reduced {k : ℕ} {x : ℝ} (hx : |x| ≤ (2 : ℝ) ^ (-(k : ℤ))) {d n : ℕ}
    (hd : n + 2 ≤ k * d) :
    |exp x - ∑ j ∈ range d, x ^ j / j.factorial| ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  refine (abs_exp_sub_sum_le x d).trans ?_
  have hx1 : |x| ≤ 1 := by
    calc |x| ≤ (2 : ℝ) ^ (-(k : ℤ)) := hx
      _ ≤ (2 : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 := zpow_zero 2
  have hd1 : (1 : ℝ) ≤ d.factorial := by exact_mod_cast d.factorial_pos
  have he : exp |x| ≤ 4 := by
    calc exp |x| ≤ exp 1 := exp_le_exp.mpr hx1
      _ ≤ 4 := by linarith [Real.exp_one_lt_d9]
  have hxd : |x| ^ d ≤ (2 : ℝ) ^ (-((k * d : ℕ) : ℤ)) := by
    calc |x| ^ d ≤ ((2 : ℝ) ^ (-(k : ℤ))) ^ d := pow_le_pow_left₀ (abs_nonneg _) hx d
      _ = (2 : ℝ) ^ (-((k * d : ℕ) : ℤ)) := by
          rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  calc |x| ^ d / d.factorial * exp |x| ≤ (2 : ℝ) ^ (-((k * d : ℕ) : ℤ)) / 1 * 4 := by gcongr
    _ = (2 : ℝ) ^ (-((k * d : ℕ) : ℤ) + 2) := by
        rw [zpow_add₀ (by norm_num)]; norm_num
    _ ≤ (2 : ℝ) ^ (-(n : ℤ)) := zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)

/-- `2√n ≤ k + n/k` for `k > 0`: the cost `(k + n/k) M(n)` is least near `k = √n`. -/
theorem two_sqrt_le_add_div {n k : ℝ} (hn : 0 ≤ n) (hk : 0 < k) : 2 * Real.sqrt n ≤ k + n / k := by
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn
  have h := sq_nonneg (k - Real.sqrt n)
  rw [sub_sq, hs] at h
  have key : k + n / k - 2 * Real.sqrt n = (k ^ 2 - 2 * k * Real.sqrt n + n) / k := by
    field_simp; ring
  have : 0 ≤ (k ^ 2 - 2 * k * Real.sqrt n + n) / k := div_nonneg h hk.le
  linarith

/-! ### §4.4.2: the three reductions -/

/-- `exp x = exp (x/2)²`. -/
theorem exp_eq_sq_exp_half (x : ℝ) : exp x = exp (x / 2) ^ 2 := by
  rw [← exp_two_mul', mul_div_cancel₀ _ two_ne_zero]

/-- `ln(1 + x) = 2 ln(1 + x / (1 + √(1 + x)))` for `x > −1`. -/
theorem log_one_add_eq_two_mul_log_one_add {x : ℝ} (hx : -1 < x) :
    log (1 + x) = 2 * log (1 + x / (1 + Real.sqrt (1 + x))) := by
  have h1x : 0 < 1 + x := by linarith
  set s := Real.sqrt (1 + x) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr h1x
  have hs2 : s ^ 2 = 1 + x := Real.sq_sqrt h1x.le
  have hval : 1 + x / (1 + s) = s := by
    have hx' : x = s ^ 2 - 1 := by linarith
    rw [hx']
    field_simp
    ring
  rw [hval, hs, Real.log_sqrt h1x.le]
  ring

/-- The reduced argument of `log1p` is less than half the argument: `x / (1 + √(1 + x)) < x/2`
for `x > 0`. -/
theorem div_one_add_sqrt_lt_half {x : ℝ} (hx : 0 < x) : x / (1 + Real.sqrt (1 + x)) < x / 2 := by
  have h1 : 1 < Real.sqrt (1 + x) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  exact div_lt_div_of_pos_left hx (by norm_num) (by linarith)

/-- `arctan x = 2 arctan (x / (1 + √(1 + x²)))`. -/
theorem arctan_eq_two_mul_arctan (x : ℝ) :
    arctan x = 2 * arctan (x / (1 + Real.sqrt (1 + x ^ 2))) := by
  set θ := arctan x with hθ
  have hθ1 : -(π / 2) < θ := neg_pi_div_two_lt_arctan x
  have hθ2 : θ < π / 2 := arctan_lt_pi_div_two x
  have hcos : 0 < cos (θ / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  -- the half-angle formula `tan (θ/2) = sin θ / (1 + cos θ)`
  have htan : tan (θ / 2) = sin θ / (1 + cos θ) := by
    have hsθ : sin θ = 2 * sin (θ / 2) * cos (θ / 2) := by
      rw [← sin_two_mul, mul_div_cancel₀ _ two_ne_zero]
    have hcθ : cos θ = 2 * cos (θ / 2) ^ 2 - 1 := by
      rw [← cos_two_mul, mul_div_cancel₀ _ two_ne_zero]
    rw [tan_eq_sin_div_cos, hsθ, hcθ]
    field_simp
    ring
  have hval : sin θ / (1 + cos θ) = x / (1 + Real.sqrt (1 + x ^ 2)) := by
    rw [hθ, sin_arctan, cos_arctan]
    have hr : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
    ring
  rw [← hval, ← htan, arctan_tan (by linarith) (by linarith)]
  ring

/-- The reduced argument of `arctan` is at most half the argument. -/
theorem abs_div_one_add_sqrt_sq_le_half (x : ℝ) :
    |x / (1 + Real.sqrt (1 + x ^ 2))| ≤ |x| / 2 := by
  have h1 : 1 ≤ Real.sqrt (1 + x ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg x]
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + Real.sqrt (1 + x ^ 2))]
  exact div_le_div_of_nonneg_left (abs_nonneg x) (by norm_num) (by linarith)

/-- `exp` halved, reconstructed by one squaring. -/
noncomputable def expHalf : ArgumentReduction exp where
  reduce x := x / 2
  g := exp
  reconstruct _ t := t ^ 2
  spec x := exp_eq_sq_exp_half x

/-- `arctan` halved, reconstructed by a doubling. -/
noncomputable def arctanHalf : ArgumentReduction arctan where
  reduce x := x / (1 + Real.sqrt (1 + x ^ 2))
  g := arctan
  reconstruct _ t := 2 * t
  spec x := arctan_eq_two_mul_arctan x

/-! ### Using symmetries -/

/-- `y = x / (2 + x)`, so that `(1 + y)/(1 − y) = 1 + x`. -/
noncomputable def symmetricLogVar (x : ℝ) : ℝ := x / (2 + x)

theorem one_add_div_one_sub_eq {x : ℝ} (hx : -1 < x) :
    (1 + symmetricLogVar x) / (1 - symmetricLogVar x) = 1 + x := by
  unfold symmetricLogVar
  have h2 : (2 + x) ≠ 0 := by linarith
  have h3 : 1 - x / (2 + x) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    field_simp at h
    linarith
  field_simp
  ring

/-- `|y| < 1` for `x > −1`. -/
theorem abs_symmetricLogVar_lt_one {x : ℝ} (hx : -1 < x) : |symmetricLogVar x| < 1 := by
  unfold symmetricLogVar
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 + x), div_lt_one (by linarith), abs_lt]
  constructor <;> linarith

/-- The symmetric series: `ln(1 + x) = 2 ∑ y^(2j+1)/(2j+1)` with `y = x/(2 + x)`, for `x > −1`. -/
theorem hasSum_log_one_add_symmetric {x : ℝ} (hx : -1 < x) :
    HasSum (fun j : ℕ => 2 * symmetricLogVar x ^ (2 * j + 1) / (2 * j + 1)) (log (1 + x)) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (abs_symmetricLogVar_lt_one hx)
  have hy1 : 0 < 1 - symmetricLogVar x := by
    have := abs_symmetricLogVar_lt_one hx; rw [abs_lt] at this; linarith
  have hy2 : 0 < 1 + symmetricLogVar x := by
    have := abs_symmetricLogVar_lt_one hx; rw [abs_lt] at this; linarith
  rw [← Real.log_div hy2.ne' hy1.ne', one_add_div_one_sub_eq hx] at h
  refine h.congr_fun fun j => ?_
  ring

/-- `y < x / 2` for `x > 0`: the symmetric substitution also reduces the argument. -/
theorem symmetricLogVar_lt_half {x : ℝ} (hx : 0 < x) : symmetricLogVar x < x / 2 := by
  unfold symmetricLogVar
  exact div_lt_div_of_pos_left hx (by norm_num) (by linarith)

end BZ

end Azurite
