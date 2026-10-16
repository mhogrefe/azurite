/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.RepeatedDoubling

/-!
# Brent–Zimmermann §4.3.3: Guard digits

Guard digits are digits beyond those wanted in the answer; the right number of them — the right
working precision — gives an accurate result without excessive cost.  The example is `exp x`
with the reduced argument `t = x / 2^k = O(2^(−k))`, `x = Θ(1)`:

* if `t` is accurate to `n` bits then `1 + t` is accurate to `n + k` bits, but *forward*
  summation at working precision `n` keeps only `n` of them; the `k` squarings then lose about
  one bit each, leaving `n − k` bits;
* *backward* summation (small terms first, `1` added last) at working precision `n + k` through
  the squarings gives `n + k` bits before the squarings and `n` bits at the end;
* alternatively evaluate `expm1 (x / 2^k)` with `expm1 x = exp x − 1`, whose doubling formula
  avoids the loss of significance for small `|x|` (Exercises 4.7–4.9).

What is formalized:

* `abs_one_add_mul_sub_le`, `relError_one_add_le` — `1 + t(1 + ε)` against `1 + t`: absolute
  error `|t ε| ≤ 2^(−(n+k))`, relative error at most `2^(1−(n+k))` (the `n + k` bits).
* `abs_mul_one_add_sub_one_le` — rounding at precision `n` afterwards adds `2^(−n)`, so the
  compound relative error is `≈ 2^(−n)` whatever the precision of the sum (only `n` bits kept).
* `abs_squareSeq_sub_exp_le_of_uniform` — the squaring model of §4.3.1 with a uniform
  per-operation bound `η`: final relative error `≤ 2^(k+3) η`; `forwardSummation_bits`
  (`η = 2^(−n)`: `n − k − 3` bits) and `backwardSummation_bits` (`η = 2^(−(n+k))`: `n − 3` bits)
  are the two scenarios of the text, up to the constant `8`.
* `expm1`, `expm1_two_mul` — `expm1 (2x) = expm1 x · (expm1 x + 2)`; `expm1_two_mul_perturbed`
  and `abs_expm1_two_mul_relError_le` — the doubling formula propagates a relative error `ε` to
  at most `2|ε| + ε²` for `x ≥ 0` (one bit per doubling, no cancellation);
  `expm1_of_exp_perturbed`, `expm1_le_mul_exp`, `relError_expm1_of_exp_ge` — computing
  `exp x − 1` from a rounded `exp x` with relative error `ρ` gives relative error at least
  `|ρ| / x` for `0 < x`, unbounded as `x → 0`: the loss of significance that `expm1` avoids.
-/

namespace Azurite

namespace BZ

open Finset Real

/-! ### `n + k` bits in `1 + t`, and what the working precision keeps -/

/-- `|(1 + t(1 + ε)) − (1 + t)| = |t| |ε| ≤ 2^(−k) · 2^(−n)`. -/
theorem abs_one_add_mul_sub_le {t ε : ℝ} {n k : ℕ} (ht : |t| ≤ (2 : ℝ) ^ (-(k : ℤ)))
    (hε : |ε| ≤ (2 : ℝ) ^ (-(n : ℤ))) :
    |(1 + t * (1 + ε)) - (1 + t)| ≤ (2 : ℝ) ^ (-((n + k : ℕ) : ℤ)) := by
  rw [show (1 + t * (1 + ε)) - (1 + t) = t * ε by ring, abs_mul]
  calc |t| * |ε| ≤ (2 : ℝ) ^ (-(k : ℤ)) * (2 : ℝ) ^ (-(n : ℤ)) := by gcongr
    _ = (2 : ℝ) ^ (-((n + k : ℕ) : ℤ)) := by rw [← zpow_add₀ (by norm_num)]; push_cast; ring_nf

/-- The relative error of `1 + t(1 + ε)` against `1 + t` is at most `2^(1−(n+k))` for `k ≥ 1`:
`1 + t` is accurate to `n + k` bits (up to one bit) when `t` is accurate to `n`. -/
theorem relError_one_add_le {t ε : ℝ} {n k : ℕ} (hk : 1 ≤ k) (ht : |t| ≤ (2 : ℝ) ^ (-(k : ℤ)))
    (hε : |ε| ≤ (2 : ℝ) ^ (-(n : ℤ))) :
    |(1 + t * (1 + ε)) - (1 + t)| ≤ (2 : ℝ) ^ (1 - ((n + k : ℕ) : ℤ)) * |1 + t| := by
  have hk' : (2 : ℝ) ^ (-(k : ℤ)) ≤ 1 / 2 := by
    calc (2 : ℝ) ^ (-(k : ℤ)) ≤ (2 : ℝ) ^ (-(1 : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  have ht' : |t| ≤ 1 / 2 := ht.trans hk'
  have h1t : 1 / 2 ≤ |1 + t| := by
    rw [abs_le] at ht'
    rw [abs_of_pos (by linarith)]; linarith
  calc |(1 + t * (1 + ε)) - (1 + t)| ≤ (2 : ℝ) ^ (-((n + k : ℕ) : ℤ)) :=
        abs_one_add_mul_sub_le ht hε
    _ = (2 : ℝ) ^ (1 - ((n + k : ℕ) : ℤ)) * (1 / 2) := by
        rw [show (1 : ℤ) - ((n + k : ℕ) : ℤ) = -((n + k : ℕ) : ℤ) + 1 by ring,
          zpow_add₀ (by norm_num), zpow_one]
        ring
    _ ≤ (2 : ℝ) ^ (1 - ((n + k : ℕ) : ℤ)) * |1 + t| := by gcongr

/-- Two relative perturbations compound to `|δ₁| + |δ₂| + |δ₁||δ₂|`: rounding the sum at
precision `n` (`|δ₂| ≤ 2^(−n)`) leaves a relative error of order `2^(−n)` however accurate the
sum was. -/
theorem abs_mul_one_add_sub_one_le (δ₁ δ₂ : ℝ) :
    |(1 + δ₁) * (1 + δ₂) - 1| ≤ |δ₁| + |δ₂| + |δ₁| * |δ₂| := by
  rw [show (1 + δ₁) * (1 + δ₂) - 1 = δ₁ + δ₂ + δ₁ * δ₂ by ring]
  calc |δ₁ + δ₂ + δ₁ * δ₂| ≤ |δ₁ + δ₂| + |δ₁ * δ₂| := abs_add_le _ _
    _ ≤ |δ₁| + |δ₂| + |δ₁| * |δ₂| := by rw [abs_mul]; gcongr; exact abs_add_le _ _

/-! ### Forward and backward summation through the squarings -/

/-- The squaring model with a uniform bound: a start with relative error `|ε| ≤ 3η` (the
summed series, rounded) and squarings with relative errors `|θ_i| ≤ η`, where `2^(k+2) η ≤ 1`,
give a final relative error at most `2^(k+3) η`. -/
theorem abs_squareSeq_sub_exp_le_of_uniform (x : ℝ) (k : ℕ) {ε η : ℝ} (θ : ℕ → ℝ)
    (hε : |ε| ≤ 3 * η) (hθ : ∀ i, |θ i| ≤ η) (hη : (2 : ℝ) ^ (k + 2) * η ≤ 1) :
    |squareSeq (exp (x / 2 ^ k) * (1 + ε)) θ k - exp x| ≤ (2 : ℝ) ^ (k + 3) * η * exp x := by
  have hη0 : 0 ≤ η := le_trans (abs_nonneg _) (hθ 0)
  have hsum : ∑ i ∈ range k, (2 ^ (k - 1 - i) : ℝ) * |θ i| ≤ (2 : ℝ) ^ k * η := by
    calc ∑ i ∈ range k, (2 ^ (k - 1 - i) : ℝ) * |θ i|
        ≤ ∑ i ∈ range k, (2 ^ (k - 1 - i) : ℝ) * η := by
          gcongr with i _; exact hθ i
      _ = (∑ i ∈ range k, (2 : ℝ) ^ (k - 1 - i)) * η := by rw [sum_mul]
      _ ≤ (2 : ℝ) ^ k * η := by
          gcongr
          -- `∑_{i<k} 2^(k−1−i) = 2^k − 1`
          have : ∑ i ∈ range k, (2 : ℝ) ^ (k - 1 - i) = ∑ i ∈ range k, (2 : ℝ) ^ i := by
            rw [← sum_range_reflect]
            exact sum_congr rfl fun i hi => by
              rw [mem_range] at hi; congr 1; omega
          rw [this, geom_sum_eq (by norm_num)]
          have : (0 : ℝ) < 2 ^ k := by positivity
          rw [div_le_iff₀ (by norm_num)]; linarith
  have hS : (2 ^ k : ℝ) * |ε| + ∑ i ∈ range k, (2 ^ (k - 1 - i) : ℝ) * |θ i|
      ≤ (2 : ℝ) ^ (k + 2) * η := by
    calc (2 ^ k : ℝ) * |ε| + ∑ i ∈ range k, (2 ^ (k - 1 - i) : ℝ) * |θ i|
        ≤ (2 ^ k : ℝ) * (3 * η) + (2 : ℝ) ^ k * η := by gcongr
      _ = (2 : ℝ) ^ (k + 2) * η := by rw [pow_add]; ring
  calc |squareSeq (exp (x / 2 ^ k) * (1 + ε)) θ k - exp x|
      ≤ 2 * ((2 ^ k : ℝ) * |ε| + ∑ i ∈ range k, (2 ^ (k - 1 - i) : ℝ) * |θ i|) * exp x :=
        abs_squareSeq_sub_exp_le x k ε θ (hS.trans hη)
    _ ≤ 2 * ((2 : ℝ) ^ (k + 2) * η) * exp x := by gcongr
    _ = (2 : ℝ) ^ (k + 3) * η * exp x := by rw [pow_succ]; ring

/-- Forward summation at working precision `n`: the final result has about `n − k − 3` bits. -/
theorem forwardSummation_bits (x : ℝ) {k n : ℕ} {ε : ℝ} (θ : ℕ → ℝ)
    (hε : |ε| ≤ 3 * (2 : ℝ) ^ (-(n : ℤ))) (hθ : ∀ i, |θ i| ≤ (2 : ℝ) ^ (-(n : ℤ)))
    (hn : k + 2 ≤ n) :
    |squareSeq (exp (x / 2 ^ k) * (1 + ε)) θ k - exp x|
      ≤ (2 : ℝ) ^ (-((n : ℤ) - k - 3)) * exp x := by
  have h := abs_squareSeq_sub_exp_le_of_uniform x k θ hε hθ (by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by push_cast; omega))
  convert h using 2
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
  congr 1; push_cast; ring

/-- Backward summation at working precision `n + k`: the final result has about `n − 3` bits. -/
theorem backwardSummation_bits (x : ℝ) {k n : ℕ} {ε : ℝ} (θ : ℕ → ℝ)
    (hε : |ε| ≤ 3 * (2 : ℝ) ^ (-((n + k : ℕ) : ℤ)))
    (hθ : ∀ i, |θ i| ≤ (2 : ℝ) ^ (-((n + k : ℕ) : ℤ))) (hn : 2 ≤ n) :
    |squareSeq (exp (x / 2 ^ k) * (1 + ε)) θ k - exp x|
      ≤ (2 : ℝ) ^ (-((n : ℤ) - 3)) * exp x := by
  have h := abs_squareSeq_sub_exp_le_of_uniform x k θ hε hθ (by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by push_cast; omega))
  convert h using 2
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
  congr 1; push_cast; ring

/-! ### `expm1` -/

/-- `expm1 x = exp x − 1`. -/
noncomputable def expm1 (x : ℝ) : ℝ := exp x - 1

/-- The doubling formula `expm1 (2x) = expm1 x · (expm1 x + 2)`, which stays in terms of
`expm1` and never forms `exp x − 1` from `exp x`. -/
theorem expm1_two_mul (x : ℝ) : expm1 (2 * x) = expm1 x * (expm1 x + 2) := by
  unfold expm1
  rw [two_mul, exp_add]
  ring

/-- `expm1 x > −1`, so `expm1 x + 2 > 1`. -/
theorem expm1_add_two_pos (x : ℝ) : 0 < expm1 x + 2 := by
  unfold expm1; linarith [exp_pos x]

/-- The doubling formula applied to `expm1 x (1 + ε)`: the result is `expm1 (2x)` times
`1 + ε (2(e + 1) + e ε) / (e + 2)` with `e = expm1 x`. -/
theorem expm1_two_mul_perturbed (x ε : ℝ) :
    expm1 x * (1 + ε) * (expm1 x * (1 + ε) + 2)
      = expm1 (2 * x) * (1 + ε * (2 * (expm1 x + 1) + expm1 x * ε) / (expm1 x + 2)) := by
  rw [expm1_two_mul]
  have h := (expm1_add_two_pos x).ne'
  field_simp
  ring

/-- For `x ≥ 0` the relative error of the doubling step is at most `2|ε| + ε²`: about one bit
per doubling, with no cancellation. -/
theorem abs_expm1_two_mul_relError_le {x : ℝ} (hx : 0 ≤ x) (ε : ℝ) :
    |ε * (2 * (expm1 x + 1) + expm1 x * ε) / (expm1 x + 2)| ≤ 2 * |ε| + ε ^ 2 := by
  have he : 0 ≤ expm1 x := by unfold expm1; linarith [one_le_exp_iff.mpr hx]
  have h2 := expm1_add_two_pos x
  rw [abs_div, abs_of_pos h2, div_le_iff₀ h2, abs_mul]
  have hb : |2 * (expm1 x + 1) + expm1 x * ε| ≤ 2 * (expm1 x + 1) + expm1 x * |ε| := by
    calc |2 * (expm1 x + 1) + expm1 x * ε| ≤ |2 * (expm1 x + 1)| + |expm1 x * ε| := abs_add_le _ _
      _ = 2 * (expm1 x + 1) + expm1 x * |ε| := by
          rw [abs_of_pos (by linarith), abs_mul, abs_of_nonneg he]
  calc |ε| * |2 * (expm1 x + 1) + expm1 x * ε| ≤ |ε| * (2 * (expm1 x + 1) + expm1 x * |ε|) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ ≤ (2 * |ε| + ε ^ 2) * (expm1 x + 2) := by
        rw [← sq_abs ε]; nlinarith [abs_nonneg ε, sq_nonneg |ε|]

/-- Computing `exp x − 1` from a rounded exponential `exp x (1 + ρ)` makes an absolute error
`ρ exp x`. -/
theorem expm1_of_exp_perturbed (x ρ : ℝ) : (exp x * (1 + ρ) - 1) - expm1 x = ρ * exp x := by
  unfold expm1; ring

/-- `expm1 x ≤ x exp x` (from `1 − x ≤ exp (−x)`). -/
theorem expm1_le_mul_exp (x : ℝ) : expm1 x ≤ x * exp x := by
  unfold expm1
  have h := add_one_le_exp (-x)
  rw [exp_neg] at h
  have hpos := exp_pos x
  have h' : (-x + 1) * exp x ≤ 1 := by
    calc (-x + 1) * exp x ≤ (exp x)⁻¹ * exp x := mul_le_mul_of_nonneg_right h hpos.le
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  nlinarith

/-- The loss of significance: for `0 < x`, the relative error of `exp x − 1` computed from an
exponential with relative error `ρ` is at least `|ρ| / x`, unbounded as `x → 0`. -/
theorem relError_expm1_of_exp_ge {x : ℝ} (hx : 0 < x) (ρ : ℝ) :
    |ρ| / x ≤ |(exp x * (1 + ρ) - 1) - expm1 x| / expm1 x := by
  rw [expm1_of_exp_perturbed, abs_mul, abs_of_pos (exp_pos x)]
  have hpos : 0 < expm1 x := by unfold expm1; linarith [exp_pos x, add_one_lt_exp hx.ne']
  rw [div_le_div_iff₀ hx hpos]
  have := expm1_le_mul_exp x
  nlinarith [abs_nonneg ρ]

end BZ

end Azurite
