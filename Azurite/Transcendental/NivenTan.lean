/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.NivenSin
import Mathlib.NumberTheory.Real.Irrational

/-!
# Niven's theorem for the tangent

`tan (2πr)` for a rational `r` is irrational unless the reduced denominator of `r` is `1`, `2`
(the value `0`), `8` (the values `±1`) or `4` (the poles): `irrational_tan_two_pi_mul_rat`.  If
`tan (2πr) = t` is rational and `cos (2πr) ≠ 0`, then `cos (4πr) = 2/(1 + t²) − 1` is rational,
hence one of `−1, −1/2, 0, 1/2, 1` (Niven for the cosine); `−1` is impossible, `±1/2` would make
`t² = 3` or `1/3`, and `0`, `1` put the denominator of `2r` in `{4, 1}`, that of `r` among the
divisors of `8`.  The values for `0 ≤ r < 1` are given through the numerator.
-/

namespace Azurite

open Real

theorem eq_of_dvd_eight {d : ℕ} (h : d ∣ 8) : d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by
  have hle := Nat.le_of_dvd (by norm_num) h
  interval_cases d <;> omega

/-- No rational has square `3`. -/
theorem rat_sq_ne_three (t : ℚ) : t ^ 2 ≠ 3 := by
  intro h
  have h3 : Irrational (√(3 : ℝ)) := by
    have := Nat.Prime.irrational_sqrt (p := 3) Nat.prime_three
    simpa using this
  have hsq : ((|t| : ℚ) : ℝ) = √(3 : ℝ) := by
    have h' : ((|t| : ℚ) : ℝ) ^ 2 = 3 := by
      have : (|t| : ℚ) ^ 2 = 3 := by rw [sq_abs]; exact h
      exact_mod_cast this
    rw [← h', Real.sqrt_sq (by positivity)]
  exact h3 ⟨|t|, hsq⟩

/-- **Niven's theorem for the tangent**: `tan (2πr)` is irrational for a rational `r` whose
reduced denominator is not `1`, `2`, `4` or `8`. -/
theorem irrational_tan_two_pi_mul_rat {r : ℚ} (h1 : r.den ≠ 1) (h2 : r.den ≠ 2)
    (h4 : r.den ≠ 4) (h8 : r.den ≠ 8) : Irrational (tan (2 * π * r)) := by
  rintro ⟨t, ht⟩
  have hc : cos (2 * π * r) ≠ 0 := fun h => h4 (den_eq_four_of_cos_two_pi_mul_rat_eq_zero h)
  have hsq := Real.inv_one_add_tan_sq hc
  rw [← ht] at hsq
  have h2r : cos (2 * π * ((2 * r : ℚ) : ℝ)) = ((2 * (1 + t ^ 2)⁻¹ - 1 : ℚ) : ℝ) := by
    push_cast
    rw [show 2 * π * (2 * (r : ℝ)) = 2 * (2 * π * r) by ring, Real.cos_two_mul, hsq]
  have hpos : (0 : ℚ) < 1 + t ^ 2 := by positivity
  have key : (2 * r).den ∣ 4 → False := by
    intro hd
    obtain ⟨k, hk⟩ := exists_int_mul_of_den_dvd hd
    have h8r : ((8 : ℕ) : ℚ) * r = (k : ℚ) := by push_cast at hk ⊢; linarith
    rcases eq_of_dvd_eight (den_dvd_of_mul_eq_int (by norm_num) h8r) with h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h4 h
    · exact h8 h
  rcases cos_two_pi_mul_rat_mem_of_rat (2 * r) h2r with h | h | h | h | h
  · have : (1 + t ^ 2)⁻¹ = 0 := by linarith
    exact (inv_ne_zero hpos.ne') this
  · have h' : (1 + t ^ 2)⁻¹ = 1 / 4 := by linarith
    have : 1 + t ^ 2 = 4 := by
      rw [← inv_inv (1 + t ^ 2), h']; norm_num
    exact rat_sq_ne_three t (by linarith)
  · refine key ?_
    have := den_eq_four_of_cos_two_pi_mul_rat_eq_zero (r := 2 * r) (by rw [h2r, h]; norm_num)
    rw [this]
  · have h' : (1 + t ^ 2)⁻¹ = 3 / 4 := by linarith
    have h'' : 1 + t ^ 2 = 4 / 3 := by
      rw [← inv_inv (1 + t ^ 2), h']; norm_num
    have ht0 : t ≠ 0 := by
      rintro rfl
      norm_num at h''
    refine rat_sq_ne_three t⁻¹ ?_
    rw [inv_pow, show t ^ 2 = 1 / 3 by linarith]
    norm_num
  · refine key ?_
    have := den_eq_one_of_cos_two_pi_mul_rat_eq_one (r := 2 * r) (by rw [h2r, h]; norm_num)
    rw [this]
    norm_num

/-- `tan (2πr)` is irrational for a rational `0 < r < 1/8`. -/
theorem irrational_tan_two_pi_mul_rat_of_small {r : ℚ} (h0 : 0 < r) (h1 : r < 1 / 8) :
    Irrational (tan (2 * π * r)) := by
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hnum : (1 : ℚ) ≤ r.num := by exact_mod_cast Rat.num_pos.mpr h0
  have hle : (1 : ℚ) / r.den ≤ r := by
    rw [div_le_iff₀ hden, Rat.mul_den_eq_num]
    exact hnum
  have key : ∀ k : ℕ, 0 < k → k ≤ 8 → r.den ≠ k := by
    intro k hk0 hk6 h
    rw [h] at hle
    have hk : (0 : ℚ) < k := by exact_mod_cast hk0
    have hk' : (k : ℚ) ≤ 8 := by exact_mod_cast hk6
    have : (1 : ℚ) / 8 ≤ 1 / k := one_div_le_one_div_of_le hk hk'
    linarith
  exact irrational_tan_two_pi_mul_rat (key 1 (by norm_num) (by norm_num))
    (key 2 (by norm_num) (by norm_num)) (key 4 (by norm_num) (by norm_num))
    (key 8 (by norm_num) (by norm_num))

/-! ### The values at the denominators `1`, `2` and `8` -/

/-- `tan (2πr) = 0` for the denominators `1` and `2`. -/
theorem tan_two_pi_mul_rat_of_den_dvd_two {r : ℚ} (h : r.den ∣ 2) : tan (2 * π * r) = 0 := by
  rw [Real.tan_eq_sin_div_cos, sin_two_pi_mul_rat_of_den_dvd_two h, zero_div]

/-- `tan (2πr) = ±1` for the denominator `8` (`r = 1/8, 5/8` or `3/8, 7/8`). -/
theorem tan_two_pi_mul_rat_of_den_eq_eight {r : ℚ} (h : r.den = 8) (h0 : 0 ≤ r) (h1 : r < 1) :
    tan (2 * π * r) = if r.num = 1 ∨ r.num = 5 then 1 else -1 := by
  obtain ⟨hn0, hn1⟩ := num_bounds_of_unit h0 h1
  have hc := r.reduced
  rw [h] at hc hn1
  rw [Rat.cast_def, h]
  generalize r.num = n at *
  have hn : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 := by
    have hn1' : n < 8 := by exact_mod_cast hn1
    interval_cases n <;> first | omega | (exact absurd hc (by decide))
  rcases hn with rfl | rfl | rfl | rfl
  · rw [ite_eq_left (Or.inl rfl),
      show 2 * π * (((1 : ℤ) : ℝ) / ((8 : ℕ) : ℝ)) = π / 4 by push_cast; ring, Real.tan_pi_div_four]
  · rw [ite_eq_right (by norm_num),
      show 2 * π * (((3 : ℤ) : ℝ) / ((8 : ℕ) : ℝ)) = π - π / 4 by push_cast; ring,
      Real.tan_pi_sub, Real.tan_pi_div_four]
  · rw [ite_eq_left (Or.inr rfl),
      show 2 * π * (((5 : ℤ) : ℝ) / ((8 : ℕ) : ℝ)) = π / 4 + π by push_cast; ring,
      Real.tan_add_pi, Real.tan_pi_div_four]
  · rw [ite_eq_right (by norm_num),
      show 2 * π * (((7 : ℤ) : ℝ) / ((8 : ℕ) : ℝ)) = -(π / 4) + 2 * π by push_cast; ring,
      show -(π / 4) + 2 * π = -(π / 4) + π + π by ring, Real.tan_add_pi, Real.tan_add_pi,
      Real.tan_neg, Real.tan_pi_div_four]

end Azurite
