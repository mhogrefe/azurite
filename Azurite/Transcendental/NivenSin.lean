/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.Niven

/-!
# Niven's theorem for the sine

`sin (2πr)` for a rational `r` is rational exactly when the reduced denominator of `r` is `1`,
`2`, `4` or `12` (`irrational_sin_two_pi_mul_rat`), by `sin (2πr) = cos (2π (r − 1/4))` and
Niven's theorem for the cosine (`Transcendental/Niven.lean`); the values there are `0` (`1`,
`2`), `±1` (`4`) and `±1/2` (`12`), given for `0 ≤ r < 1` through the numerator.
-/

namespace Azurite

open Real

theorem sin_two_pi_mul_eq_cos (t : ℝ) :
    sin (2 * π * t) = cos (2 * π * (t - 1 / 4)) := by
  rw [show 2 * π * (t - 1 / 4) = 2 * π * t - π / 2 by ring, Real.cos_sub_pi_div_two]

/-- `N r` is an integer when the denominator of `r` divides `N`. -/
theorem exists_int_mul_of_den_dvd {r : ℚ} {N : ℕ} (h : r.den ∣ N) :
    ∃ k : ℤ, (N : ℚ) * r = k := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨c * r.num, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num r]
  ring

/-- The denominator of `r` divides `N` when `N r` is an integer. -/
theorem den_dvd_of_mul_eq_int {r : ℚ} {N : ℕ} (hN : 0 < N) {k : ℤ} (h : (N : ℚ) * r = k) :
    r.den ∣ N := by
  have hN' : (N : ℚ) ≠ 0 := by positivity
  have hr : r = (k : ℚ) / ((N : ℤ) : ℚ) := by
    rw [Int.cast_natCast, eq_div_iff hN', mul_comm]
    exact h
  have h2 := Rat.den_dvd k (N : ℤ)
  rw [Rat.divInt_eq_div, ← hr] at h2
  exact_mod_cast h2

theorem eq_of_dvd_four {d : ℕ} (h : d ∣ 4) : d = 1 ∨ d = 2 ∨ d = 4 := by
  have hle := Nat.le_of_dvd (by norm_num) h
  interval_cases d <;> omega

theorem eq_of_dvd_twelve {d : ℕ} (h : d ∣ 12) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 ∨ d = 12 := by
  have hle := Nat.le_of_dvd (by norm_num) h
  interval_cases d <;> omega

/-- **Niven's theorem for the sine**: `sin (2πr)` is irrational for a rational `r` whose reduced
denominator is not `1`, `2`, `4` or `12`. -/
theorem irrational_sin_two_pi_mul_rat {r : ℚ} (h1 : r.den ≠ 1) (h2 : r.den ≠ 2)
    (h4 : r.den ≠ 4) (h12 : r.den ≠ 12) : Irrational (sin (2 * π * r)) := by
  have hs : sin (2 * π * r) = cos (2 * π * ((r - 1 / 4 : ℚ) : ℝ)) := by
    rw [sin_two_pi_mul_eq_cos]; push_cast; rfl
  rw [hs]
  set s : ℚ := r - 1 / 4 with hsdef
  have hr : r = s + 1 / 4 := by rw [hsdef]; ring
  have key4 : s.den ∣ 4 → False := by
    intro hd
    obtain ⟨k, hk⟩ := exists_int_mul_of_den_dvd hd
    have h4r : ((4 : ℕ) : ℚ) * r = ((k + 1 : ℤ) : ℚ) := by
      rw [hr]; push_cast at hk ⊢; linarith
    rcases eq_of_dvd_four (den_dvd_of_mul_eq_int (by norm_num) h4r) with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h4 h
  have key6 : s.den ∣ 6 → False := by
    intro hd
    obtain ⟨k, hk⟩ := exists_int_mul_of_den_dvd hd
    have h12r : ((12 : ℕ) : ℚ) * r = ((2 * k + 3 : ℤ) : ℚ) := by
      rw [hr]; push_cast at hk ⊢; linarith
    have hsix : r.den ∣ 6 → False := by
      intro hd6
      obtain ⟨j, hj⟩ := exists_int_mul_of_den_dvd hd6
      have hq : ((2 * j : ℤ) : ℚ) = ((2 * k + 3 : ℤ) : ℚ) := by
        rw [hr] at hj; push_cast at hk hj ⊢; linarith
      have hz : 2 * j = 2 * k + 3 := by exact_mod_cast hq
      omega
    rcases eq_of_dvd_twelve (den_dvd_of_mul_eq_int (by norm_num) h12r) with h | h | h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact hsix (by rw [h]; norm_num)
    · exact h4 h
    · exact hsix (by rw [h])
    · exact h12 h
  exact irrational_cos_two_pi_mul_rat (fun h => key4 (by rw [h]; norm_num))
    (fun h => key4 (by rw [h]; norm_num)) (fun h => key6 (by rw [h]; norm_num))
    (fun h => key4 (by rw [h])) (fun h => key6 (by rw [h]))

/-- `sin (2πr)` is irrational for a rational `0 < r < 1/12`. -/
theorem irrational_sin_two_pi_mul_rat_of_small {r : ℚ} (h0 : 0 < r) (h1 : r < 1 / 12) :
    Irrational (sin (2 * π * r)) := by
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hnum : (1 : ℚ) ≤ r.num := by exact_mod_cast Rat.num_pos.mpr h0
  have hle : (1 : ℚ) / r.den ≤ r := by
    rw [div_le_iff₀ hden, Rat.mul_den_eq_num]
    exact hnum
  have key : ∀ k : ℕ, 0 < k → k ≤ 12 → r.den ≠ k := by
    intro k hk0 hk6 h
    rw [h] at hle
    have hk : (0 : ℚ) < k := by exact_mod_cast hk0
    have hk' : (k : ℚ) ≤ 12 := by exact_mod_cast hk6
    have : (1 : ℚ) / 12 ≤ 1 / k := one_div_le_one_div_of_le hk hk'
    linarith
  exact irrational_sin_two_pi_mul_rat (key 1 (by norm_num) (by norm_num))
    (key 2 (by norm_num) (by norm_num)) (key 4 (by norm_num) (by norm_num))
    (key 12 (by norm_num) (by norm_num))

/-! ### The values at the four denominators -/

/-- `sin (2πr) = 0` for the denominators `1` and `2`. -/
theorem sin_two_pi_mul_rat_of_den_dvd_two {r : ℚ} (h : r.den ∣ 2) : sin (2 * π * r) = 0 := by
  obtain ⟨k, hk⟩ := exists_int_mul_of_den_dvd h
  have hk' : (2 : ℝ) * (r : ℝ) = (k : ℝ) := by exact_mod_cast hk
  rw [show 2 * π * (r : ℝ) = k * π by rw [← hk']; ring]
  exact Real.sin_int_mul_pi k

/-- The numerator of a rational `0 ≤ r < 1` lies in `[0, den)`. -/
theorem num_bounds_of_unit {r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1) : 0 ≤ r.num ∧ r.num < r.den := by
  refine ⟨Rat.num_nonneg.mpr h0, ?_⟩
  have hd : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have h : (r.num : ℚ) < r.den := by rw [← Rat.mul_den_eq_num r]; nlinarith
  exact_mod_cast h

/-- `sin (2πr) = ±1` for the denominator `4` (`r = 1/4` or `3/4`). -/
theorem sin_two_pi_mul_rat_of_den_eq_four {r : ℚ} (h : r.den = 4) (h0 : 0 ≤ r) (h1 : r < 1) :
    sin (2 * π * r) = if r.num = 1 then 1 else -1 := by
  obtain ⟨hn0, hn1⟩ := num_bounds_of_unit h0 h1
  have hc := r.reduced
  rw [h] at hc hn1
  rw [Rat.cast_def, h]
  generalize r.num = n at *
  have hn : n = 1 ∨ n = 3 := by
    have hn1' : n < 4 := by exact_mod_cast hn1
    interval_cases n <;> first | omega | (exact absurd hc (by decide))
  rcases hn with rfl | rfl
  · rw [ite_eq_left rfl, show 2 * π * (((1 : ℤ) : ℝ) / ((4 : ℕ) : ℝ)) = π / 2 by push_cast; ring,
      Real.sin_pi_div_two]
  · rw [ite_eq_right (by norm_num),
      show 2 * π * (((3 : ℤ) : ℝ) / ((4 : ℕ) : ℝ)) = π / 2 + π by push_cast; ring,
      Real.sin_add_pi, Real.sin_pi_div_two]

/-- `sin (2πr) = ±1/2` for the denominator `12` (`r = 1/12, 5/12` or `7/12, 11/12`). -/
theorem sin_two_pi_mul_rat_of_den_eq_twelve {r : ℚ} (h : r.den = 12) (h0 : 0 ≤ r)
    (h1 : r < 1) : sin (2 * π * r) = if r.num = 1 ∨ r.num = 5 then 1 / 2 else -1 / 2 := by
  obtain ⟨hn0, hn1⟩ := num_bounds_of_unit h0 h1
  have hc := r.reduced
  rw [h] at hc hn1
  rw [Rat.cast_def, h]
  generalize r.num = n at *
  have hn : n = 1 ∨ n = 5 ∨ n = 7 ∨ n = 11 := by
    have hn1' : n < 12 := by exact_mod_cast hn1
    interval_cases n <;> first | omega | (exact absurd hc (by decide))
  rcases hn with rfl | rfl | rfl | rfl
  · rw [ite_eq_left (Or.inl rfl),
      show 2 * π * (((1 : ℤ) : ℝ) / ((12 : ℕ) : ℝ)) = π / 6 by push_cast; ring,
      Real.sin_pi_div_six]
  · rw [ite_eq_left (Or.inr rfl),
      show 2 * π * (((5 : ℤ) : ℝ) / ((12 : ℕ) : ℝ)) = π - π / 6 by push_cast; ring,
      Real.sin_pi_sub, Real.sin_pi_div_six]
  · rw [ite_eq_right (by norm_num),
      show 2 * π * (((7 : ℤ) : ℝ) / ((12 : ℕ) : ℝ)) = π / 6 + π by push_cast; ring,
      Real.sin_add_pi, Real.sin_pi_div_six]
    ring
  · rw [ite_eq_right (by norm_num),
      show 2 * π * (((11 : ℤ) : ℝ) / ((12 : ℕ) : ℝ)) = 2 * π - π / 6 by push_cast; ring,
      Real.sin_two_pi_sub, Real.sin_pi_div_six]
    ring

end Azurite
