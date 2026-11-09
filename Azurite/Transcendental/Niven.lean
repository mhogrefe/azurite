/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.NumberTheory.Real.Irrational

/-!
# Niven's theorem: the rational values of `cos (2πr)`

For a rational `r`, `cos (2πr)` is rational exactly when the denominator of `r` is `1`, `2`, `3`,
`4` or `6`, with the values `1`, `−1`, `−1/2`, `0`, `1/2`.

* `isIntegral_two_cos_two_pi_mul_rat`: `2 cos (2πr)` is an algebraic integer
  (`e^{2πir} + e^{−2πir}`, both roots of unity).
* `cos_two_pi_mul_rat_mem_of_rat`: a rational `cos (2πr)` is one of `−1, −1/2, 0, 1/2, 1`
  (an algebraic integer that is rational is an integer, of modulus at most `2`).
* `den_mem_of_cos_two_pi_mul_rat_eq_*`: each of the five values forces the denominator.
* `irrational_cos_two_pi_mul_rat`: `cos (2πr)` is irrational when `r.den ∉ {1, 2, 3, 4, 6}`.
* `cos_two_pi_mul_rat_of_den_eq_*`: the values at the five denominators.

The driver `cosWithPeriodPrecRound` (`AzFloat/CosPeriod.lean`) decides rationality by the
reduced denominator of the fractional part of `x/u` and certifies its Ziv loop by the
irrationality.
-/

namespace Azurite

open Real

/-! ### `2 cos (2πr)` is an algebraic integer -/

/-- `e^{2πi r}` is an algebraic integer: a root of `X^den − 1`. -/
theorem isIntegral_exp_two_pi_mul_rat_mul_I (r : ℚ) :
    IsIntegral ℤ (Complex.exp (2 * Real.pi * (r : ℂ) * Complex.I)) := by
  have hden : 0 < r.den := r.den_pos
  refine IsIntegral.of_pow hden ?_
  rw [← Complex.exp_nat_mul]
  have : (r.den : ℂ) * (2 * Real.pi * (r : ℂ) * Complex.I)
      = (r.num : ℂ) * (2 * Real.pi * Complex.I) := by
    have h : (r.den : ℂ) * (r : ℂ) = (r.num : ℂ) := by
      have hd : (r.den : ℂ) ≠ 0 := by exact_mod_cast hden.ne'
      rw [Rat.cast_def]
      field_simp
    linear_combination (2 * Real.pi * Complex.I) * h
  rw [this, Complex.exp_int_mul_two_pi_mul_I]
  exact isIntegral_one

theorem isIntegral_two_cos_two_pi_mul_rat (r : ℚ) :
    IsIntegral ℤ (2 * Real.cos (2 * Real.pi * r)) := by
  have h1 := isIntegral_exp_two_pi_mul_rat_mul_I r
  have h2 := isIntegral_exp_two_pi_mul_rat_mul_I (-r)
  have hsum := h1.add h2
  have heq : Complex.exp (2 * Real.pi * (r : ℂ) * Complex.I)
      + Complex.exp (2 * Real.pi * ((-r : ℚ) : ℂ) * Complex.I)
      = ((2 * Real.cos (2 * Real.pi * r) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.two_cos]
    congr 1
    congr 1
    ring
  rw [heq] at hsum
  have hsum' : IsIntegral ℤ (algebraMap ℝ ℂ (2 * Real.cos (2 * Real.pi * r))) := by
    rw [Complex.coe_algebraMap]
    exact hsum
  exact (isIntegral_algebraMap_iff (A := ℝ) (B := ℂ)).mp hsum'

/-- A rational `cos (2πr)` is one of `−1, −1/2, 0, 1/2, 1`. -/
theorem cos_two_pi_mul_rat_mem_of_rat (r : ℚ) {s : ℚ} (hs : Real.cos (2 * Real.pi * r) = s) :
    s = -1 ∨ s = -1 / 2 ∨ s = 0 ∨ s = 1 / 2 ∨ s = 1 := by
  have hint := isIntegral_two_cos_two_pi_mul_rat r
  rw [hs] at hint
  have hint' : IsIntegral ℤ (algebraMap ℚ ℝ (2 * s)) := by
    rw [eq_ratCast]; push_cast; exact hint
  rw [isIntegral_algebraMap_iff (A := ℚ) (B := ℝ)] at hint'
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hm' : (m : ℚ) = 2 * s := hm
  have hbound := Real.abs_cos_le_one (2 * Real.pi * r)
  rw [hs] at hbound
  have hb : |(s : ℝ)| ≤ 1 := hbound
  have hb' : |s| ≤ 1 := by exact_mod_cast hb
  have hm2 : |(m : ℚ)| ≤ 2 := by rw [hm', abs_mul, abs_two]; linarith
  have hm3 : |m| ≤ 2 := by exact_mod_cast hm2
  have hs2 : s = m / 2 := by rw [hm']; ring
  rw [abs_le] at hm3
  have : m = -2 ∨ m = -1 ∨ m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [hs2]

/-! ### The denominators forced by the five values -/

theorem rat_eq_of_two_pi_mul_eq {r : ℚ} {t : ℝ} (h : 2 * Real.pi * r = 2 * Real.pi * t) :
    (r : ℝ) = t := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi h

theorem den_eq_of_coprime_den {a : ℤ} {b : ℕ} {r : ℚ} (hr : (r : ℝ) = (a : ℝ) / b) (hb : 0 < b)
    (h : Nat.Coprime a.natAbs b) : r.den = b := by
  have hq : r = (a : ℚ) / b := by exact_mod_cast hr
  have := Rat.den_div_eq_of_coprime (a := a) (b := b) (by exact_mod_cast hb)
    (by rwa [Int.natAbs_natCast])
  rw [hq]
  exact_mod_cast this

/-- `Nat.Coprime` of the absolute values from `IsCoprime` over `ℤ`. -/
theorem coprime_natAbs_of_isCoprime {a b : ℤ} (h : IsCoprime a b) :
    Nat.Coprime a.natAbs b.natAbs :=
  Int.isCoprime_iff_gcd_eq_one.mp h

theorem den_eq_one_of_cos_two_pi_mul_rat_eq_one {r : ℚ} (h : Real.cos (2 * Real.pi * r) = 1) :
    r.den = 1 := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp h
  have : (r : ℝ) = n := rat_eq_of_two_pi_mul_eq (by rw [← hn]; ring)
  have hq : r = (n : ℚ) := by exact_mod_cast this
  rw [hq, Rat.den_intCast]

theorem den_eq_two_of_cos_two_pi_mul_rat_eq_neg_one {r : ℚ}
    (h : Real.cos (2 * Real.pi * r) = -1) : r.den = 2 := by
  have h' : Real.cos (2 * Real.pi * r - Real.pi) = 1 := by rw [Real.cos_sub_pi, h]; ring
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp h'
  have : (r : ℝ) = ((2 * n + 1 : ℤ) : ℝ) / ((2 : ℕ) : ℝ) :=
    rat_eq_of_two_pi_mul_eq (by push_cast; linear_combination -hn)
  exact den_eq_of_coprime_den this (by norm_num)
    (coprime_natAbs_of_isCoprime (a := 2 * n + 1) (b := 2) ⟨1, -n, by ring⟩)

theorem den_eq_four_of_cos_two_pi_mul_rat_eq_zero {r : ℚ}
    (h : Real.cos (2 * Real.pi * r) = 0) : r.den = 4 := by
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h
  have : (r : ℝ) = ((2 * k + 1 : ℤ) : ℝ) / ((4 : ℕ) : ℝ) :=
    rat_eq_of_two_pi_mul_eq (by push_cast; linear_combination hk)
  exact den_eq_of_coprime_den this (by norm_num)
    (coprime_natAbs_of_isCoprime (a := 2 * k + 1) (b := 4) ⟨1 - 2 * k, k ^ 2, by ring⟩)

theorem den_eq_six_of_cos_two_pi_mul_rat_eq_half {r : ℚ}
    (h : Real.cos (2 * Real.pi * r) = 1 / 2) : r.den = 6 := by
  rw [← Real.cos_pi_div_three, Real.cos_eq_cos_iff] at h
  obtain ⟨k, hk | hk⟩ := h
  · have : (r : ℝ) = ((1 - 6 * k : ℤ) : ℝ) / ((6 : ℕ) : ℝ) :=
      rat_eq_of_two_pi_mul_eq (by push_cast; linear_combination -hk)
    exact den_eq_of_coprime_den this (by norm_num)
      (coprime_natAbs_of_isCoprime (a := 1 - 6 * k) (b := 6) ⟨1, k, by ring⟩)
  · have : (r : ℝ) = ((6 * k - 1 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) :=
      rat_eq_of_two_pi_mul_eq (by push_cast; linear_combination hk)
    exact den_eq_of_coprime_den this (by norm_num)
      (coprime_natAbs_of_isCoprime (a := 6 * k - 1) (b := 6) ⟨-1, k, by ring⟩)

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  ring

theorem den_eq_three_of_cos_two_pi_mul_rat_eq_neg_half {r : ℚ}
    (h : Real.cos (2 * Real.pi * r) = -1 / 2) : r.den = 3 := by
  rw [← cos_two_pi_div_three, Real.cos_eq_cos_iff] at h
  obtain ⟨k, hk | hk⟩ := h
  · have : (r : ℝ) = ((1 - 3 * k : ℤ) : ℝ) / ((3 : ℕ) : ℝ) :=
      rat_eq_of_two_pi_mul_eq (by push_cast; linear_combination -hk)
    exact den_eq_of_coprime_den this (by norm_num)
      (coprime_natAbs_of_isCoprime (a := 1 - 3 * k) (b := 3) ⟨1, k, by ring⟩)
  · have : (r : ℝ) = ((3 * k - 1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ) :=
      rat_eq_of_two_pi_mul_eq (by push_cast; linear_combination hk)
    exact den_eq_of_coprime_den this (by norm_num)
      (coprime_natAbs_of_isCoprime (a := 3 * k - 1) (b := 3) ⟨-1, k, by ring⟩)

/-- **Niven's theorem**: `cos (2πr)` is irrational unless the denominator of `r` is one of
`1, 2, 3, 4, 6`. -/
theorem irrational_cos_two_pi_mul_rat {r : ℚ} (h1 : r.den ≠ 1) (h2 : r.den ≠ 2) (h3 : r.den ≠ 3)
    (h4 : r.den ≠ 4) (h6 : r.den ≠ 6) : Irrational (Real.cos (2 * Real.pi * r)) := by
  rintro ⟨s, hs⟩
  rcases cos_two_pi_mul_rat_mem_of_rat r hs.symm with rfl | rfl | rfl | rfl | rfl
  · exact h2 (den_eq_two_of_cos_two_pi_mul_rat_eq_neg_one (by rw [← hs]; push_cast; ring))
  · exact h3 (den_eq_three_of_cos_two_pi_mul_rat_eq_neg_half (by rw [← hs]; push_cast; ring))
  · exact h4 (den_eq_four_of_cos_two_pi_mul_rat_eq_zero (by rw [← hs]; push_cast; ring))
  · exact h6 (den_eq_six_of_cos_two_pi_mul_rat_eq_half (by rw [← hs]; push_cast; ring))
  · exact h1 (den_eq_one_of_cos_two_pi_mul_rat_eq_one (by rw [← hs]; push_cast; ring))

/-- `cos (2πr)` is irrational for a rational `0 < r < 1/6` (its denominator exceeds `6`). -/
theorem irrational_cos_two_pi_mul_rat_of_small {r : ℚ} (h0 : 0 < r) (h1 : r < 1 / 6) :
    Irrational (Real.cos (2 * Real.pi * r)) := by
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hnum : (1 : ℚ) ≤ r.num := by exact_mod_cast Rat.num_pos.mpr h0
  have hle : (1 : ℚ) / r.den ≤ r := by
    rw [div_le_iff₀ hden, Rat.mul_den_eq_num]
    exact hnum
  have key : ∀ k : ℕ, 0 < k → k ≤ 6 → r.den ≠ k := by
    intro k hk0 hk6 h
    rw [h] at hle
    have hk : (0 : ℚ) < k := by exact_mod_cast hk0
    have hk' : (k : ℚ) ≤ 6 := by exact_mod_cast hk6
    have : (1 : ℚ) / 6 ≤ 1 / k := one_div_le_one_div_of_le hk hk'
    linarith
  exact irrational_cos_two_pi_mul_rat (key 1 (by norm_num) (by norm_num))
    (key 2 (by norm_num) (by norm_num)) (key 3 (by norm_num) (by norm_num))
    (key 4 (by norm_num) (by norm_num)) (key 6 (by norm_num) (by norm_num))

/-! ### The values at the five denominators -/

/-- A prime dividing the denominator does not divide the numerator. -/
theorem not_dvd_num_of_prime_dvd_den {r : ℚ} {p : ℕ} (hp : p.Prime) (h : p ∣ r.den) :
    ¬ (p : ℤ) ∣ r.num := by
  intro hd
  have h1 : Nat.Coprime r.num.natAbs p := Nat.Coprime.coprime_dvd_right h r.reduced
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp] at h1
  exact h1 (Int.natCast_dvd.mp hd)

theorem cos_two_pi_mul_rat_of_den_eq_one {r : ℚ} (h : r.den = 1) :
    Real.cos (2 * Real.pi * r) = 1 := by
  rw [← Rat.coe_int_num_of_den_eq_one h, Rat.cast_intCast,
    show 2 * Real.pi * (r.num : ℝ) = r.num * (2 * Real.pi) by ring]
  exact Real.cos_int_mul_two_pi r.num

theorem cos_two_pi_mul_rat_of_den_eq_two {r : ℚ} (h : r.den = 2) :
    Real.cos (2 * Real.pi * r) = -1 := by
  have h2 := not_dvd_num_of_prime_dvd_den Nat.prime_two (by rw [h])
  obtain ⟨k, hk⟩ : ∃ k : ℤ, r.num = 2 * k + 1 := ⟨r.num / 2, by omega⟩
  rw [Rat.cast_def, h, hk, show 2 * Real.pi * (((2 * k + 1 : ℤ) : ℝ) / ((2 : ℕ) : ℝ))
    = k * (2 * Real.pi) + Real.pi by push_cast; ring]
  exact Real.cos_int_mul_two_pi_add_pi k

theorem cos_two_pi_mul_rat_of_den_eq_four {r : ℚ} (h : r.den = 4) :
    Real.cos (2 * Real.pi * r) = 0 := by
  have h2 := not_dvd_num_of_prime_dvd_den Nat.prime_two (by rw [h]; norm_num)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, r.num = 2 * k + 1 := ⟨r.num / 2, by omega⟩
  rw [Real.cos_eq_zero_iff]
  refine ⟨k, ?_⟩
  rw [Rat.cast_def, h, hk]
  push_cast
  ring

theorem cos_two_pi_mul_rat_of_den_eq_three {r : ℚ} (h : r.den = 3) :
    Real.cos (2 * Real.pi * r) = -1 / 2 := by
  have h3 := not_dvd_num_of_prime_dvd_den Nat.prime_three (by rw [h])
  rcases (by omega : r.num % 3 = 1 ∨ r.num % 3 = 2) with hm | hm
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, r.num = 3 * k + 1 := ⟨r.num / 3, by omega⟩
    rw [Rat.cast_def, h, hk, show 2 * Real.pi * (((3 * k + 1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ))
      = 2 * Real.pi / 3 + k * (2 * Real.pi) by push_cast; ring, Real.cos_add_int_mul_two_pi,
      cos_two_pi_div_three]
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, r.num = 3 * k + 2 := ⟨r.num / 3, by omega⟩
    rw [Rat.cast_def, h, hk, show 2 * Real.pi * (((3 * k + 2 : ℤ) : ℝ) / ((3 : ℕ) : ℝ))
      = Real.pi / 3 + Real.pi + k * (2 * Real.pi) by push_cast; ring, Real.cos_add_int_mul_two_pi,
      Real.cos_add_pi, Real.cos_pi_div_three]
    ring

theorem cos_two_pi_mul_rat_of_den_eq_six {r : ℚ} (h : r.den = 6) :
    Real.cos (2 * Real.pi * r) = 1 / 2 := by
  have h2 := not_dvd_num_of_prime_dvd_den Nat.prime_two (by rw [h]; norm_num)
  have h3 := not_dvd_num_of_prime_dvd_den Nat.prime_three (by rw [h]; norm_num)
  rcases (by omega : r.num % 6 = 1 ∨ r.num % 6 = 5) with hm | hm
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, r.num = 6 * k + 1 := ⟨r.num / 6, by omega⟩
    rw [Rat.cast_def, h, hk, show 2 * Real.pi * (((6 * k + 1 : ℤ) : ℝ) / ((6 : ℕ) : ℝ))
      = Real.pi / 3 + k * (2 * Real.pi) by push_cast; ring, Real.cos_add_int_mul_two_pi,
      Real.cos_pi_div_three]
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, r.num = 6 * k + 5 := ⟨r.num / 6, by omega⟩
    rw [Rat.cast_def, h, hk, show 2 * Real.pi * (((6 * k + 5 : ℤ) : ℝ) / ((6 : ℕ) : ℝ))
      = 2 * Real.pi - Real.pi / 3 + k * (2 * Real.pi) by push_cast; ring,
      Real.cos_add_int_mul_two_pi, Real.cos_two_pi_sub, Real.cos_pi_div_three]

end Azurite
