/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Size

/-!
# The 2-adic valuation of `r^a − 1`

`padicValNat_two_pow_sub_one_le`: `v₂(r^a − 1) + 3 ≤ 2 size r + size a` for an odd `r ≥ 3` and
`a ≥ 1` (lifting the exponent).  `not_eq_pow_of_twoAdic_gt`: hence a number `n` with
`v₂(n − 1) + 3 > 2 size b + size (size n)` is not a power of `b ≥ 2` — the cheap test that lets
`AzNat.checkedLogBase` reject `m 2^t + 1` for a huge `t` without computing any power.
-/

namespace Azurite

/-- `v₂(m) < size m`. -/
theorem padicValNat_two_lt_size {m : ℕ} (hm : m ≠ 0) : padicValNat 2 m < m.size := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (pow_padicValNat_dvd (p := 2) (n := m))
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h (Nat.lt_size_self m))

/-- **Lifting the exponent**: `v₂(r^a − 1) + 3 ≤ 2 size r + size a` for an odd `r ≥ 3` and
`a ≥ 1` (from `v₂(r^(2a) − 1) = v₂(r + 1) + v₂(r − 1) + v₂(2a) − 1` and
`r^(2a) − 1 = (r^a − 1)(r^a + 1)` with `r^a + 1` even). -/
theorem padicValNat_two_pow_sub_one_le {r a : ℕ} (hr : Odd r) (hr3 : 3 ≤ r) (ha : 1 ≤ a) :
    padicValNat 2 (r ^ a - 1) + 3 ≤ 2 * r.size + a.size := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr1 : 1 < r := by omega
  have hra : 1 < r ^ a := Nat.one_lt_pow (by omega) hr1
  have hra0 : r ^ a - 1 ≠ 0 := by omega
  have hra1 : r ^ a + 1 ≠ 0 := by omega
  have hlte := padicValNat.pow_two_sub_pow (x := r) (y := 1) hr1
    (even_iff_two_dvd.mp (Nat.Odd.sub_odd hr odd_one))
    (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hr) (n := 2 * a) (by omega)
    (even_two_mul a)
  rw [one_pow] at hlte
  have hfac : r ^ (2 * a) - 1 = (r ^ a + 1) * (r ^ a - 1) := by
    have := Nat.sq_sub_sq (r ^ a) 1
    rwa [one_pow, ← pow_mul, mul_comm a 2] at this
  rw [hfac, padicValNat.mul hra1 hra0, padicValNat.mul two_ne_zero (by omega),
    padicValNat_self] at hlte
  have h1 : 1 ≤ padicValNat 2 (r ^ a + 1) :=
    one_le_padicValNat_of_dvd hra1 (even_iff_two_dvd.mp (hr.pow.add_one))
  have h2 := padicValNat_two_lt_size (show r + 1 ≠ 0 by omega)
  have h3 := padicValNat_two_lt_size (show r - 1 ≠ 0 by omega)
  have h4 := padicValNat_two_lt_size (show a ≠ 0 by omega)
  have h5 : (r + 1).size ≤ r.size + 1 := by
    rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self r
    omega
  have h6 : (r - 1).size ≤ r.size := Nat.size_le_size (by omega)
  omega

/-- A number `n` with `v₂(n − 1) + 3 > 2 size b + size (size n)` is not a power of `b ≥ 2`. -/
theorem not_eq_pow_of_twoAdic_gt {b n : ℕ} (hb : 2 ≤ b)
    (h : 2 * b.size + n.size.size < padicValNat 2 (n - 1) + 3) (e : ℕ) : n ≠ b ^ e := by
  rintro rfl
  have hbs : 2 ≤ b.size := Nat.lt_size.mpr (by simpa using hb)
  rcases Nat.eq_zero_or_pos e with rfl | he
  · have h0 : padicValNat 2 (b ^ 0 - 1) = 0 := by simp
    rw [h0] at h
    omega
  rcases Nat.even_or_odd b with hev | hodd
  · have hodd' : ¬ 2 ∣ b ^ e - 1 := by
      have h1 : 2 ∣ b ^ e := dvd_pow (even_iff_two_dvd.mp hev) (by omega)
      have h2 : 1 ≤ b ^ e := Nat.one_le_pow _ _ (by omega)
      omega
    rw [padicValNat.eq_zero_of_not_dvd hodd'] at h
    omega
  · have hb3 : 3 ≤ b := by
      rcases hodd with ⟨k, hk⟩
      omega
    have hlte := padicValNat_two_pow_sub_one_le hodd hb3 he
    have he2 : e < (b ^ e).size := by
      rw [Nat.lt_size]
      exact Nat.pow_le_pow_left hb e
    have hes : e.size ≤ (b ^ e).size.size := Nat.size_le_size he2.le
    omega

/-- The 2-adic valuation and the bit length of a power: if `n = b^e` then `v₂(n) = e v₂(b)` and
`(size b − 1) e < size n ≤ size b · e + 1`.  Hence `n` is not a power of `b ≥ 2` when `b` is odd
and `n` even, or when `b` is even and `e = v₂(n)/v₂(b)` is not an integer or does not fit the
bit lengths — the cheap test that rejects `m 2^t` for a huge `t` and a base that is not a power
of two. -/
theorem not_eq_pow_of_valuation {b n : ℕ} (hb : 2 ≤ b)
    (h : (padicValNat 2 b = 0 ∧ padicValNat 2 n ≠ 0) ∨
      (padicValNat 2 b ≠ 0 ∧ (padicValNat 2 n % padicValNat 2 b ≠ 0 ∨
        ¬ ((b.size - 1) * (padicValNat 2 n / padicValNat 2 b) < n.size ∧
          n.size ≤ b.size * (padicValNat 2 n / padicValNat 2 b) + 1))))
    (e : ℕ) : n ≠ b ^ e := by
  rintro rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hval : padicValNat 2 (b ^ e) = e * padicValNat 2 b :=
    padicValNat.pow b e
  rw [hval] at h
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, mul_zero] at h1
    exact h1 rfl
  · rcases h1 with h1 | h1
    · exact h1 (Nat.mul_mod_left e _)
    · apply h1
      rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero h0)]
      have hbs : 0 < b.size := Nat.size_pos.mpr (by omega)
      constructor
      · rw [Nat.lt_size, pow_mul]
        exact Nat.pow_le_pow_left (Nat.lt_size.mp (by omega)) e
      · rw [Nat.size_le, pow_succ, pow_mul]
        have h2 : b ^ e ≤ (2 ^ b.size) ^ e := Nat.pow_le_pow_left (Nat.lt_size_self b).le e
        have h3 : 0 < (2 ^ b.size) ^ e := by positivity
        omega

end Azurite
