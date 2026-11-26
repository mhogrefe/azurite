/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Size
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic

/-!
# Perfect powers: the theory behind the 2-adic detector

D. J. Bernstein, *Detecting perfect powers in essentially linear time*, Math. Comp. 67 (1998),
1253–1283, §21–§22 (the 2-adic variant).  This file has the number theory on `ℕ`; the
algorithm on `AzNat` is in `Azurite/AzNat/PerfectPower.lean`.

* `IsPerfectPower n`: `n = x ^ k` for some `x` and some `k > 1` (so `0` and `1` are).
* `IsPerfectPower.exists_prime`: a perfect power is a `p`-th power for a prime `p`;
  `exponent_lt_size`: for `n ≥ 2` that prime is below the bit length of `n`.
* `root_lt_two_pow`: a `k`-th root of a number of `f` bits is below `2 ^ ⌈f/k⌉`.
* **`odd_root_unique`** (the content of Lemma 21.5, case 2): for odd `k`, an odd `x < 2 ^ b` is
  determined by `x ^ k mod 2 ^ b`.  So a number `r < 2 ^ b` with `r ^ k ≡ n (mod 2 ^ b)` is
  the only possible `k`-th root of an odd `n < 2 ^ (b k)`, however `r` was found.
* **`pow_eq_two_pow_mul_iff`** (§22, "if `n` has a prime divisor, find its order"): for odd
  `m`, `2 ^ e * m` is a `p`-th power exactly when `p ∣ e` and `m` is a `p`-th power.
-/

namespace Azurite

/-- `n` is a perfect power: `n = x ^ k` with `k > 1`. -/
def IsPerfectPower (n : ℕ) : Prop := ∃ x k, 1 < k ∧ x ^ k = n

theorem isPerfectPower_zero : IsPerfectPower 0 := ⟨0, 2, by norm_num, by norm_num⟩

theorem isPerfectPower_one : IsPerfectPower 1 := ⟨1, 2, by norm_num, by norm_num⟩

/-- A perfect power is a `p`-th power for some prime `p`. -/
theorem IsPerfectPower.exists_prime {n : ℕ} (h : IsPerfectPower n) :
    ∃ p, p.Prime ∧ ∃ x, x ^ p = n := by
  obtain ⟨x, k, hk, rfl⟩ := h
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
  obtain ⟨j, rfl⟩ := hpk
  exact ⟨p, hp, x ^ j, by rw [← pow_mul, mul_comm]⟩

/-- A `p`-th power with `p` prime is a perfect power. -/
theorem isPerfectPower_of_prime_pow {p x : ℕ} (hp : p.Prime) : IsPerfectPower (x ^ p) :=
  ⟨x, p, hp.one_lt, rfl⟩

/-- For `n ≥ 2`, an exponent `p` with `x ^ p = n` is below the bit length of `n`. -/
theorem exponent_lt_size {n p x : ℕ} (hn : 2 ≤ n) (h : x ^ p = n) : p < n.size := by
  have hx : 2 ≤ x := by
    by_contra hc
    have : x = 0 ∨ x = 1 := by omega
    rcases this with rfl | rfl
    · rcases Nat.eq_zero_or_pos p with rfl | hp0
      · simp at h; omega
      · rw [zero_pow (by omega)] at h; omega
    · simp at h; omega
  have h1 : 2 ^ p ≤ n := h ▸ Nat.pow_le_pow_left hx p
  have h2 : n < 2 ^ n.size := Nat.lt_size_self n
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h1 h2)

/-- A `k`-th root of a number below `2 ^ f` is below `2 ^ ⌈f/k⌉`. -/
theorem root_lt_two_pow {x k f : ℕ} (hk : 0 < k) (h : x ^ k < 2 ^ f) :
    x < 2 ^ ((f + k - 1) / k) := by
  by_contra hc
  push Not at hc
  have h1 : (2 ^ ((f + k - 1) / k)) ^ k ≤ x ^ k := Nat.pow_le_pow_left hc k
  rw [← pow_mul] at h1
  have h2 : f ≤ (f + k - 1) / k * k := by
    have h4 := Nat.div_add_mod (f + k - 1) k
    have h5 := Nat.mod_lt (f + k - 1) hk
    rw [mul_comm] at h4
    omega
  have h3 : 2 ^ f ≤ 2 ^ ((f + k - 1) / k * k) := Nat.pow_le_pow_right (by norm_num) h2
  omega

/-- For odd `r`, `x` the cofactor `∑ rⁱ x^(k−1−i)` of `r − x` in `r ^ k − x ^ k` has the parity
of `k`. -/
private theorem odd_geom_sum {r x : ℤ} (hr : Odd r) (hx : Odd x) {k : ℕ} (hk : Odd k) :
    Odd (∑ i ∈ Finset.range k, r ^ i * x ^ (k - 1 - i)) := by
  rw [Int.odd_iff, Finset.sum_int_mod]
  have : ∀ i ∈ Finset.range k, r ^ i * x ^ (k - 1 - i) % 2 = 1 := fun i _ =>
    Int.odd_iff.1 ((hr.pow).mul (hx.pow))
  rw [Finset.sum_congr rfl this]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact Int.odd_iff.1 (by exact_mod_cast hk)

/-- **An odd `k`-th root is determined by the low bits of its power**: for odd `k` and odd
`x`, if `r, x < 2 ^ b` and `r ^ k ≡ x ^ k (mod 2 ^ b)` then `r = x`. -/
theorem odd_root_unique {b k r x : ℕ} (hk : Odd k) (hx : Odd x) (hr : r < 2 ^ b)
    (hxb : x < 2 ^ b) (h : r ^ k % 2 ^ b = x ^ k % 2 ^ b) : r = x := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp at hxb
      subst hxb
      exact absurd hx (by decide)
    · exact hb
  -- `r` is odd
  have hro : Odd r := by
    have h2 : r ^ k % 2 = x ^ k % 2 := by
      have hd : (2 : ℕ) ∣ 2 ^ b := dvd_pow_self 2 (by omega)
      rw [← Nat.mod_mod_of_dvd (r ^ k) hd, h, Nat.mod_mod_of_dvd _ hd]
    have : Odd (r ^ k) := by
      rw [Nat.odd_iff, h2, ← Nat.odd_iff]
      exact hx.pow
    exact (Nat.odd_pow_iff (by rintro rfl; exact absurd hk (by decide))).1 this
  -- `2 ^ b ∣ (r − x) c` with `c` odd
  have hdvd : ((2 : ℤ) ^ b) ∣ (r : ℤ) ^ k - (x : ℤ) ^ k := by
    have := (Nat.modEq_iff_dvd (n := 2 ^ b) (a := x ^ k) (b := r ^ k)).1 h.symm
    simpa using this
  rw [← Commute.mul_geom_sum₂ (Commute.all _ _)] at hdvd
  have hc : Odd (∑ i ∈ Finset.range k, (r : ℤ) ^ i * (x : ℤ) ^ (k - 1 - i)) :=
    odd_geom_sum (by exact_mod_cast hro) (by exact_mod_cast hx) hk
  have hcop : IsCoprime ((2 : ℤ) ^ b)
      (∑ i ∈ Finset.range k, (r : ℤ) ^ i * (x : ℤ) ^ (k - 1 - i)) :=
    (Int.isCoprime_two_left.mpr hc).pow_left
  have hd : ((2 : ℤ) ^ b) ∣ (r : ℤ) - x := (IsCoprime.dvd_mul_right_iff hcop).mp hdvd
  have hlt : |(r : ℤ) - x| < 2 ^ b := by
    rw [abs_lt]
    constructor
    · have : (x : ℤ) < 2 ^ b := by exact_mod_cast hxb
      have : (0 : ℤ) ≤ r := Int.natCast_nonneg r
      linarith
    · have : (r : ℤ) < 2 ^ b := by exact_mod_cast hr
      have : (0 : ℤ) ≤ x := Int.natCast_nonneg x
      linarith
  have h0 : (r : ℤ) - x = 0 := Int.eq_zero_of_abs_lt_dvd hd hlt
  have : (r : ℤ) = x := by linarith
  exact_mod_cast this

/-- **Powers of two times an odd number**: for odd `m` and `p > 0`, `2 ^ e * m` is a `p`-th
power exactly when `p ∣ e` and `m` is a `p`-th power. -/
theorem pow_eq_two_pow_mul_iff {e m p : ℕ} (hm : Odd m) (hp : 0 < p) :
    (∃ x, x ^ p = 2 ^ e * m) ↔ p ∣ e ∧ ∃ r, r ^ p = m := by
  have hm2 : ¬ 2 ∣ m := by
    rw [Nat.two_dvd_ne_zero]
    exact Nat.odd_iff.1 hm
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hx
      have : 2 ^ e * m ≠ 0 := Nat.mul_ne_zero (by positivity) (by rintro rfl; simp at hm2)
      exact this hx.symm
    obtain ⟨a, r, hr, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hx0
    have hr2 : ¬ 2 ∣ r ^ p := by
      rw [Nat.two_dvd_ne_zero]
      exact Nat.odd_iff.1 hr.pow
    rw [mul_pow, ← pow_mul] at hx
    have hv := congrArg (padicValNat 2) hx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hr0 : r ^ p ≠ 0 := by rintro h0; rw [h0] at hr2; simp at hr2
    rw [padicValNat.mul (by positivity) hr0,
      padicValNat.mul (by positivity) (by rintro rfl; simp at hm2), padicValNat.prime_pow,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hr2,
      padicValNat.eq_zero_of_not_dvd hm2] at hv
    simp only [add_zero] at hv
    refine ⟨⟨a, by rw [← hv, mul_comm]⟩, r, ?_⟩
    rw [hv] at hx
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hx
  · rintro ⟨⟨j, rfl⟩, r, rfl⟩
    exact ⟨2 ^ j * r, by rw [mul_pow, ← pow_mul, mul_comm j p]⟩

end Azurite
