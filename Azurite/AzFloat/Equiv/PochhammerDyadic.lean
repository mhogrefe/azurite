/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.ZivSpec
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factors

/-!
# Rising factorials of rationals that are not dyadic

For a rational `q = a/d` in lowest terms whose denominator is not a power of two:

* `not_isDyadic_prod_rat`: `(q)ₙ = ∏_{j<n} (q + j)` is not dyadic for `n ≥ 1`.  It is
  `∏ (a + j d) / dⁿ`, and an odd prime `p ∣ d` divides no `a + j d`, so the `p`-adic valuation
  is negative.
* `not_isDyadic_inv_prod_rat`: `1 / (q)ₙ` is not dyadic for `n ≥ 4`.  Now the valuation at
  the primes of `d` is positive, and the obstruction is an odd prime of the numerator of some
  factor: the four integers `a, a + d, a + 2d, a + 3d` are not all `±` powers of two
  (`exists_odd_prime_dvd_num_add`) — two of them of the same index parity are odd, and two
  odd `±` powers of two differ by at most `2 < 2d`.  (Three are not enough:
  `(−2/3)(1/3)(4/3) = −8/27`.)

A number that is not dyadic is no rounding boundary, so Ziv's loop on a convergent bracket
terminates there: these are the certificates of `pochhammerRat` and of the reciprocal branch
of `genPochhammerRat`.
-/

namespace Azurite.AzFloat

open Finset

/-- A rational with a negative valuation at an odd prime is not dyadic. -/
theorem not_isDyadic_of_padicValRat_neg {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {R : ℚ}
    (h : padicValRat p R < 0) : ¬ IsDyadic ((R : ℚ) : ℝ) := by
  rintro ⟨m, k, hmk⟩
  have hR : R = (m : ℚ) * (2 : ℚ) ^ k := by
    have : ((R : ℚ) : ℝ) = (((m : ℚ) * (2 : ℚ) ^ k : ℚ) : ℝ) := by
      push_cast
      exact hmk
    exact Rat.cast_injective this
  have hm : (m : ℚ) ≠ 0 := by
    intro h0
    rw [hR, h0, zero_mul, padicValRat.zero] at h
    exact lt_irrefl _ h
  have h2 : padicValRat p (2 : ℚ) = 0 := by
    have : padicValRat p ((2 : ℕ) : ℚ) = padicValNat p 2 := padicValRat.of_nat
    rw [show ((2 : ℕ) : ℚ) = 2 by norm_num] at this
    rw [this, padicValNat.eq_zero_of_not_dvd fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)]
    rfl
  rw [hR, padicValRat.mul hm (zpow_ne_zero _ (by norm_num)), padicValRat.zpow, h2, mul_zero,
    add_zero, padicValRat.of_int] at h
  have : (0 : ℤ) ≤ (padicValInt p m : ℤ) := Int.natCast_nonneg _
  omega

/-- `q + i = (a + i d) / d`. -/
theorem rat_add_nat_eq (q : ℚ) (i : ℕ) :
    q + (i : ℚ) = ((q.num + i * q.den : ℤ) : ℚ) / (q.den : ℚ) := by
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [eq_div_iff hd0]
  push_cast
  rw [add_mul, Rat.mul_den_eq_num]

/-- A prime of the denominator divides no `a + i d`. -/
theorem not_dvd_num_add (q : ℚ) {p : ℕ} (hp : p.Prime) (hpd : p ∣ q.den) (i : ℕ) :
    ¬ (p : ℤ) ∣ q.num + i * q.den := by
  intro h
  have h1 : (p : ℤ) ∣ (i : ℤ) * (q.den : ℤ) :=
    Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hpd) _
  have h2 : (p : ℤ) ∣ q.num := (dvd_add_left h1).mp h
  have h3 : p ∣ q.num.natAbs := Int.natCast_dvd.mp h2
  have h4 := Nat.dvd_gcd h3 hpd
  rw [q.reduced.gcd_eq_one] at h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

/-- No `a + i d` vanishes when `d ≠ 1`. -/
theorem num_add_ne_zero (q : ℚ) (hd : q.den ≠ 1) (i : ℕ) : q.num + i * q.den ≠ 0 := by
  intro h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  exact not_dvd_num_add q hp hpd i (h ▸ dvd_zero _)

/-- **`(q)ₙ` is not dyadic** for a rational `q` whose denominator is not a power of two,
`n ≥ 1`. -/
theorem not_isDyadic_prod_rat (q : ℚ) (hd : ¬ ∃ k : ℕ, q.den = 2 ^ k) {n : ℕ} (hn : n ≠ 0) :
    ¬ IsDyadic (∏ j ∈ range n, (((q : ℚ) : ℝ) + j)) := by
  rcases q.den.eq_two_pow_or_exists_odd_prime_and_dvd with h | ⟨p, hp, hpd, hodd⟩
  · exact absurd h hd
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h => by rw [h] at hodd; exact absurd hodd (by decide)
  have hd1 : q.den ≠ 1 := fun h => hd ⟨0, by rw [h, pow_zero]⟩
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hfac : ∀ i : ℕ, q + (i : ℚ) ≠ 0 ∧ padicValRat p (q + (i : ℚ)) ≤ -1 := by
    intro i
    have ht := num_add_ne_zero q hd1 i
    have ht' : ((q.num + i * q.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast ht
    rw [rat_add_nat_eq]
    refine ⟨div_ne_zero ht' hd0, ?_⟩
    rw [padicValRat.div ht' hd0, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd (not_dvd_num_add q hp hpd i), padicValRat.of_nat]
    have := one_le_padicValNat_of_dvd q.den_nz hpd
    omega
  have hprod : ∀ m : ℕ, ∏ j ∈ range m, (q + (j : ℚ)) ≠ 0 ∧
      padicValRat p (∏ j ∈ range m, (q + (j : ℚ))) ≤ -(m : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := hfac m
      rw [prod_range_succ]
      refine ⟨mul_ne_zero h1 h3, ?_⟩
      rw [padicValRat.mul h1 h3]
      push_cast
      omega
  have hcast : (∏ j ∈ range n, (((q : ℚ) : ℝ) + j))
      = ((∏ j ∈ range n, (q + (j : ℚ)) : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [hcast]
  refine not_isDyadic_of_padicValRat_neg hp2 ?_
  have := (hprod n).2
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  omega

/-- An odd integer that is `±` a power of two is `±1`. -/
theorem int_eq_one_or_of_natAbs_pow {t : ℤ} {k : ℕ} (h : t.natAbs = 2 ^ k)
    (hodd : t % 2 = 1) : t = 1 ∨ t = -1 := by
  cases k with
  | zero =>
    rw [pow_zero] at h
    omega
  | succ k =>
    rw [pow_succ] at h
    omega

/-- **One of `a, a + d, a + 2d, a + 3d` has an odd prime factor** when `d` is not a power of
two and `gcd (a, d) = 1`. -/
theorem exists_odd_prime_dvd_num_add (q : ℚ) (hd : ¬ ∃ k : ℕ, q.den = 2 ^ k) :
    ∃ (i : ℕ) (l : ℕ), i < 4 ∧ l.Prime ∧ l ≠ 2 ∧ (l : ℤ) ∣ q.num + i * q.den := by
  by_contra hcon
  have hpow : ∀ i : ℕ, i < 4 → ∃ k : ℕ, (q.num + i * q.den).natAbs = 2 ^ k := by
    intro i hi
    rcases (q.num + i * q.den).natAbs.eq_two_pow_or_exists_odd_prime_and_dvd with
      h | ⟨l, hl, hld, hodd⟩
    · exact h
    · refine absurd ⟨i, l, hi, hl, ?_, Int.natCast_dvd.mpr hld⟩ hcon
      intro h
      rw [h] at hodd
      exact absurd hodd (by decide)
  have hd1 : q.den ≠ 1 := fun h => hd ⟨0, by rw [h, pow_zero]⟩
  have hd2 : q.den ≠ 2 := fun h => hd ⟨1, by rw [h, pow_one]⟩
  have hd0 := q.den_nz
  obtain ⟨d, hdd⟩ : ∃ d : ℕ, d = q.den := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = q.num := ⟨_, rfl⟩
  rw [← hdd, ← ha] at hpow
  rw [← hdd] at hd0 hd1 hd2
  obtain ⟨k0, h0⟩ := hpow 0 (by norm_num)
  obtain ⟨k1, h1⟩ := hpow 1 (by norm_num)
  obtain ⟨k2, h2⟩ := hpow 2 (by norm_num)
  obtain ⟨k3, h3⟩ := hpow 3 (by norm_num)
  push_cast at h0 h1 h2 h3
  rw [zero_mul, add_zero] at h0
  rw [one_mul] at h1
  by_cases hdo : d % 2 = 1
  · by_cases hao : a % 2 = 1
    · have e0 := int_eq_one_or_of_natAbs_pow h0 hao
      have e2 := int_eq_one_or_of_natAbs_pow h2 (by omega)
      omega
    · have e1 := int_eq_one_or_of_natAbs_pow h1 (by omega)
      have e3 := int_eq_one_or_of_natAbs_pow h3 (by omega)
      omega
  · have hao : a % 2 = 1 := by
      by_contra hae
      have h2a : 2 ∣ a.natAbs := by omega
      have h2d : 2 ∣ d := by omega
      have := Nat.dvd_gcd h2a h2d
      rw [ha, hdd, q.reduced.gcd_eq_one] at this
      omega
    have e0 := int_eq_one_or_of_natAbs_pow h0 hao
    have e1 := int_eq_one_or_of_natAbs_pow h1 (by omega)
    omega

/-- **`1 / (q)ₙ` is not dyadic** for a rational `q` whose denominator is not a power of two,
`n ≥ 4`. -/
theorem not_isDyadic_inv_prod_rat (q : ℚ) (hd : ¬ ∃ k : ℕ, q.den = 2 ^ k) {n : ℕ}
    (hn : 4 ≤ n) : ¬ IsDyadic (∏ j ∈ range n, (((q : ℚ) : ℝ) + j))⁻¹ := by
  obtain ⟨i₀, l, hi₀, hl, hl2, hld⟩ := exists_odd_prime_dvd_num_add q hd
  have : Fact l.Prime := ⟨hl⟩
  have hd1 : q.den ≠ 1 := fun h => hd ⟨0, by rw [h, pow_zero]⟩
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hlden : ¬ l ∣ q.den := fun h => not_dvd_num_add q hl h i₀ hld
  have hvd : padicValRat l (q.den : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hlden]
    rfl
  have hfac : ∀ i : ℕ, q + (i : ℚ) ≠ 0 ∧ 0 ≤ padicValRat l (q + (i : ℚ)) ∧
      (i = i₀ → 1 ≤ padicValRat l (q + (i : ℚ))) := by
    intro i
    have ht := num_add_ne_zero q hd1 i
    have ht' : ((q.num + i * q.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast ht
    rw [rat_add_nat_eq]
    refine ⟨div_ne_zero ht' hd0, ?_, ?_⟩
    · rw [padicValRat.div ht' hd0, padicValRat.of_int, hvd, sub_zero]
      exact Int.natCast_nonneg _
    · intro hi
      rw [padicValRat.div ht' hd0, padicValRat.of_int, hvd, sub_zero]
      have h1 : (l : ℤ) ^ 1 ∣ q.num + i * q.den := by rw [pow_one, hi]; exact hld
      have := (padicValInt_dvd_iff 1 (q.num + i * q.den)).mp h1
      rcases this with h0 | h0
      · exact absurd h0 ht
      · exact_mod_cast h0
  have hprod : ∀ m : ℕ, ∏ j ∈ range m, (q + (j : ℚ)) ≠ 0 ∧
      0 ≤ padicValRat l (∏ j ∈ range m, (q + (j : ℚ))) ∧
      (i₀ < m → 1 ≤ padicValRat l (∏ j ∈ range m, (q + (j : ℚ)))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨h4, h5, h6⟩ := hfac m
      rw [prod_range_succ]
      refine ⟨mul_ne_zero h1 h4, ?_, ?_⟩
      · rw [padicValRat.mul h1 h4]
        omega
      · intro hlt
        rw [padicValRat.mul h1 h4]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
        · have := h3 h
          omega
        · have := h6 h.symm
          omega
  have hcast : (∏ j ∈ range n, (((q : ℚ) : ℝ) + j))⁻¹
      = (((∏ j ∈ range n, (q + (j : ℚ)))⁻¹ : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [hcast]
  refine not_isDyadic_of_padicValRat_neg hl2 ?_
  rw [padicValRat.inv]
  have := (hprod n).2.2 (by omega)
  omega

end Azurite.AzFloat
