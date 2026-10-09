/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.DoubleFactorial
import Azurite.AzNat.Equiv.Factorial
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
## Correctness of `AzNat.doubleFactorial`

`toNat_doubleFactorial : (doubleFactorial n).toNat = n‼` (Mathlib's `Nat.doubleFactorial`).
Even `n = 2k`: `(2k)‼ = 2^k k!` (`Nat.doubleFactorial_two_mul`).  Odd `n = 2k + 1`:
`n! = n‼ · 2^k · k!` (`Nat.factorial_eq_mul_doubleFactorial`), so `v_p(n‼) = v_p(n!) − v_p(k!)`
for every odd prime, `n‼` is odd, and `n‼ = ∏ p^{v_p(n‼)}` over the odd primes up to `n`.
-/

namespace Azurite.AzNat

open scoped Nat

theorem odd_doubleFactorial_odd : ∀ k : ℕ, Odd (2 * k + 1)‼
  | 0 => by decide
  | k + 1 => by
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, Nat.doubleFactorial_add_two]
    exact Odd.mul (⟨k + 1, by ring⟩ : Odd (2 * k + 1 + 2)) (odd_doubleFactorial_odd k)

/-- **Correctness of `doubleFactorial`.** -/
theorem toNat_doubleFactorial (n : ℕ) : (doubleFactorial n).toNat = n‼ := by
  unfold doubleFactorial
  split_ifs with heven
  · rw [toNat_hShiftLeft, Nat.shiftLeft_eq, toNat_factorial]
    have : n = 2 * (n / 2) := by omega
    conv_rhs => rw [this, Nat.doubleFactorial_two_mul]
    ring
  · set k := n / 2 with hk
    have hn : n = 2 * k + 1 := by omega
    have hfac : n.factorial = n‼ * (2 ^ k * k.factorial) := by
      rw [hn, Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
    have hodd : Odd n‼ := hn ▸ odd_doubleFactorial_odd k
    have hne : n‼ ≠ 0 := hodd.pos.ne'
    have hnot2 : ¬ 2 ∣ n‼ := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    have hdvd : n‼ ∣ n.factorial := ⟨_, hfac⟩
    have hexp : ∀ p, Nat.Prime p → p ≠ 2 →
        legendreExp p n n - legendreExp p k k = padicValNat p n‼ := by
      intro p hp hp2
      have := Fact.mk hp
      have hp2k : ¬ p ∣ 2 ^ k := fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      rw [legendreExp_eq_padicValNat p n hp, legendreExp_eq_padicValNat p k hp, hfac,
        padicValNat.mul hne (by positivity),
        padicValNat.mul (by positivity) (Nat.factorial_ne_zero k),
        padicValNat.eq_zero_of_not_dvd hp2k]
      omega
    unfold oddDoubleFactorialExps
    rw [← hk, toNat_prodPrimePowers _ _ _ (oddPrimes_nodup n) (fun p hp =>
        lt_of_le_of_lt (Nat.sub_le _ _)
          (lt_of_le_of_lt (legendreExp_le p ((mem_oddPrimes n p).mp hp).1.two_le n n)
            (Nat.lt_pow_succ_log_self (by norm_num) n))),
      toFinset_oddPrimes]
    have hfull := Nat.prod_pow_prime_padicValNat n‼ hne (n.factorial + 1)
      (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.factorial_pos n) hdvd))
    have hsub : ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ^ padicValNat p n‼
        = ∏ p ∈ (Finset.range (n.factorial + 1)).filter Nat.Prime, p ^ padicValNat p n‼ := by
      apply Finset.prod_subset
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact ⟨by have := Nat.self_le_factorial n; omega, hp.2⟩
      · intro p hp hnp
        simp only [Finset.mem_filter, Finset.mem_range] at hp hnp
        have hgt : n < p := by
          by_contra h
          exact hnp ⟨by omega, hp.2⟩
        rw [padicValNat.eq_zero_of_not_dvd (fun h =>
          absurd ((Nat.Prime.dvd_factorial hp.2).mp (h.trans hdvd)) (by omega)), pow_zero]
    rw [← hsub] at hfull
    calc ∏ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).erase 2,
          p ^ (legendreExp p n n - legendreExp p k k)
        = ∏ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).erase 2, p ^ padicValNat p n‼ := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [hexp p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
            (Finset.mem_erase.mp hp).1]
      _ = ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ^ padicValNat p n‼ :=
          Finset.prod_erase _ (by rw [padicValNat.eq_zero_of_not_dvd hnot2, pow_zero])
      _ = n‼ := hfull

end Azurite.AzNat
