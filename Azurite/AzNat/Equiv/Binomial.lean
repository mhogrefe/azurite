/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Binomial
import Azurite.AzNat.Equiv.RisingFallingFactorial
import Azurite.AzNat.Equiv.Div.DivMod
import Mathlib.Data.Nat.Choose.Basic

/-!
## Correctness of `AzNat.binomial`

`toNat_binomial : (binomial n k).toNat = n.toNat.choose k` (Mathlib's `Nat.choose`).  The
prime regime is assembled from the differences of `p`-adic valuations, which the Legendre
exponents compute, through `toNat_primePowers_of_dvd_factorial` (any divisor of `n!` is the
product of its prime powers over the primes up to `n`); the thin regime is
`Nat.choose_eq_descFactorial_div_factorial`; the symmetry is `Nat.choose_symm`.
-/

namespace Azurite.AzNat

open scoped Nat

/-- A nonzero divisor `Q` of `a!` is the product of `p^{v_p(Q)}` over the primes up to `a`,
assembled with the power of two as a shift. -/
theorem toNat_primePowers_of_dvd_factorial (a Q : ℕ) (hQne : Q ≠ 0) (hdvd : Q ∣ a !)
    (e : ℕ → ℕ) (he : ∀ p, Nat.Prime p → e p = padicValNat p Q) (B : ℕ)
    (hB : ∀ p ∈ (primesUpTo a).toList.filter (· ≠ 2), e p < 2 ^ B) :
    (prodPrimePowers (((primesUpTo a).toList.filter (· ≠ 2)).map fun p => (p, e p)) B
      <<< e 2).toNat = Q := by
  rw [toNat_hShiftLeft, Nat.shiftLeft_eq, he 2 Nat.prime_two,
    toNat_prodPrimePowers _ _ _ (oddPrimes_nodup a) hB, toFinset_oddPrimes]
  rw [Finset.prod_congr rfl (fun p hp => by
    rw [he p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2])]
  have hfull := Nat.prod_pow_prime_padicValNat Q hQne (a ! + 1)
    (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.factorial_pos a) hdvd))
  have hsub : ∏ p ∈ (Finset.range (a + 1)).filter Nat.Prime, p ^ padicValNat p Q
      = ∏ p ∈ (Finset.range (a ! + 1)).filter Nat.Prime, p ^ padicValNat p Q := by
    apply Finset.prod_subset
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      exact ⟨by have := Nat.self_le_factorial a; omega, hp.2⟩
    · intro p hp hnp
      simp only [Finset.mem_filter, Finset.mem_range] at hp hnp
      have hgt : a < p := by
        by_contra h
        exact hnp ⟨by omega, hp.2⟩
      rw [padicValNat.eq_zero_of_not_dvd (fun h =>
        absurd ((Nat.Prime.dvd_factorial hp.2).mp (h.trans hdvd)) (by omega)), pow_zero]
  rw [← hsub] at hfull
  conv_rhs => rw [← hfull]
  by_cases h2 : 2 ≤ a
  · have hmem : 2 ∈ (Finset.range (a + 1)).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_two⟩
    rw [← Finset.mul_prod_erase _ _ hmem, mul_comm]
  · have hnot : 2 ∉ (Finset.range (a + 1)).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [Finset.erase_eq_of_notMem hnot,
      padicValNat.eq_zero_of_not_dvd (fun hd =>
        absurd ((Nat.Prime.dvd_factorial Nat.prime_two).mp (hd.trans hdvd)) (by omega)),
      pow_zero, mul_one]

/-- **Correctness of the prime regime.** -/
theorem toNat_binomialPrime (n k : ℕ) (h : k ≤ n) : (binomialPrime n k).toNat = n.choose k := by
  have hfac : n ! = n.choose k * k ! * (n - k)! := (Nat.choose_mul_factorial_mul_factorial h).symm
  have hQne : n.choose k ≠ 0 := (Nat.choose_pos h).ne'
  have hdvd : n.choose k ∣ n ! := ⟨k ! * (n - k)!, by rw [hfac]; ring⟩
  unfold binomialPrime binomialExps
  apply toNat_primePowers_of_dvd_factorial n _ hQne hdvd
  · intro p hp
    have := Fact.mk hp
    rw [legendreExp_eq_padicValNat p n hp, legendreExp_eq_padicValNat p k hp,
      legendreExp_eq_padicValNat p (n - k) hp, hfac,
      padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
      padicValNat.mul hQne (Nat.factorial_ne_zero _)]
    omega
  · intro p hp
    exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt (Nat.sub_le _ _)
      (lt_of_le_of_lt (legendreExp_le p ((mem_oddPrimes n p).mp hp).1.two_le n n)
        (Nat.lt_pow_succ_log_self (by norm_num) n)))

/-- **Correctness of the thin regime.** -/
theorem toNat_binomialProduct (n : AzNat) (k : ℕ) :
    (binomialProduct n k).toNat = n.toNat.choose k := by
  unfold binomialProduct
  rw [toNat_div, toNat_fallingFactorial, toNat_factorial, Nat.choose_eq_descFactorial_div_factorial]

/-- **Correctness of `binomial`.** -/
theorem toNat_binomial (n : AzNat) (k : ℕ) : (binomial n k).toNat = n.toNat.choose k := by
  unfold binomial
  dsimp only
  split_ifs with hsize hlt hj hdense
  · rw [toUInt64_toNat_of_size_le_one n hsize] at hlt
    rw [toNat_zero, Nat.choose_eq_zero_of_lt hlt]
  · rw [toUInt64_toNat_of_size_le_one n hsize] at hj hlt
    rw [toNat_one]
    rcases Nat.min_eq_zero_iff.mp hj with h0 | h0
    · rw [h0, Nat.choose_zero_right]
    · rw [show k = n.toNat by omega, Nat.choose_self]
  · rw [toUInt64_toNat_of_size_le_one n hsize] at hj hdense hlt ⊢
    have hle : min k (n.toNat - k) ≤ n.toNat := by omega
    rw [toNat_binomialPrime _ _ hle]
    rcases Nat.le_total k (n.toNat - k) with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, Nat.choose_symm (by omega)]
  · rw [toUInt64_toNat_of_size_le_one n hsize] at hj hdense hlt ⊢
    rw [toNat_binomialProduct]
    rcases Nat.le_total k (n.toNat - k) with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, Nat.choose_symm (by omega)]
  · exact toNat_binomialProduct n k

end Azurite.AzNat
