/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.RisingFallingFactorial
import Azurite.AzNat.Equiv.Factorial
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.SumProduct

/-!
## Correctness of `AzNat.risingFactorial` and `AzNat.fallingFactorial`

`toNat_risingFactorial : (risingFactorial x k).toNat = x.toNat.ascFactorial k` and
`toNat_fallingFactorial : (fallingFactorial x k).toNat = x.toNat.descFactorial k` (Mathlib's
`Nat.ascFactorial`, `Nat.descFactorial`).  The quotient of factorials is assembled from the
differences of `p`-adic valuations, which the Legendre exponents compute
(`toNat_factorialQuotient`); the direct regime is the list product; the falling factorial is
`Nat.add_descFactorial_eq_ascFactorial'`.
-/

namespace Azurite.AzNat

open scoped Nat

/-- **Correctness of `factorialQuotient`**: `a! / b!` for `b ≤ a`. -/
theorem toNat_factorialQuotient (a b : ℕ) (h : b ≤ a) :
    (factorialQuotient a b).toNat = a ! / b ! := by
  set Q := a ! / b ! with hQ
  have hfac : a ! = Q * b ! := (Nat.div_mul_cancel (Nat.factorial_dvd_factorial h)).symm
  have hQne : Q ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hfac; exact Nat.factorial_ne_zero a hfac
  have hdvd : Q ∣ a ! := ⟨b !, hfac⟩
  have hexp : ∀ p, Nat.Prime p →
      legendreExp p a a - legendreExp p b b = padicValNat p Q := by
    intro p hp
    have := Fact.mk hp
    rw [legendreExp_eq_padicValNat p a hp, legendreExp_eq_padicValNat p b hp, hfac,
      padicValNat.mul hQne (Nat.factorial_ne_zero b)]
    omega
  unfold factorialQuotient factorialQuotientExps
  rw [toNat_hShiftLeft, Nat.shiftLeft_eq, hexp 2 Nat.prime_two,
    toNat_prodPrimePowers _ _ _ (oddPrimes_nodup a) (fun p hp =>
      lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_of_le_of_lt (legendreExp_le p ((mem_oddPrimes a p).mp hp).1.two_le a a)
          (Nat.lt_pow_succ_log_self (by norm_num) a))),
    toFinset_oddPrimes]
  rw [Finset.prod_congr rfl (fun p hp => by
    rw [hexp p (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2])]
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

/-- The product of `x, x + 1, …, x + k − 1` as a list is the rising factorial. -/
theorem prod_map_range_add (n : ℕ) : ∀ k : ℕ,
    (((List.range k).map fun i => n + i)).prod = n.ascFactorial k
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, prod_map_range_add n k, Nat.ascFactorial_succ, mul_comm]

/-- A one-limb value is its low word. -/
theorem toUInt64_toNat_of_size_le_one (x : AzNat) (h : x.limbs.size ≤ 1) :
    x.toUInt64.toNat = x.toNat := by
  rw [← toNat_mod_2_64_eq_toUInt64_toNat]
  apply Nat.mod_eq_of_lt
  calc x.toNat < 2 ^ (64 * x.limbs.size) := toNat_lt_pow x
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Correctness of `risingFactorial`.** -/
theorem toNat_risingFactorial (x : AzNat) (k : ℕ) :
    (risingFactorial x k).toNat = x.toNat.ascFactorial k := by
  unfold risingFactorial
  split_ifs with hk hx hsmall
  · rw [hk, Nat.ascFactorial_zero, toNat_one]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hx, toNat_zero, Nat.zero_ascFactorial]
  · obtain ⟨hsize, hle⟩ := hsmall
    rw [toUInt64_toNat_of_size_le_one x hsize] at hle ⊢
    have hpos : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (toNat_injective (h0.trans toNat_zero.symm)) hx
      · exact h0
    rw [toNat_factorialQuotient _ _ (by omega), Nat.ascFactorial_eq_div' _ _ hpos]
  · rw [toNat_product, List.map_map]
    have : (toNat ∘ fun i => x + ofNat i) = fun i => x.toNat + i := by
      funext i
      simp only [Function.comp, toNat_add, toNat_ofNat]
    rw [this, prod_map_range_add]

/-- **Correctness of `fallingFactorial`.** -/
theorem toNat_fallingFactorial (x : AzNat) (k : ℕ) :
    (fallingFactorial x k).toNat = x.toNat.descFactorial k := by
  unfold fallingFactorial
  rw [toNat_risingFactorial, toNat_sub, toNat_add, toNat_one, toNat_ofNat]
  by_cases h : k ≤ x.toNat
  · have := Nat.add_descFactorial_eq_ascFactorial' (x.toNat + 1 - k) k
    rw [show x.toNat + 1 - k + k - 1 = x.toNat by omega] at this
    exact this.symm
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show x.toNat + 1 - (j + 1) = 0 by omega, Nat.zero_ascFactorial,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]

end Azurite.AzNat
