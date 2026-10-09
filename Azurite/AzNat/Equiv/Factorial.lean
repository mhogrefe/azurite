/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Factorial
import Azurite.Algorithm.Equiv.PrimeSieve
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.SumProduct
import Azurite.AzNat.Equiv.Square.Dispatch
import Azurite.AzNat.Equiv.ShiftLeft
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-!
## Correctness of `AzNat.factorial`

`toNat_factorial : (factorial n).toNat = n.factorial`.  Legendre's exponent loop computes
`padicValNat p n!` (`legendreExp_eq_padicValNat`, via Mathlib's `padicValNat_factorial`); the
balanced product computes the list product (`toNat_product`); Horner's rule on the bits
gives `∏ p ^ (Σ_i bit_i(e_p) 2^i)` (`toNat_hornerPow`, `sum_testBit`), which is
`∏ p ^ e_p` over the odd primes up to `n`; and `n!` is that product times `2^{e_2}` by
`Nat.prod_pow_prime_padicValNat`, restricted to the primes up to `n` (the others have exponent
`0`).
-/

namespace Azurite.AzNat

/-! ### Legendre's exponent -/

theorem legendreExp_eq (p : ℕ) : ∀ (fuel m : ℕ),
    legendreExp p fuel m = ∑ i ∈ Finset.range fuel, m / p ^ (i + 1) := by
  intro fuel
  induction fuel with
  | zero => intro m; simp [legendreExp]
  | succ fuel ih =>
    intro m
    rw [legendreExp, Finset.sum_range_succ', ih]
    have hdiv : ∀ i, m / p ^ (i + 1 + 1) = m / p / p ^ (i + 1) := fun i => by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
    rw [Finset.sum_congr rfl (fun i _ => hdiv i), zero_add, pow_one]
    split_ifs with h0
    · rw [h0, Finset.sum_eq_zero (fun i _ => Nat.zero_div _)]
    · rw [add_comm]

theorem legendreExp_le (p : ℕ) (hp : 2 ≤ p) : ∀ (fuel m : ℕ), legendreExp p fuel m ≤ m := by
  intro fuel
  induction fuel with
  | zero => intro m; simp [legendreExp]
  | succ fuel ih =>
    intro m
    rw [legendreExp]
    split_ifs with h
    · exact Nat.zero_le _
    · have h1 := ih (m / p)
      have h2 : m / p ≤ m / 2 := Nat.div_le_div_left hp (by norm_num)
      omega

theorem legendreExp_eq_padicValNat (p n : ℕ) (hp : Nat.Prime p) :
    legendreExp p n n = padicValNat p n.factorial := by
  have := Fact.mk hp
  rw [padicValNat_factorial (b := n + 1)
      (lt_of_le_of_lt (Nat.log_le_self p n) (Nat.lt_succ_self n)),
    legendreExp_eq p, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl (fun i _ => by rw [add_comm])

/-! ### Horner's rule on the exponent bits -/

theorem toNat_hornerPow (P : ℕ → AzNat) : ∀ (B : ℕ) (acc : AzNat),
    (hornerPow P B acc).toNat
      = acc.toNat ^ (2 ^ B) * ∏ i ∈ Finset.range B, (P i).toNat ^ (2 ^ i) := by
  intro B
  induction B with
  | zero => intro acc; simp [hornerPow]
  | succ B ih =>
    intro acc
    rw [hornerPow, ih, toNat_mul, toNat_square, Finset.prod_range_succ, mul_pow, ← pow_mul,
      pow_succ]
    ring

/-- The binary expansion: `Σ_{i < B} bit_i(e) 2^i = e` for `e < 2^B`. -/
theorem sum_testBit : ∀ (B e : ℕ), e < 2 ^ B →
    ∑ i ∈ Finset.range B, (if e.testBit i then 1 else 0) * 2 ^ i = e := by
  intro B
  induction B with
  | zero => intro e h; simp at h; simp [h]
  | succ B ih =>
    intro e h
    have h2 : e / 2 < 2 ^ B := by rw [pow_succ] at h; omega
    rw [Finset.sum_range_succ']
    simp only [Nat.testBit_succ, pow_succ, pow_zero, mul_one]
    have hsum : ∑ i ∈ Finset.range B, (if (e / 2).testBit i then 1 else 0) * (2 ^ i * 2)
        = 2 * ∑ i ∈ Finset.range B, (if (e / 2).testBit i then 1 else 0) * 2 ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum, ih (e / 2) h2, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one e with h0 | h1
    · simp [h0]; omega
    · simp [h1]; omega

theorem prod_primesWithBit (ps : List ℕ) (e : ℕ → ℕ) (j : ℕ) :
    ((primesWithBit (ps.map fun p => (p, e p)) j).map toNat).prod
      = (ps.map fun p => p ^ (if (e p).testBit j then 1 else 0)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    unfold primesWithBit at ih ⊢
    rw [List.map_cons, List.filterMap_cons, List.map_cons, List.prod_cons]
    dsimp only
    split_ifs with h
    · rw [List.map_cons, List.prod_cons, toNat_ofNat, ih, pow_one]
    · rw [ih, pow_zero, one_mul]

/-! ### The factorial -/

/-- **Horner's rule assembles the prime powers**: for a duplicate-free list of primes `ps` with
exponents `e p < 2^B`, `prodPrimePowers` computes `∏ p ^ e p`. -/
theorem toNat_prodPrimePowers (ps : List ℕ) (e : ℕ → ℕ) (B : ℕ) (hnd : ps.Nodup)
    (hB : ∀ p ∈ ps, e p < 2 ^ B) :
    (prodPrimePowers (ps.map fun p => (p, e p)) B).toNat = ∏ p ∈ ps.toFinset, p ^ e p := by
  unfold prodPrimePowers
  rw [toNat_hornerPow, toNat_one, one_pow, one_mul]
  have hP : ∀ i, (product (primesWithBit (ps.map fun p => (p, e p)) i)).toNat
      = ∏ p ∈ ps.toFinset, p ^ (if (e p).testBit i then 1 else 0) := fun i => by
    rw [toNat_product, prod_primesWithBit, ← List.prod_toFinset _ hnd]
  have h1 : ∏ i ∈ Finset.range B, (product (primesWithBit (ps.map fun p => (p, e p)) i)).toNat
        ^ 2 ^ i
      = ∏ i ∈ Finset.range B, ∏ p ∈ ps.toFinset,
          p ^ ((if (e p).testBit i then 1 else 0) * 2 ^ i) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [hP i, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p _
    rw [← pow_mul]
  rw [h1, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Finset.prod_pow_eq_pow_sum, sum_testBit B (e p) (hB p (List.mem_toFinset.mp hp))]

/-- The odd primes up to `n`, as a duplicate-free list and as a `Finset`. -/
theorem oddPrimes_nodup (n : ℕ) : ((primesUpTo n).toList.filter (· ≠ 2)).Nodup :=
  ((primesUpTo_sorted n).imp ne_of_lt).filter _

theorem mem_oddPrimes (n p : ℕ) :
    p ∈ (primesUpTo n).toList.filter (· ≠ 2) ↔ Nat.Prime p ∧ p ≤ n ∧ p ≠ 2 := by
  rw [List.mem_filter, ← Array.mem_def, mem_primesUpTo]
  simp [and_assoc]

theorem toFinset_oddPrimes (n : ℕ) :
    ((primesUpTo n).toList.filter (· ≠ 2)).toFinset
      = ((Finset.range (n + 1)).filter Nat.Prime).erase 2 := by
  ext p
  simp only [List.mem_toFinset, mem_oddPrimes, Finset.mem_erase, Finset.mem_filter,
    Finset.mem_range, Nat.lt_succ_iff]
  tauto

/-- The odd part is `∏ p ^ v_p(n!)` over the odd primes up to `n`. -/
theorem toNat_factorialOdd (n : ℕ) :
    (factorialOdd n).toNat
      = ∏ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).erase 2,
          p ^ padicValNat p n.factorial := by
  unfold factorialOdd oddPrimeExps
  rw [toNat_prodPrimePowers _ _ _ (oddPrimes_nodup n) (fun p hp =>
      lt_of_le_of_lt (legendreExp_le p ((mem_oddPrimes n p).mp hp).1.two_le n n)
        (Nat.lt_pow_succ_log_self (by norm_num) n)),
    toFinset_oddPrimes]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : Nat.Prime p := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
  rw [legendreExp_eq_padicValNat p n hprime]

/-- **Correctness of `factorial`.** -/
theorem toNat_factorial (n : ℕ) : (factorial n).toNat = n.factorial := by
  unfold factorial
  rw [toNat_hShiftLeft, Nat.shiftLeft_eq, toNat_factorialOdd,
    legendreExp_eq_padicValNat 2 n Nat.prime_two]
  have hfull := Nat.prod_pow_prime_padicValNat n.factorial (Nat.factorial_ne_zero n)
    (n.factorial + 1) (Nat.lt_succ_self _)
  have hsub : ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, p ^ padicValNat p n.factorial
      = ∏ p ∈ (Finset.range (n.factorial + 1)).filter Nat.Prime,
          p ^ padicValNat p n.factorial := by
    apply Finset.prod_subset
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      exact ⟨by have := Nat.self_le_factorial n; omega, hp.2⟩
    · intro p hp hnp
      simp only [Finset.mem_filter, Finset.mem_range] at hp hnp
      have hgt : n < p := by
        by_contra h
        exact hnp ⟨by omega, hp.2⟩
      rw [padicValNat.eq_zero_of_not_dvd (by rw [Nat.Prime.dvd_factorial hp.2]; omega), pow_zero]
  rw [← hsub] at hfull
  conv_rhs => rw [← hfull]
  by_cases h2 : 2 ≤ n
  · have hmem : 2 ∈ (Finset.range (n + 1)).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_two⟩
    rw [← Finset.mul_prod_erase _ _ hmem, mul_comm]
  · have hnot : 2 ∉ (Finset.range (n + 1)).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [Finset.erase_eq_of_notMem hnot,
      padicValNat.eq_zero_of_not_dvd (by rw [Nat.Prime.dvd_factorial Nat.prime_two]; omega),
      pow_zero, mul_one]

end Azurite.AzNat
