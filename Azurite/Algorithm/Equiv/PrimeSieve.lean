/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Correctness of the bitpacked sieve of Eratosthenes**:
  `(primeSieve n).testBit j = true ↔ Nat.Prime j` for `j ≤ n`
  (`primeSieve_testBit_iff`), hence `p ∈ primesUpTo n ↔ p.Prime ∧ p ≤ n`
  (`mem_primesUpTo`, with sortedness `primesUpTo_sorted`), and every
  cached small prime is prime (`smallPrimes_prime`).

  The loop invariant (`SieveInv n d s`, holding after all rounds
  `d' < d`): bit `j ≤ n` is set iff `2 ≤ j` and every prime `p < d`
  dividing `j` has `p² > j`.  From the invariant, bit `d` at `d`'s own
  turn is set exactly when `d` is prime (a composite `d`'s least prime
  factor `p` has `p² ≤ d` and was processed earlier), which justifies the
  prime-only marking; and when a composite `d` is skipped, its multiples
  `≥ d²` were already cleared by its least prime factor — so the
  invariant advances either way (`sieveInv_step`).  At exit (`d² > n`)
  the invariant IS primality (`sieveInv_final`): a composite `j ≤ n` has
  its least prime factor `p` with `p² ≤ j < d²`, and a prime `j`'s only
  prime divisor is `j` itself, with `j < j²`.

  Bit accesses transport along `testBit_eq_toNat_testBit` and
  `toNat_clearBit`/`toNat_lowMask` to `Nat.testBit` arithmetic.
-/
import Azurite.Algorithm.PrimeSieve
import Azurite.AzNat.Equiv.TestBit
import Azurite.AzNat.Equiv.ClearBit
import Azurite.AzNat.Equiv.LowMask
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Prime.Basic

namespace Azurite

namespace AzNat

/-- Pointwise `clearBit`: bit `j` survives iff it survived before and
`j ≠ i`. -/
theorem testBit_clearBit (s : AzNat) (i j : Nat) :
    (s.clearBit i).testBit j = (s.testBit j && !(j == i)) := by
  rw [testBit_eq_toNat_testBit, toNat_clearBit, Nat.testBit_ldiff,
    testBit_eq_toNat_testBit]
  congr 1
  rcases eq_or_ne j i with rfl | hne
  · simp [Nat.testBit_two_pow_self]
  · simp [Nat.testBit_two_pow_of_ne (fun h => hne h.symm), hne]

/-- Pointwise `lowMask`: bit `j` of `2^k − 1` is set iff `j < k`. -/
theorem testBit_lowMask (k j : Nat) :
    (lowMask k).testBit j = decide (j < k) := by
  rw [testBit_eq_toNat_testBit, toNat_lowMask, Nat.testBit_two_pow_sub_one]

/-- What `sieveMark` clears: exactly the in-range progression
`j₀, j₀ + d, …` (given enough fuel and `d > 0`). -/
theorem testBit_sieveMark {n d : Nat} (hd : 0 < d) :
    ∀ (fuel j₀ : Nat) (s : AzNat) (k : Nat), n + 1 ≤ j₀ + fuel * d →
      ((sieveMark n d fuel j₀ s).testBit k = true ↔
        s.testBit k = true ∧ ¬(j₀ ≤ k ∧ k ≤ n ∧ d ∣ k - j₀)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j₀ s k hfuel
    rw [sieveMark]
    exact ⟨fun h => ⟨h, fun ⟨h1, h2, _⟩ => by omega⟩, fun h => h.1⟩
  | succ fuel ih =>
    intro j₀ s k hfuel
    rw [sieveMark]
    by_cases hj : j₀ ≤ n
    · rw [ite_eq_left hj,
        ih (j₀ + d) (s.clearBit j₀) k (by
          have h1 : j₀ + (fuel + 1) * d = j₀ + d + fuel * d := by ring
          omega),
        testBit_clearBit, Bool.and_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne]
      constructor
      · rintro ⟨⟨hs, hne⟩, hnot⟩
        refine ⟨hs, ?_⟩
        rintro ⟨h1, h2, hdvd⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact hne rfl
        · have hge : d ≤ k - j₀ := Nat.le_of_dvd (by omega) hdvd
          obtain ⟨t, ht⟩ := hdvd
          match t, ht with
          | 0, ht => omega
          | t' + 1, ht =>
            have ht' : k - j₀ = d * t' + d := by rw [ht]; ring
            exact hnot ⟨by omega, h2, ⟨t', by omega⟩⟩
      · rintro ⟨hs, hnot⟩
        refine ⟨⟨hs, ?_⟩, ?_⟩
        · rintro rfl
          exact hnot ⟨le_rfl, hj, by simp⟩
        · rintro ⟨h1, h2, hdvd⟩
          obtain ⟨t, ht⟩ := hdvd
          refine hnot ⟨by omega, h2, ⟨t + 1, ?_⟩⟩
          have h3 : d * (t + 1) = d * t + d := by ring
          omega
    · rw [ite_eq_right hj]
      exact ⟨fun h => ⟨h, fun ⟨h1, h2, _⟩ => by omega⟩, fun h => h.1⟩

/-- The sieve-loop invariant after all rounds `d' < d`: bit `j ≤ n` is
set iff `2 ≤ j` and no prime `p < d` divides `j` with `p² ≤ j`. -/
def SieveInv (n d : Nat) (s : AzNat) : Prop :=
  ∀ j, j ≤ n →
    (s.testBit j = true ↔
      2 ≤ j ∧ ∀ p, Nat.Prime p → p < d → p ∣ j → j < p * p)

/-- At exit (`d² > n`) the invariant is primality. -/
theorem sieveInv_final {n d : Nat} {s : AzNat} (hd2 : n < d * d)
    (hinv : SieveInv n d s) :
    ∀ j, j ≤ n → (s.testBit j = true ↔ Nat.Prime j) := by
  intro j hj
  rw [hinv j hj]
  constructor
  · rintro ⟨h2, hcond⟩
    by_contra hnp
    have hp := Nat.minFac_prime (n := j) (by omega)
    have hdvd := Nat.minFac_dvd j
    have hsq : j.minFac ^ 2 ≤ j := Nat.minFac_sq_le_self (by omega) hnp
    rw [pow_two] at hsq
    have hlt : j.minFac < d := by
      by_contra hge
      have := Nat.mul_le_mul (by omega : d ≤ j.minFac)
        (by omega : d ≤ j.minFac)
      omega
    have := hcond _ hp hlt hdvd
    omega
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro p hpp hplt hpdvd
    obtain rfl : p = j := (Nat.prime_dvd_prime_iff_eq hpp hp).mp hpdvd
    have h2 := hpp.two_le
    calc p < p * 2 := by omega
      _ ≤ p * p := Nat.mul_le_mul_left p h2

/-- One round advances the invariant, whether or not `d`'s bit is set. -/
theorem sieveInv_step {n d : Nat} {s : AzNat} (h2 : 2 ≤ d)
    (hdn : d * d ≤ n) (hinv : SieveInv n d s) :
    SieveInv n (d + 1)
      (if s.testBit d then sieveMark n d (n + 1) (d * d) s else s) := by
  have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
  have hdle : d ≤ n := by omega
  by_cases hbit : s.testBit d = true
  · -- `d`'s bit is set: by the invariant, `d` is prime
    have hdprime : Nat.Prime d := by
      obtain ⟨-, hcond⟩ := (hinv d hdle).mp hbit
      by_contra hnp
      have hp := Nat.minFac_prime (n := d) (by omega)
      have hsq : d.minFac ^ 2 ≤ d := Nat.minFac_sq_le_self (by omega) hnp
      rw [pow_two] at hsq
      have hple : d.minFac ≤ d := Nat.minFac_le (by omega)
      have hpne : d.minFac ≠ d := fun h => hnp (h ▸ hp)
      have := hcond _ hp (by omega) (Nat.minFac_dvd d)
      omega
    rw [ite_eq_left hbit]
    intro j hj
    rw [testBit_sieveMark (by omega) (n + 1) (d * d) s j
      (by
        have h1 : n + 1 ≤ (n + 1) * d :=
          Nat.le_mul_of_pos_right (n + 1) (by omega)
        omega),
      hinv j hj]
    constructor
    · rintro ⟨⟨hj2, hcond⟩, hnot⟩
      refine ⟨hj2, ?_⟩
      intro p hpp hplt hpdvd
      rcases Nat.lt_or_ge p d with hlt | hge
      · exact hcond p hpp hlt hpdvd
      · obtain rfl : p = d := by omega
        by_contra hjge
        refine hnot ⟨by omega, hj, ?_⟩
        obtain ⟨t, ht⟩ := hpdvd
        match t, ht with
        | 0, ht => omega
        | t' + 1, ht =>
          have htge : p ≤ t' + 1 := by
            by_contra htlt
            have hmul : p * (t' + 1) < p * p :=
              mul_lt_mul_of_pos_left (by omega) (by omega)
            omega
          obtain ⟨u, hu⟩ : ∃ u, t' + 1 = u + p := ⟨t' + 1 - p, by omega⟩
          refine ⟨u, ?_⟩
          have h3 : j = p * u + p * p := by rw [ht, hu]; ring
          omega
    · rintro ⟨hj2, hcond⟩
      refine ⟨⟨hj2, fun p hpp hplt => hcond p hpp (by omega)⟩, ?_⟩
      rintro ⟨hge, -, hdvd⟩
      obtain ⟨t, ht⟩ := hdvd
      have hddvd : d ∣ j := by
        refine ⟨t + d, ?_⟩
        have h3 : d * (t + d) = d * t + d * d := by ring
        omega
      have := hcond d hdprime (by omega) hddvd
      omega
  · -- `d`'s bit is clear: `d` is composite, and adds nothing to the
    -- condition
    have hnd : ¬ Nat.Prime d := by
      intro hp
      apply hbit
      rw [hinv d hdle]
      refine ⟨h2, ?_⟩
      intro p hpp hplt hpdvd
      obtain rfl : p = d := (Nat.prime_dvd_prime_iff_eq hpp hp).mp hpdvd
      omega
    rw [ite_eq_right hbit]
    intro j hj
    rw [hinv j hj]
    constructor
    · rintro ⟨hj2, hcond⟩
      refine ⟨hj2, ?_⟩
      intro p hpp hplt hpdvd
      rcases Nat.lt_or_ge p d with h | h
      · exact hcond p hpp h hpdvd
      · obtain rfl : p = d := by omega
        exact absurd hpp hnd
    · rintro ⟨hj2, hcond⟩
      exact ⟨hj2, fun p hpp hplt => hcond p hpp (by omega)⟩

/-- The loop turns the invariant into primality. -/
theorem testBit_sieveLoop (n : Nat) :
    ∀ (fuel d : Nat) (s : AzNat), 2 ≤ d → n + 1 ≤ d + fuel →
      SieveInv n d s →
      ∀ j, j ≤ n →
        ((sieveLoop n fuel d s).testBit j = true ↔ Nat.Prime j) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d s h2 hfuel hinv j hj
    rw [sieveLoop]
    refine sieveInv_final ?_ hinv j hj
    have : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
    omega
  | succ fuel ih =>
    intro d s h2 hfuel hinv j hj
    rw [sieveLoop]
    by_cases hdd : d * d ≤ n
    · rw [ite_eq_left hdd]
      exact ih (d + 1) _ (by omega) (by omega)
        (sieveInv_step h2 hdd hinv) j hj
    · rw [ite_eq_right hdd]
      exact sieveInv_final (by omega) hinv j hj

/-- **Correctness of the sieve**: bit `j` is set iff `j` is prime. -/
theorem primeSieve_testBit_iff {n j : Nat} (hj : j ≤ n) :
    ((primeSieve n).testBit j = true) ↔ Nat.Prime j := by
  refine testBit_sieveLoop n (n + 1) 2 _ le_rfl (by omega) ?_ j hj
  intro k hk
  rw [testBit_clearBit, testBit_clearBit, testBit_lowMask]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hklt, hk0⟩, hk1⟩
    refine ⟨by omega, ?_⟩
    intro p hpp hplt _
    have := hpp.two_le
    omega
  · rintro ⟨hk2, -⟩
    exact ⟨⟨by omega, by omega⟩, by omega⟩

/-- **The extracted list is exactly the primes up to `n`.** -/
theorem mem_primesUpTo {n p : Nat} :
    p ∈ primesUpTo n ↔ Nat.Prime p ∧ p ≤ n := by
  simp only [primesUpTo, Array.mem_filter, Array.mem_range]
  constructor
  · rintro ⟨hlt, hbit⟩
    exact ⟨(primeSieve_testBit_iff (by omega)).mp hbit, by omega⟩
  · rintro ⟨hp, hle⟩
    exact ⟨by omega, (primeSieve_testBit_iff hle).mpr hp⟩

/-- The extracted list is strictly increasing. -/
theorem primesUpTo_sorted (n : Nat) :
    (primesUpTo n).toList.Pairwise (· < ·) := by
  rw [primesUpTo]
  rw [Array.toList_filter, Array.toList_range]
  exact List.pairwise_lt_range.filter _

set_option maxRecDepth 4096 in
/-- **Every cached small prime is prime.** -/
theorem smallPrimes_prime : ∀ p ∈ smallPrimes, Nat.Prime p := by decide

end AzNat

end Azurite
