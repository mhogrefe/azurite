/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.IsPrimeWord
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Correctness of the one-word primality test

**`isPrimeWord_eq_some`**: `isPrimeWord n = some b → (b = true ↔ Nat.Prime n.toNat)`.
-/

namespace Azurite.AzNat

/-- The loop: for an odd `n < 2^32` whose prime factors are all at least the odd `d ≤ 65537`,
a verdict is right. -/
theorem trialOddWord_spec (n : UInt64) (hn : n.toNat < 2 ^ 32) (hodd : n.toNat % 2 = 1)
    (hn2 : 2 ≤ n.toNat) : ∀ (fuel : ℕ) (d : UInt64) (b : Bool), 3 ≤ d.toNat →
    d.toNat ≤ 65537 → d.toNat % 2 = 1 → (∀ p : ℕ, p.Prime → p ∣ n.toNat → d.toNat ≤ p) →
    trialOddWord n fuel d = some b → (b = true ↔ Nat.Prime n.toNat) := by
  intro fuel
  induction fuel with
  | zero => intro d b _ _ _ _ h; simp [trialOddWord] at h
  | succ fuel ih =>
    intro d b hd3 hd hdodd hmin h
    rw [trialOddWord] at h
    have hsq : (d * d).toNat = d.toNat * d.toNat := by
      rw [UInt64.toNat_mul]
      exact Nat.mod_eq_of_lt (by nlinarith)
    split_ifs at h with h1 h2
    · -- `n < d²`: prime
      cases h
      rw [UInt64.lt_iff_toNat_lt, hsq] at h1
      simp only [true_iff]
      by_contra hnp
      have h3 := Nat.minFac_sq_le_self (by omega) hnp
      have h4 := hmin _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)
      nlinarith
    · -- `d ∣ n`, `d² ≤ n`: composite
      cases h
      rw [UInt64.lt_iff_toNat_lt, hsq] at h1
      have hdvd : d.toNat ∣ n.toNat := by
        have := congrArg UInt64.toNat h2
        rw [UInt64.toNat_mod] at this
        exact Nat.dvd_of_mod_eq_zero this
      simp only [Bool.false_eq_true, false_iff]
      intro hp
      have := (Nat.prime_dvd_prime_iff_eq (Nat.minFac_prime (by omega : d.toNat ≠ 1)) hp).1
        ((Nat.minFac_dvd _).trans hdvd)
      have hle := Nat.minFac_le (by omega : 0 < d.toNat)
      nlinarith
    · -- next divisor
      rw [UInt64.lt_iff_toNat_lt, hsq] at h1
      have hlt : d.toNat < 65536 := by
        by_contra hc
        nlinarith
      have hadd : (d + 2).toNat = d.toNat + 2 := by
        rw [UInt64.toNat_add]
        exact Nat.mod_eq_of_lt (by have : (2 : UInt64).toNat = 2 := rfl; omega)
      have hnd : ¬ d.toNat ∣ n.toNat := by
        intro hdvd
        apply h2
        apply UInt64.toNat_inj.1
        rw [UInt64.toNat_mod]
        exact Nat.mod_eq_zero_of_dvd hdvd
      refine ih (d + 2) b (by omega) (by omega) (by omega) (fun p hp hpd => ?_) h
      rw [hadd]
      have h5 := hmin p hp hpd
      have hpodd : p % 2 = 1 := by
        rcases Nat.Prime.eq_two_or_odd hp with rfl | h
        · omega
        · exact h
      have hne : p ≠ d.toNat := fun he => hnd (he ▸ hpd)
      omega

/-- **The one-word primality test is correct.** -/
theorem isPrimeWord_eq_some {n : UInt64} {b : Bool} (h : isPrimeWord n = some b) :
    b = true ↔ Nat.Prime n.toNat := by
  unfold isPrimeWord at h
  split_ifs at h with h0 h1 h2 h3
  · -- `n < 2`
    cases h
    rw [UInt64.lt_iff_toNat_lt] at h1
    have : (2 : UInt64).toNat = 2 := rfl
    simp only [Bool.false_eq_true, false_iff]
    intro hp
    have := hp.two_le
    omega
  · -- `n = 2, 3`
    cases h
    rw [UInt64.lt_iff_toNat_lt] at h1 h2
    have e2 : (2 : UInt64).toNat = 2 := rfl
    have e4 : (4 : UInt64).toNat = 4 := rfl
    simp only [true_iff]
    have : n.toNat = 2 ∨ n.toNat = 3 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num
  · -- even
    cases h
    rw [UInt64.lt_iff_toNat_lt] at h1 h2
    have e2 : (2 : UInt64).toNat = 2 := rfl
    have e4 : (4 : UInt64).toNat = 4 := rfl
    have hmod := congrArg UInt64.toNat h3
    rw [UInt64.toNat_mod, e2] at hmod
    simp only [Bool.false_eq_true, false_iff]
    intro hp
    rcases Nat.Prime.eq_two_or_odd hp with h | h
    · omega
    · have : (0 : UInt64).toNat = 0 := rfl
      omega
  · -- odd, at least 5
    rw [UInt64.le_iff_toNat_le] at h0
    rw [UInt64.lt_iff_toNat_lt] at h1 h2
    have e2 : (2 : UInt64).toNat = 2 := rfl
    have e4 : (4 : UInt64).toNat = 4 := rfl
    have e3 : (3 : UInt64).toNat = 3 := rfl
    have ebig : (4294967296 : UInt64).toNat = 4294967296 := rfl
    have hodd : n.toNat % 2 = 1 := by
      by_contra hc
      apply h3
      apply UInt64.toNat_inj.1
      rw [UInt64.toNat_mod, e2]
      have : (0 : UInt64).toNat = 0 := rfl
      omega
    refine trialOddWord_spec n (by omega) hodd (by omega) 32770 3 b (by omega) (by omega)
      (by omega) (fun p hp hpd => ?_) h
    rw [e3]
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · have := hp.two_le
      have : p = 2 := by omega
      subst this
      omega
    · exact hge

end Azurite.AzNat
