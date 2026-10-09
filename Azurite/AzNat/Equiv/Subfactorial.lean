/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Subfactorial
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Mul
import Azurite.AzInt.Equiv.Conversion
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
## Correctness of `AzNat.subfactorial`

`toNat_subfactorial : (subfactorial n).toNat = numDerangements n` and, through Mathlib's
`card_derangements_fin_eq_numDerangements`, `toNat_subfactorial_card`: it is the number of
derangements of `Fin n`.  The splitting lemma `subfactorialSplit_spec` gives the interval
product and the alternating sum, which assemble to Mathlib's `numDerangements_sum`.
-/

namespace Azurite.AzNat

/-- The invariant of the binary splitting on `(a, b]`, valid once `fuel ≥ b − a`. -/
theorem subfactorialSplit_spec : ∀ (fuel a b : ℕ), b - a ≤ fuel →
    (subfactorialSplit fuel a b).1.toNat = ∏ k ∈ Finset.Ico (a + 1) (b + 1), k ∧
    (subfactorialSplit fuel a b).2.toInt
      = ∑ k ∈ Finset.Ico (a + 1) (b + 1),
          (-1 : ℤ) ^ k * ∏ j ∈ Finset.Ico (k + 1) (b + 1), (j : ℤ) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b hab
    rw [subfactorialSplit, Finset.Ico_eq_empty_of_le (by omega)]
    exact ⟨toNat_one, AzInt.toInt_zero⟩
  | succ fuel ih =>
    intro a b hab
    rw [subfactorialSplit]
    dsimp only
    by_cases hle : b ≤ a
    · rw [ite_eq_left hle, Finset.Ico_eq_empty_of_le (by omega)]
      exact ⟨toNat_one, AzInt.toInt_zero⟩
    rw [ite_eq_right hle]
    by_cases heq : b = a + 1
    · rw [ite_eq_left heq]
      subst heq
      rw [Nat.Ico_succ_singleton, Finset.prod_singleton, Finset.sum_singleton, Finset.Ico_self,
        Finset.prod_empty, mul_one]
      refine ⟨toNat_ofNat _, ?_⟩
      show (if (a + 1) % 2 = 0 then (1 : AzInt) else -1).toInt = _
      split_ifs with hpar
      · rw [AzInt.toInt_one, (Nat.even_iff.mpr hpar).neg_one_pow]
      · rw [AzInt.toInt_neg, AzInt.toInt_one, (Nat.odd_iff.mpr (by omega)).neg_one_pow]
    rw [ite_eq_right heq]
    dsimp only
    have hm1 : a + 1 ≤ (a + b) / 2 + 1 := by omega
    have hm2 : (a + b) / 2 + 1 ≤ b + 1 := by omega
    obtain ⟨hl1, hl2⟩ := ih a ((a + b) / 2) (by omega)
    obtain ⟨hr1, hr2⟩ := ih ((a + b) / 2) b (by omega)
    refine ⟨?_, ?_⟩
    · rw [toNat_mul, hl1, hr1, Finset.prod_Ico_consecutive _ hm1 hm2]
    · rw [AzInt.toInt_add, AzInt.toInt_mul, AzNat.toInt_toAzInt, hl2, hr2, hr1, Finset.sum_mul,
        ← Finset.sum_Ico_consecutive _ hm1 hm2]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [mul_assoc, Nat.cast_prod, Finset.prod_Ico_consecutive _ (by omega : k + 1 ≤ _) hm2]

/-- **Correctness of `subfactorial`**: it computes Mathlib's `numDerangements`, the number of
derangements defined by the recurrence `!(n+2) = (n+1) (!n + !(n+1))`. -/
theorem toNat_subfactorial (n : ℕ) : (subfactorial n).toNat = numDerangements n := by
  obtain ⟨h1, h2⟩ := subfactorialSplit_spec n 0 n (by omega)
  unfold subfactorial
  dsimp only
  rw [AzInt.toNat_natAbs, AzInt.toInt_add, AzNat.toInt_toAzInt, h1, h2]
  have hsum := numDerangements_sum n
  have hasc : ∀ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ k * (((k + 1).ascFactorial (n - k) : ℕ) : ℤ)
        = (-1 : ℤ) ^ k * ∏ j ∈ Finset.Ico (k + 1) (n + 1), (j : ℤ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Nat.ascFactorial_eq_prod_range, Finset.prod_Ico_eq_prod_range,
      show n + 1 - (k + 1) = n - k by omega]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hasc, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    at hsum
  simp only [pow_zero, one_mul, zero_add] at hsum
  have hP : ((∏ k ∈ Finset.Ico (0 + 1) (n + 1), k : ℕ) : ℤ)
      = ∏ j ∈ Finset.Ico (0 + 1) (n + 1), (j : ℤ) := by push_cast; rfl
  rw [hP, zero_add, ← hsum, Int.natAbs_natCast]

/-- **The combinatorial meaning**: `subfactorial n` is the number of derangements of `Fin n`
(fixed-point-free permutations). -/
theorem toNat_subfactorial_card (n : ℕ) :
    (subfactorial n).toNat = Fintype.card (derangements (Fin n)) := by
  rw [toNat_subfactorial, card_derangements_fin_eq_numDerangements]

end Azurite.AzNat
