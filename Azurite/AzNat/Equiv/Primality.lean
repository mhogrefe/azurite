import Azurite.AzNat.Primality
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.SqrtRem
import Azurite.AzNat.Equiv.Div.DivMod
import Mathlib.Data.Nat.Prime.Basic

/-!
# Correctness of the naive primality test

This file proves that `Azurite.AzNat.isPrime` reflects `Nat.Prime`:
`isPrime n = true ↔ Nat.Prime n.toNat`.
-/

namespace Azurite.AzNat

private theorem toNat_two : ((2 : UInt64).toAzNat).toNat = 2 := by
  rw [UInt64.toNat_toAzNat]; decide

private theorem toNat_three : ((3 : UInt64).toAzNat).toNat = 3 := by
  rw [UInt64.toNat_toAzNat]; decide

private theorem toNat_zero_az : ((0 : AzNat)).toNat = 0 := by decide

/-- Spec for `trialDivideOdd`: starting at `d` and stepping by `2`, it returns
`true` iff none of `d, d+2, d+4, …, ≤ s` divides `n`. -/
theorem trialDivideOdd_eq_true_iff (n s d : AzNat) :
    trialDivideOdd n s d = true ↔
      ∀ k : ℕ, d.toNat + 2 * k ≤ s.toNat → ¬ ((d.toNat + 2 * k) ∣ n.toNat) := by
  induction d using trialDivideOdd.induct (n := n) (s := s) with
  | case1 d hgt =>
    -- compare d s = gt, returns true; RHS vacuous
    rw [trialDivideOdd, dif_pos hgt]
    have hlt : s.toNat < d.toNat := by
      rw [compare_eq_compare_toNat] at hgt
      exact Nat.compare_eq_gt.mp hgt
    simp only [true_iff]
    intro k hk
    omega
  | case2 d hgt hmod =>
    -- not gt, n % d == 0, returns false; RHS false at k = 0
    rw [trialDivideOdd, dif_neg hgt, if_pos hmod]
    have hle : d.toNat ≤ s.toNat := by
      rw [compare_eq_compare_toNat] at hgt
      exact Nat.le_of_not_lt (fun h => hgt (Nat.compare_eq_gt.mpr h))
    have hdvd : d.toNat ∣ n.toNat := by
      rw [beq_iff_eq] at hmod
      have : (n % d).toNat = (0 : AzNat).toNat := by rw [hmod]
      rw [toNat_mod, toNat_zero_az] at this
      exact Nat.dvd_of_mod_eq_zero this
    simp only [Bool.false_eq_true, false_iff, not_forall, not_not]
    refine ⟨0, ?_⟩
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ⟨hle, hdvd⟩
  | case3 d hgt hmod ih =>
    -- not gt, n % d != 0, recurse on d+2
    rw [trialDivideOdd, dif_neg hgt, if_neg hmod]
    have hndvd : ¬ (d.toNat ∣ n.toNat) := by
      intro hd
      apply hmod
      rw [beq_iff_eq]
      apply toNat_injective
      rw [toNat_mod, toNat_zero_az]
      exact Nat.dvd_iff_mod_eq_zero.mp hd
    have hd2 : (d + (2 : UInt64).toAzNat).toNat = d.toNat + 2 := by
      rw [toNat_add, toNat_two]
    rw [ih, hd2]
    constructor
    · -- shifted → unshifted
      intro h k hk
      rcases k with _ | j
      · simpa using hndvd
      · have := h j (by omega)
        have he : d.toNat + 2 + 2 * j = d.toNat + 2 * (j + 1) := by ring
        rwa [he] at this
    · -- unshifted → shifted
      intro h k hk
      have := h (k + 1) (by omega)
      have he : d.toNat + 2 * (k + 1) = d.toNat + 2 + 2 * k := by ring
      rwa [he] at this

/-- **Correctness of the naive primality test.**  `isPrime n` returns `true`
iff `n.toNat` is prime. -/
theorem isPrime_eq_true_iff (n : AzNat) : isPrime n = true ↔ Nat.Prime n.toNat := by
  unfold isPrime
  -- Condition translations
  have hlt2 : (compare n (2 : UInt64).toAzNat = Ordering.lt) ↔ n.toNat < 2 := by
    rw [compare_eq_compare_toNat, toNat_two]
    exact ⟨Nat.compare_eq_lt.mp, Nat.compare_eq_lt.mpr⟩
  have heq2 : (n == (2 : UInt64).toAzNat) = true ↔ n.toNat = 2 := by
    rw [beq_iff_eq]
    constructor
    · intro h; rw [h, toNat_two]
    · intro h; apply toNat_injective; rw [toNat_two]; exact h
  by_cases hc1 : compare n (2 : UInt64).toAzNat = Ordering.lt
  · -- n < 2: not prime
    rw [if_pos hc1]
    have : n.toNat < 2 := hlt2.mp hc1
    simp only [Bool.false_eq_true, false_iff]
    intro hp
    have := hp.two_le
    omega
  · rw [if_neg hc1]
    have hge2 : 2 ≤ n.toNat := by
      have := hlt2.not.mp hc1
      omega
    by_cases hc2 : (n == (2 : UInt64).toAzNat) = true
    · -- n = 2: prime
      rw [if_pos hc2]
      have h2 : n.toNat = 2 := heq2.mp hc2
      rw [h2]
      simp only [true_iff]
      exact Nat.prime_two
    · rw [if_neg hc2]
      have hne2 : n.toNat ≠ 2 := fun h => hc2 (heq2.mpr h)
      by_cases hc3 : n.isEven = true
      · -- even and > 2: composite
        rw [if_pos hc3]
        have heven : Even n.toNat := (isEven_iff n).mp hc3
        simp only [Bool.false_eq_true, false_iff]
        intro hp
        have := (Nat.Prime.even_iff hp).mp heven
        exact hne2 this
      · -- odd and > 2: trial divide
        rw [if_neg hc3]
        have hodd : ¬ Even n.toNat := fun h => hc3 ((isEven_iff n).mpr h)
        have hoddn : Odd n.toNat := Nat.not_even_iff_odd.mp hodd
        rw [trialDivideOdd_eq_true_iff, toNat_three, toNat_sqrt]
        rw [Nat.prime_def_le_sqrt]
        constructor
        · -- our condition → prime condition
          intro h
          refine ⟨hge2, ?_⟩
          intro m hm2 hms
          by_cases hme : Even m
          · -- even m divides odd n: impossible
            intro hmdvd
            have h2m : (2 : ℕ) ∣ m := hme.two_dvd
            have : (2 : ℕ) ∣ n.toNat := dvd_trans h2m hmdvd
            exact (Nat.not_even_iff_odd.mpr hoddn) (even_iff_two_dvd.mpr this)
          · -- odd m: m = 3 + 2*k
            have hmodd : Odd m := Nat.not_even_iff_odd.mp hme
            have hm1 : m % 2 = 1 := Nat.odd_iff.mp hmodd
            have hm3 : 3 ≤ m := by omega
            have hk : 3 + 2 * ((m - 3) / 2) = m := by omega
            have := h ((m - 3) / 2) (by rw [hk]; exact hms)
            rw [hk] at this
            exact this
        · -- prime condition → our condition
          rintro ⟨_, h⟩ k hk
          exact h (3 + 2 * k) (by omega) hk

/-- `ofNat`-phrased correctness: `isPrime (ofNat k)` returns `true` iff `k` is prime. -/
theorem isPrime_ofNat_eq_true_iff (k : Nat) : isPrime (ofNat k) = true ↔ Nat.Prime k := by
  rw [isPrime_eq_true_iff, toNat_ofNat]

end Azurite.AzNat
