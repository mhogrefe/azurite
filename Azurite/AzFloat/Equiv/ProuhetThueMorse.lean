/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Equiv.RoundScaled
import Azurite.AzFloat.ProuhetThueMorse
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftRight
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Prouhet–Thue–Morse constant is a lift

`prouhetThueMorseConstant : ℝ := Σ tₙ / 2^(n+1)` with `tₙ` the Thue–Morse sequence, and
`prouhetThueMorsePrecRound_eq_liftVal₀ : prouhetThueMorsePrecRound p mode = liftVal₀ (some
prouhetThueMorseConstant) p mode`.

* The sequence: `prouhetThueMorseSeq_pow_mul_add` (`t (2^k a + b) = t a xor t b` for
  `b < 2^k`), hence `t (2^k) = 1`, `t (3 · 2^k) = 0`, and `t (64 j + l) = t j xor t l`.
* The words: `ptmWord k` is the integer whose `2^k` bits are the first `2^k` terms
  (`ptmWord_eq_sum`), and `ptmWord 6` is the literal `prouhetThueMorseWord` by `decide`; a limb
  is the word or its complement (`toNat_prouhetThueMorseLimb`), and `prouhetThueMorseLimbs N`
  is the integer of the first `64 N` bits (`toNat_prouhetThueMorseLimbs`).
* The real: the partial sum of `K` terms is that integer over `2^K`, and the tail lies strictly
  between `0` and `2^-K` because the sequence is not eventually constant (`tail_bounds`); in
  particular `1/4 < τ < 1/2`.
* Rounding: the first `p + 1` significant bits give the floor at `p` bits and the round bit, the
  truncation is never exact and the value never a midpoint, so `roundFromFloor_spec` and
  `normalizeCarry_spec` assemble the rounding as for the square root.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The sequence -/

theorem prouhetThueMorseSeq_zero : prouhetThueMorseSeq 0 = false := by
  rw [prouhetThueMorseSeq]; simp

theorem prouhetThueMorseSeq_of_ne_zero (n : ℕ) (hn : n ≠ 0) :
    prouhetThueMorseSeq n = xor (prouhetThueMorseSeq (n / 2)) (decide (n % 2 = 1)) := by
  rw [prouhetThueMorseSeq]; simp [hn]

/-- The recursion holds at `0` as well. -/
theorem prouhetThueMorseSeq_eq (n : ℕ) :
    prouhetThueMorseSeq n = xor (prouhetThueMorseSeq (n / 2)) (decide (n % 2 = 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [prouhetThueMorseSeq_zero]
  · exact prouhetThueMorseSeq_of_ne_zero n hn

theorem prouhetThueMorseSeq_one : prouhetThueMorseSeq 1 = true := by
  rw [prouhetThueMorseSeq_eq]; simp [prouhetThueMorseSeq_zero]

/-- The parity of the number of ones is additive over disjoint bit ranges. -/
theorem prouhetThueMorseSeq_pow_mul_add (k a b : ℕ) (hb : b < 2 ^ k) :
    prouhetThueMorseSeq (2 ^ k * a + b) = xor (prouhetThueMorseSeq a) (prouhetThueMorseSeq b) := by
  induction k generalizing b with
  | zero =>
    have hb0 : b = 0 := by simpa using hb
    subst hb0
    simp [prouhetThueMorseSeq_zero]
  | succ k ih =>
    have h2 : 2 ^ (k + 1) * a + b = 2 * (2 ^ k * a) + b := by rw [pow_succ]; ring
    rw [h2, prouhetThueMorseSeq_eq (2 * (2 ^ k * a) + b)]
    have hdiv : (2 * (2 ^ k * a) + b) / 2 = 2 ^ k * a + b / 2 := by omega
    have hmod : (2 * (2 ^ k * a) + b) % 2 = b % 2 := by omega
    rw [hdiv, hmod, ih (b / 2) (by rw [pow_succ] at hb; omega), prouhetThueMorseSeq_eq b,
      Bool.xor_assoc]

theorem prouhetThueMorseSeq_two_pow (k : ℕ) : prouhetThueMorseSeq (2 ^ k) = true := by
  have := prouhetThueMorseSeq_pow_mul_add k 1 0 (by positivity)
  simpa [prouhetThueMorseSeq_zero, prouhetThueMorseSeq_one] using this

theorem prouhetThueMorseSeq_three_mul_two_pow (k : ℕ) :
    prouhetThueMorseSeq (2 ^ k * 3) = false := by
  have h3 : prouhetThueMorseSeq 3 = false := by
    rw [prouhetThueMorseSeq_eq]
    simp [prouhetThueMorseSeq_one]
  have := prouhetThueMorseSeq_pow_mul_add k 3 0 (by positivity)
  simpa [prouhetThueMorseSeq_zero, h3] using this

/-- The term `tₙ` as a natural number. -/
def ptmBit (n : ℕ) : ℕ := if prouhetThueMorseSeq n then 1 else 0

theorem ptmBit_le_one (n : ℕ) : ptmBit n ≤ 1 := by
  unfold ptmBit; split_ifs <;> omega

/-! ### The words -/

/-- The integer whose `2^k` bits are the first `2^k` terms of the sequence, most significant
first: `T₀ = 0`, `T_(k+1) = T_k ∥ ¬T_k`. -/
def ptmWord : ℕ → ℕ
  | 0 => 0
  | k + 1 => ptmWord k * 2 ^ (2 ^ k) + (2 ^ (2 ^ k) - 1 - ptmWord k)

/-- `Σ_{i<m} 2^(m−1−i) = 2^m − 1`. -/
theorem sum_two_pow_rev (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ (m - 1 - i) = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ', show m + 1 - 1 - 0 = m by omega]
    have : ∀ i ∈ Finset.range m, 2 ^ (m + 1 - 1 - (i + 1)) = 2 ^ (m - 1 - i) := by
      intro i hi
      congr 1
      omega
    rw [Finset.sum_congr rfl this, ih, pow_succ]
    have := Nat.one_le_two_pow (n := m)
    omega

theorem ptmWord_lt (k : ℕ) : ptmWord k < 2 ^ (2 ^ k) := by
  induction k with
  | zero => simp [ptmWord]
  | succ k ih =>
    rw [ptmWord, pow_succ, pow_mul]
    have h1 := Nat.one_le_two_pow (n := 2 ^ k)
    have : ptmWord k * 2 ^ 2 ^ k + (2 ^ 2 ^ k - 1 - ptmWord k)
        ≤ (ptmWord k + 1) * 2 ^ 2 ^ k - 1 := by
      rw [add_mul, one_mul]
      omega
    calc ptmWord k * 2 ^ 2 ^ k + (2 ^ 2 ^ k - 1 - ptmWord k)
          ≤ (ptmWord k + 1) * 2 ^ 2 ^ k - 1 := this
      _ < (ptmWord k + 1) * 2 ^ 2 ^ k := Nat.sub_lt (by positivity) one_pos
      _ ≤ 2 ^ 2 ^ k * 2 ^ 2 ^ k := Nat.mul_le_mul_right _ ih
      _ = (2 ^ 2 ^ k) ^ 2 := (sq _).symm

theorem ptmWord_eq_sum (k : ℕ) :
    ptmWord k = ∑ i ∈ Finset.range (2 ^ k), ptmBit i * 2 ^ (2 ^ k - 1 - i) := by
  induction k with
  | zero =>
    simp only [ptmWord, pow_zero, Finset.sum_range_one, ptmBit, prouhetThueMorseSeq_zero,
      Bool.false_eq_true, ↓reduceIte, zero_mul]
  | succ k ih =>
    rw [ptmWord, pow_succ, mul_two, Finset.sum_range_add]
    -- the first half: the exponents shift by `2^k`
    have h1 : ∑ i ∈ Finset.range (2 ^ k), ptmBit i * 2 ^ (2 ^ k + 2 ^ k - 1 - i)
        = ptmWord k * 2 ^ 2 ^ k := by
      rw [ih, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    -- the second half: the complemented bits
    have h2 : ∑ i ∈ Finset.range (2 ^ k), ptmBit (2 ^ k + i) * 2 ^ (2 ^ k + 2 ^ k - 1 - (2 ^ k + i))
        = 2 ^ 2 ^ k - 1 - ptmWord k := by
      have hc : ∀ i ∈ Finset.range (2 ^ k),
          ptmBit (2 ^ k + i) * 2 ^ (2 ^ k + 2 ^ k - 1 - (2 ^ k + i))
            = 2 ^ (2 ^ k - 1 - i) - ptmBit i * 2 ^ (2 ^ k - 1 - i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have hx : 2 ^ k + 2 ^ k - 1 - (2 ^ k + i) = 2 ^ k - 1 - i := by omega
        rw [hx]
        have ht : prouhetThueMorseSeq (2 ^ k + i) = !prouhetThueMorseSeq i := by
          have := prouhetThueMorseSeq_pow_mul_add k 1 i hi
          rw [mul_one] at this
          rw [this, prouhetThueMorseSeq_one]
          cases prouhetThueMorseSeq i <;> rfl
        unfold ptmBit
        rw [ht]
        cases prouhetThueMorseSeq i <;> simp
      have hbnd : ∀ i, ptmBit i * 2 ^ (2 ^ k - 1 - i) ≤ 2 ^ (2 ^ k - 1 - i) := fun i =>
        calc ptmBit i * 2 ^ (2 ^ k - 1 - i) ≤ 1 * 2 ^ (2 ^ k - 1 - i) :=
              Nat.mul_le_mul_right _ (ptmBit_le_one i)
          _ = 2 ^ (2 ^ k - 1 - i) := one_mul _
      rw [Finset.sum_congr rfl hc, Finset.sum_tsub_distrib _ (fun i _ => hbnd i), sum_two_pow_rev,
        ← ih]
    rw [h1, h2]

theorem toNat_prouhetThueMorseWord : prouhetThueMorseWord.toNat = ptmWord 6 := by decide

theorem toNat_prouhetThueMorseWordNot :
    prouhetThueMorseWordNot.toNat = 2 ^ 64 - 1 - ptmWord 6 := by decide

/-- A limb is the 64 bits `t (64 j + l)`, `l < 64`, most significant first. -/
theorem toNat_prouhetThueMorseLimb (j : ℕ) :
    (prouhetThueMorseLimb j).toNat = ∑ l ∈ Finset.range 64, ptmBit (64 * j + l) * 2 ^ (63 - l) := by
  have hbit : ∀ l ∈ Finset.range 64, ptmBit (64 * j + l)
      = if prouhetThueMorseSeq j then 1 - ptmBit l else ptmBit l := by
    intro l hl
    rw [Finset.mem_range] at hl
    have h64 : 64 * j + l = 2 ^ 6 * j + l := by norm_num
    unfold ptmBit
    rw [h64, prouhetThueMorseSeq_pow_mul_add 6 j l (by norm_num; exact hl)]
    cases prouhetThueMorseSeq j <;> cases prouhetThueMorseSeq l <;> simp
  rw [Finset.sum_congr rfl (fun l hl => by rw [hbit l hl])]
  have hT : ptmWord 6 = ∑ l ∈ Finset.range 64, ptmBit l * 2 ^ (63 - l) := by
    rw [ptmWord_eq_sum]
    norm_num
  have hbnd : ∀ l, ptmBit l * 2 ^ (63 - l) ≤ 2 ^ (63 - l) := fun l =>
    calc ptmBit l * 2 ^ (63 - l) ≤ 1 * 2 ^ (63 - l) := Nat.mul_le_mul_right _ (ptmBit_le_one l)
      _ = 2 ^ (63 - l) := one_mul _
  unfold prouhetThueMorseLimb
  rcases Bool.eq_false_or_eq_true (prouhetThueMorseSeq j) with hj | hj <;> rw [hj]
  · simp only [↓reduceIte]
    rw [toNat_prouhetThueMorseWordNot, hT]
    have hsub : ∀ l ∈ Finset.range 64, (1 - ptmBit l) * 2 ^ (63 - l)
        = 2 ^ (63 - l) - ptmBit l * 2 ^ (63 - l) := by
      intro l _
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (ptmBit_le_one l) with h | h <;> rw [h] <;> simp
    rw [Finset.sum_congr rfl hsub, Finset.sum_tsub_distrib _ (fun l _ => hbnd l)]
    have := sum_two_pow_rev 64
    simp only [show (64 : ℕ) - 1 = 63 by norm_num] at this
    rw [this]
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [toNat_prouhetThueMorseWord, hT]

/-- The value of a little-endian list of limbs given by a function. -/
theorem toNatLimbsList_ofFn (N : ℕ) (f : ℕ → UInt64) :
    AzNat.toNatLimbsList (List.ofFn fun i : Fin N => f i)
      = ∑ i ∈ Finset.range N, (f i).toNat * 2 ^ (64 * i) := by
  induction N generalizing f with
  | zero => simp [AzNat.toNatLimbsList]
  | succ N ih =>
    rw [List.ofFn_succ, AzNat.toNatLimbsList_cons, Finset.sum_range_succ']
    simp only [Fin.val_zero, Fin.val_succ, mul_zero, pow_zero, mul_one]
    rw [ih (fun i => f (i + 1)), Finset.sum_mul]
    refine congrArg₂ (· + ·) ?_ rfl
    apply Finset.sum_congr rfl
    intro i _
    rw [show 64 * (i + 1) = 64 * i + 64 by ring, pow_add, mul_assoc]

/-- Regrouping the bits of the first `N` limbs. -/
theorem sum_limbs_eq (N : ℕ) :
    ∑ i ∈ Finset.range N,
        (∑ l ∈ Finset.range 64, ptmBit (64 * (N - 1 - i) + l) * 2 ^ (63 - l)) * 2 ^ (64 * i)
      = ∑ n ∈ Finset.range (64 * N), ptmBit n * 2 ^ (64 * N - 1 - n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ', show 64 * (N + 1) = 64 * N + 64 by ring, Finset.sum_range_add]
    have hre : ∀ i ∈ Finset.range N,
        (∑ l ∈ Finset.range 64, ptmBit (64 * (N + 1 - 1 - (i + 1)) + l) * 2 ^ (63 - l))
          * 2 ^ (64 * (i + 1))
        = (∑ l ∈ Finset.range 64, ptmBit (64 * (N - 1 - i) + l) * 2 ^ (63 - l)) * 2 ^ (64 * i)
          * 2 ^ 64 := by
      intro i _
      rw [show N + 1 - 1 - (i + 1) = N - 1 - i by omega, show 64 * (i + 1) = 64 * i + 64 by ring,
        pow_add, mul_assoc]
    rw [Finset.sum_congr rfl hre, ← Finset.sum_mul, ih, Finset.sum_mul,
      show N + 1 - 1 - 0 = N by omega, mul_zero, pow_zero, mul_one]
    refine congrArg₂ (· + ·) ?_ ?_
    · apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_range] at hn
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    · apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mem_range] at hl
      congr 2
      omega

/-- The integer of the first `64 N` bits. -/
theorem toNat_prouhetThueMorseLimbs (N : ℕ) :
    (prouhetThueMorseLimbs N).toNat
      = ∑ n ∈ Finset.range (64 * N), ptmBit n * 2 ^ (64 * N - 1 - n) := by
  unfold prouhetThueMorseLimbs
  rw [AzNat.toNat_ofLimbs, Array.toList_ofFn,
    toNatLimbsList_ofFn N (fun i => prouhetThueMorseLimb (N - 1 - i)), ← sum_limbs_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [toNat_prouhetThueMorseLimb]

/-! ### The real number -/

/-- The term `tₙ / 2^(n+1)`. -/
noncomputable def ptmTerm (n : ℕ) : ℝ := (ptmBit n : ℝ) / 2 ^ (n + 1)

/-- The Prouhet–Thue–Morse constant `Σ tₙ / 2^(n+1)`. -/
noncomputable def prouhetThueMorseConstant : ℝ := ∑' n : ℕ, ptmTerm n

theorem ptmTerm_nonneg (n : ℕ) : 0 ≤ ptmTerm n := by unfold ptmTerm; positivity

theorem ptmTerm_le (n : ℕ) : ptmTerm n ≤ 1 / 2 / 2 ^ n := by
  unfold ptmTerm
  have h := ptmBit_le_one n
  have h' : (ptmBit n : ℝ) ≤ 1 := by exact_mod_cast h
  rw [show (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n by ring, div_div]
  exact div_le_div_of_nonneg_right h' (by positivity)

theorem summable_ptmTerm_shift (K : ℕ) : Summable fun n => ptmTerm (n + K) := by
  apply Summable.of_nonneg_of_le (fun n => ptmTerm_nonneg _) _ (summable_geometric_two' 1)
  intro n
  have h1 := ptmTerm_le (n + K)
  have h2 : (1 : ℝ) / 2 / 2 ^ (n + K) ≤ 1 / 2 / 2 ^ n := by
    gcongr
    · norm_num
    · omega
  exact h1.trans h2

theorem summable_ptmTerm : Summable ptmTerm := by
  simpa using summable_ptmTerm_shift 0

/-- The partial sum of `K` terms is the integer of the first `K` bits over `2^K`. -/
theorem sum_ptmTerm (K : ℕ) :
    ∑ n ∈ Finset.range K, ptmTerm n
      = ((∑ n ∈ Finset.range K, ptmBit n * 2 ^ (K - 1 - n) : ℕ) : ℝ) / 2 ^ K := by
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  unfold ptmTerm
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add]
  congr 2
  omega

/-- The tail after `K` terms lies strictly between `0` and `2^-K`. -/
theorem tail_bounds (K : ℕ) :
    0 < ∑' n, ptmTerm (n + K) ∧ ∑' n, ptmTerm (n + K) < 1 / 2 ^ K := by
  have hK : K ≤ 2 ^ K := (Nat.lt_two_pow_self).le
  constructor
  · -- the term at `2^K`
    have hi : ptmTerm (2 ^ K - K + K) = 1 / 2 ^ (2 ^ K + 1) := by
      unfold ptmTerm ptmBit
      rw [Nat.sub_add_cancel hK, prouhetThueMorseSeq_two_pow]
      simp
    calc (0 : ℝ) < 1 / 2 ^ (2 ^ K + 1) := by positivity
      _ = ptmTerm (2 ^ K - K + K) := hi.symm
      _ ≤ ∑' n, ptmTerm (n + K) :=
        (summable_ptmTerm_shift K).le_tsum _ (fun j _ => ptmTerm_nonneg _)
  · -- strictly below the all-ones tail, at `3 · 2^K`
    have hsum : ∑' n : ℕ, (1 : ℝ) / 2 ^ K / 2 / 2 ^ n = 1 / 2 ^ K := tsum_geometric_two' _
    rw [← hsum]
    apply Summable.tsum_lt_tsum (i := 2 ^ K * 3 - K) _ _ (summable_ptmTerm_shift K)
      (summable_geometric_two' _)
    · intro n
      have := ptmTerm_le (n + K)
      rw [pow_add] at this
      calc ptmTerm (n + K) ≤ 1 / 2 / (2 ^ n * 2 ^ K) := this
        _ = 1 / 2 ^ K / 2 / 2 ^ n := by field_simp
    · have hK3 : K ≤ 2 ^ K * 3 := by omega
      have hzero : ptmTerm (2 ^ K * 3 - K + K) = 0 := by
        unfold ptmTerm ptmBit
        rw [Nat.sub_add_cancel hK3, prouhetThueMorseSeq_three_mul_two_pow]
        simp
      rw [hzero]
      positivity

/-- `τ · 2^K` is the integer of the first `K` bits plus a tail in `(0, 1)`. -/
theorem prouhetThueMorseConstant_mul_two_pow (K : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      prouhetThueMorseConstant * 2 ^ K
        = ((∑ n ∈ Finset.range K, ptmBit n * 2 ^ (K - 1 - n) : ℕ) : ℝ) + θ := by
  obtain ⟨hlo, hhi⟩ := tail_bounds K
  refine ⟨(∑' n, ptmTerm (n + K)) * 2 ^ K, by positivity, ?_, ?_⟩
  · have := mul_lt_mul_of_pos_right hhi (by positivity : (0 : ℝ) < 2 ^ K)
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  · unfold prouhetThueMorseConstant
    rw [← summable_ptmTerm.sum_add_tsum_nat_add K, sum_ptmTerm, add_mul,
      div_mul_cancel₀ _ (by positivity)]

/-- `1/4 < τ < 1/2`. -/
theorem prouhetThueMorseConstant_bounds :
    1 / 4 < prouhetThueMorseConstant ∧ prouhetThueMorseConstant < 1 / 2 := by
  obtain ⟨θ, hθ0, hθ1, h⟩ := prouhetThueMorseConstant_mul_two_pow 2
  have hsum : (∑ n ∈ Finset.range 2, ptmBit n * 2 ^ (2 - 1 - n) : ℕ) = 1 := by
    simp [Finset.sum_range_succ, ptmBit, prouhetThueMorseSeq_zero, prouhetThueMorseSeq_one]
  rw [hsum] at h
  push_cast at h
  constructor <;> nlinarith

/-! ### The lift -/

/-- The Prouhet–Thue–Morse constant is the lift of its value. -/
theorem prouhetThueMorsePrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    prouhetThueMorsePrecRound p mode
      = liftVal₀ (some ((prouhetThueMorseConstant : ℝ) : EReal)) p mode := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  unfold prouhetThueMorsePrecRound liftVal₀
  rw [ite_eq_right hp.ne']
  simp only
  set N := (p + 2) / 64 + 1 with hN
  have hK : p + 2 < 64 * N := by omega
  set s := 64 * N - (p + 2) with hs
  set τ := prouhetThueMorseConstant with hτ
  obtain ⟨hτlo, hτhi⟩ := prouhetThueMorseConstant_bounds
  -- the integer of the first `64 N` bits and the first `p + 2` bits
  obtain ⟨θ, hθ0, hθ1, hX⟩ := prouhetThueMorseConstant_mul_two_pow (64 * N)
  rw [← toNat_prouhetThueMorseLimbs N] at hX
  set X := (prouhetThueMorseLimbs N).toNat with hXdef
  set Y := X / 2 ^ s with hY
  have hYeq : ((prouhetThueMorseLimbs N).shiftRight s).toNat = Y := by
    rw [AzNat.toNat_shiftRight]
  -- `τ · 2^(p+2) = Y + θ'` with `0 < θ' < 1`
  have h2s : (0 : ℝ) < 2 ^ s := by positivity
  have hXY : (X : ℝ) = Y * 2 ^ s + (X % 2 ^ s : ℕ) := by
    rw [hY]
    exact_mod_cast (Nat.div_add_mod' X (2 ^ s)).symm
  have hr : (X % 2 ^ s : ℕ) < 2 ^ s := Nat.mod_lt _ (by positivity)
  have hr' : ((X % 2 ^ s : ℕ) : ℝ) + 1 ≤ 2 ^ s := by exact_mod_cast hr
  set θ' : ℝ := ((X % 2 ^ s : ℕ) + θ) / 2 ^ s with hθ'
  have hθ'0 : 0 < θ' := by rw [hθ']; positivity
  have hθ'1 : θ' < 1 := by
    rw [hθ', div_lt_one h2s]
    linarith
  have hτp2 : τ * 2 ^ (p + 2) = Y + θ' := by
    have h64 : (2 : ℝ) ^ (64 * N) = 2 ^ (p + 2) * 2 ^ s := by
      rw [← pow_add]; congr 1; omega
    have := hX
    rw [h64, ← mul_assoc, hXY] at this
    rw [hθ']
    field_simp
    linarith
  -- the floor `m` at `p` bits and the round bit `ρ`
  set m := Y / 2 with hm
  have hmeq : ((prouhetThueMorseLimbs N).shiftRight s |>.shiftRight 1).toNat = m := by
    rw [AzNat.toNat_shiftRight, hYeq, pow_one]
  set ρ := Y % 2 with hρ
  have hYm : (Y : ℝ) = 2 * m + ρ := by
    rw [hm, hρ]; exact_mod_cast (Nat.div_add_mod Y 2).symm
  have hρ1 : ρ < 2 := Nat.mod_lt _ two_pos
  set y : ℝ := τ * 2 ^ (p + 1) with hy
  have hy2 : y = m + ((ρ : ℝ) + θ') / 2 := by
    have : y * 2 = Y + θ' := by rw [hy, mul_assoc, ← pow_succ]; exact hτp2
    rw [hYm] at this
    linarith
  have hρ0 : (0 : ℝ) ≤ ρ := by positivity
  have hlo : (m : ℝ) ≤ y := by
    rw [hy2]
    linarith
  have hhi : y < m + 1 := by
    rw [hy2]
    have : (ρ : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hρ1
    linarith
  have hex : false = true ↔ y = (m : ℝ) := by
    constructor
    · intro h; exact absurd h (by simp)
    · intro h
      rw [hy2] at h
      linarith
  have hodd : ((prouhetThueMorseLimbs N).shiftRight s).isOdd = true ↔ ρ = 1 := by
    rw [AzNat.isOdd_iff, hYeq, Nat.odd_iff]
  have hmid : (if ((prouhetThueMorseLimbs N).shiftRight s).isOdd then Ordering.gt else Ordering.lt)
      = compare y ((m : ℝ) + 1 / 2) := by
    by_cases hodd' : ((prouhetThueMorseLimbs N).shiftRight s).isOdd = true
    · have hρ1' : ρ = 1 := hodd.mp hodd'
      have hgt : (m : ℝ) + 1 / 2 < y := by
        rw [hy2, hρ1']
        push_cast
        linarith
      rw [ite_eq_left hodd', eq_comm, compare_gt_iff_gt]
      exact hgt
    · have hρ0' : ρ = 0 := by
        have : ρ ≠ 1 := fun h => hodd' (hodd.mpr h)
        omega
      have hlt : y < (m : ℝ) + 1 / 2 := by
        rw [hy2, hρ0']
        push_cast
        linarith
      rw [ite_eq_right hodd', eq_comm, compare_lt_iff_lt]
      exact hlt
  obtain ⟨hR, htag⟩ := roundFromFloor_spec y
    ((prouhetThueMorseLimbs N).shiftRight s |>.shiftRight 1)
    false (if ((prouhetThueMorseLimbs N).shiftRight s).isOdd then Ordering.gt else Ordering.lt) mode
    (by rw [hmeq]; exact hlo) (by rw [hmeq]; exact hhi) (by rw [hmeq]; exact hex)
    (by rw [hmeq]; exact hmid)
  set ro := roundFromFloor ((prouhetThueMorseLimbs N).shiftRight s |>.shiftRight 1) false
    (if ((prouhetThueMorseLimbs N).shiftRight s).isOdd then Ordering.gt else Ordering.lt) mode
    with hro
  clear_value ro
  -- the scale of `τ`
  have hτ0 : τ ≠ 0 := by linarith
  have hτabs : |τ| = τ := abs_of_pos (by linarith)
  have hlog : Int.log 2 |τ| = -2 := by
    rw [hτabs]
    apply le_antisymm
    · apply Int.lt_add_one_iff.mp
      apply (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (by linarith)).mp
      push_cast
      norm_num
      linarith
    · apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (by linarith)).mp
      push_cast
      norm_num
      linarith
  have hscale : precScale 2 p τ = (2 : ℝ) ^ (-((p : ℤ) + 1)) := by
    unfold precScale
    rw [hlog]
    push_cast
    congr 1
    ring
  have h2w : (0 : ℝ) < (2 : ℝ) ^ (-((p : ℤ) + 1)) := zpow_pos (by norm_num) _
  have hyτ : τ / (2 : ℝ) ^ (-((p : ℤ) + 1)) = y := by
    rw [hy, zpow_neg, div_inv_eq_mul, show ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
  have hround : (round (floatSet p) mode τ).val
      = ((((AzInt.mkNorm true ro.1).toInt : ℝ) * 2 ^ (-((p : ℤ) + 1)) : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode τ hτ0, hscale, hyτ, hR,
      AzInt.toInt_mkNorm_true]
  -- bounds on the rounded integer
  have h2p : (0 : ℝ) < 2 ^ (p + 1) := by positivity
  have hylo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ y := by
    rw [hy, show ((p : ℤ) - 1) = (p + 1 : ℕ) + (-(2 : ℤ)) by push_cast; ring,
      zpow_add₀ (by norm_num),
      zpow_natCast, show (2 : ℝ) ^ (-(2 : ℤ)) = 1 / 4 by norm_num]
    nlinarith
  have hyhi : y < (2 : ℝ) ^ (p : ℤ) := by
    rw [hy, show (p : ℤ) = (p + 1 : ℕ) + (-(1 : ℤ)) by push_cast; ring, zpow_add₀ (by norm_num),
      zpow_natCast, show (2 : ℝ) ^ (-(1 : ℤ)) = 1 / 2 by norm_num]
    nlinarith
  have hypos : 0 < y := lt_of_lt_of_le (zpow_pos (by norm_num) _) hylo
  obtain ⟨hb1, hb2⟩ := abs_toInt_round_bounds p hp mode y (by rw [abs_of_pos hypos]; exact hylo)
    (by rw [abs_of_pos hypos]; exact hyhi)
  rw [hR] at hb1 hb2
  have habsR : ((AzInt.mkNorm true ro.1).abs.toNat : ℤ) = |(ro.1.toNat : ℤ)| := by
    rw [AzInt.abs_toNat_eq, AzInt.toInt_mkNorm_true]
  have hlo' : 2 ^ (p - 1) ≤ (AzInt.mkNorm true ro.1).abs.toNat := by
    have : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ ((AzInt.mkNorm true ro.1).abs.toNat : ℤ) := by
      rw [habsR]; exact hb1
    exact_mod_cast this
  have hhi' : (AzInt.mkNorm true ro.1).abs.toNat ≤ 2 ^ p := by
    have : ((AzInt.mkNorm true ro.1).abs.toNat : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by
      rw [habsR]; exact hb2
    exact_mod_cast this
  obtain ⟨hRval, hRprec⟩ := normalizeCarry_spec (AzInt.mkNorm true ro.1) p hp (AzInt.ofInt (-1))
    hlo' hhi'
  have hep : (AzInt.ofInt (-1)).toInt - p = -((p : ℤ) + 1) := by
    rw [AzInt.toInt_ofInt]; ring
  rw [hep] at hRval
  symm
  refine Prod.ext ?_ ?_
  · exact toVal_injective p (ofEReal_spec p mode τ).1 (Or.inl hRprec)
      (by rw [fst_roundVal, ofVal_some, (ofEReal_spec p mode τ).2, hround, hRval])
  · show (roundVal p mode (some (τ : EReal))).2 = ro.2
    rw [(roundVal_coe p mode τ).2, hround, compare_coe_coe, htag, AzInt.toInt_mkNorm_true,
      Int.cast_natCast, ← hyτ]
    conv_rhs => rw [← compare_mul_right_pos _ _ _ h2w, div_mul_cancel₀ _ h2w.ne']

end Azurite.AzFloat
