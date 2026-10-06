/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.Equiv.PrimeSieve
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Equiv.ProuhetThueMorse
import Azurite.AzFloat.Equiv.RoundScaled
import Azurite.AzFloat.PrimeConstant
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftRight
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Prime.Infinite

/-!
# The prime constant is a lift

`primeConstantReal : ℝ := Σ_{n} [n prime] / 2^n` and `primeConstantPrecRound_eq_liftVal₀ :
primeConstantPrecRound p mode = liftVal₀ (some primeConstantReal) p mode`.

* The words: `toNat_wordOfBits` (a word assembled bit by bit is `Σ [f l] 2^l`),
  `sum_mul_pow_regroup` (the limbs regroup into one sum over bit positions), and
  `toNat_primeConstantLimbs`: the integer of the first `64 N` bits is `Σ_{n ≤ 64 N} [n prime]
  2^(64 N − n)`, the sieve's bitmap read backwards (`primeSieve_testBit_iff`).
* The real: the partial sum is that integer over `2^K` and the tail lies strictly between `0`
  and `2^-K`, by the infinitude of the primes and of the composites (`tail_bounds'`); in
  particular `1/4 < ρ < 1/2`.
* Rounding: as for the Prouhet–Thue–Morse constant.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The words -/

/-- A word assembled bit by bit. -/
theorem toNat_wordOfBits (f : ℕ → Bool) :
    (wordOfBits f).toNat = ∑ l ∈ Finset.range 64, (if f l then 1 else 0) * 2 ^ l := by
  have key : ∀ j, j ≤ 64 →
      ((List.range j).foldl
        (fun acc l => if f l then acc + ((1 : UInt64) <<< UInt64.ofNat l) else acc) 0).toNat
        = ∑ l ∈ Finset.range j, (if f l then 1 else 0) * 2 ^ l ∧
      ∑ l ∈ Finset.range j, (if f l then 1 else 0) * 2 ^ l < 2 ^ j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ]
      have hbnd : (if f j then 1 else 0) * 2 ^ j ≤ 2 ^ j := by split_ifs <;> omega
      have hlt : ∑ l ∈ Finset.range j, (if f l then 1 else 0) * 2 ^ l
          + (if f j then 1 else 0) * 2 ^ j < 2 ^ (j + 1) := by
        rw [pow_succ]; omega
      refine ⟨?_, hlt⟩
      by_cases hf : f j = true
      · simp only [hf, ↓reduceIte]
        rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_one, UInt64.toNat_ofNat', ih1]
        have hj1 : j < 2 ^ 64 := lt_of_lt_of_le (by omega : j < 64) (by norm_num)
        have hj' : j % 2 ^ 64 % 64 = j := by
          rw [Nat.mod_eq_of_lt hj1, Nat.mod_eq_of_lt (by omega)]
        have hpj : 2 ^ j < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
        have hle64 : 2 ^ (j + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hj
        simp only [hf, ↓reduceIte, one_mul] at hlt ⊢
        rw [hj', Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt hpj, Nat.mod_eq_of_lt (by omega)]
      · simp only [Bool.not_eq_true] at hf
        simp only [hf, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
        exact ih1
  exact (key 64 le_rfl).1

/-- Regrouping the bits of `N` words. -/
theorem sum_mul_pow_regroup (N : ℕ) (g : ℕ → ℕ) :
    ∑ i ∈ Finset.range N, (∑ l ∈ Finset.range 64, g (64 * i + l) * 2 ^ l) * 2 ^ (64 * i)
      = ∑ m ∈ Finset.range (64 * N), g m * 2 ^ m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, show 64 * (N + 1) = 64 * N + 64 by ring, Finset.sum_range_add,
      Finset.sum_mul]
    refine congrArg₂ (· + ·) rfl ?_
    apply Finset.sum_congr rfl
    intro l _
    rw [mul_assoc, ← pow_add, add_comm]

/-- The indicator of primality. -/
def pcBit (n : ℕ) : ℕ := if Nat.Prime n then 1 else 0

theorem pcBit_le_one (n : ℕ) : pcBit n ≤ 1 := by unfold pcBit; split_ifs <;> omega

/-- The integer of the first `64 N` bits: the sieve read backwards. -/
theorem toNat_primeConstantLimbs (N : ℕ) :
    (primeConstantLimbs N).toNat
      = ∑ n ∈ Finset.range (64 * N + 1), pcBit n * 2 ^ (64 * N - n) := by
  unfold primeConstantLimbs
  simp only
  rw [AzNat.toNat_ofLimbs, Array.toList_ofFn,
    toNatLimbsList_ofFn N (fun i => wordOfBits fun l => (AzNat.primeSieve (64 * N)).testBit
      (64 * N - (64 * i + l)))]
  have hw : ∀ i ∈ Finset.range N,
      (wordOfBits fun l => (AzNat.primeSieve (64 * N)).testBit (64 * N - (64 * i + l))).toNat
        * 2 ^ (64 * i)
      = (∑ l ∈ Finset.range 64, pcBit (64 * N - (64 * i + l)) * 2 ^ l) * 2 ^ (64 * i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [toNat_wordOfBits]
    refine congrArg₂ (· * ·) ?_ rfl
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_range] at hl
    have hiff := AzNat.primeSieve_testBit_iff (n := 64 * N) (j := 64 * N - (64 * i + l)) (by omega)
    unfold pcBit
    by_cases hp : Nat.Prime (64 * N - (64 * i + l))
    · rw [ite_eq_left (hiff.mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp (hiff.mp h)), ite_eq_right hp]
  have h0 : pcBit 0 * 2 ^ (64 * N - 0) = 0 := by
    simp [pcBit, Nat.not_prime_zero]
  rw [Finset.sum_congr rfl hw, sum_mul_pow_regroup N (fun m => pcBit (64 * N - m)),
    Finset.sum_range_succ', h0, add_zero,
    ← Finset.sum_range_reflect (fun j => pcBit (j + 1) * 2 ^ (64 * N - (j + 1))) (64 * N)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show 64 * N - 1 - j + 1 = 64 * N - j by omega, show 64 * N - (64 * N - j) = j by omega]

/-! ### The real number -/

/-- The term `[n prime] / 2^n`. -/
noncomputable def pcTerm (n : ℕ) : ℝ := (pcBit n : ℝ) / 2 ^ n

/-- The prime constant `Σ_{n prime} 2^(−n)`. -/
noncomputable def primeConstantReal : ℝ := ∑' n : ℕ, pcTerm n

theorem pcTerm_nonneg (n : ℕ) : 0 ≤ pcTerm n := by unfold pcTerm; positivity

theorem pcTerm_le (n : ℕ) : pcTerm n ≤ 1 / 2 ^ n := by
  unfold pcTerm
  have h' : (pcBit n : ℝ) ≤ 1 := by exact_mod_cast pcBit_le_one n
  exact div_le_div_of_nonneg_right h' (by positivity)

theorem summable_pcTerm_shift (K : ℕ) : Summable fun n => pcTerm (n + K) := by
  apply Summable.of_nonneg_of_le (fun n => pcTerm_nonneg _) _ summable_geometric_two
  intro n
  have h1 := pcTerm_le (n + K)
  have h2 : (1 : ℝ) / 2 ^ (n + K) ≤ (1 / 2) ^ n := by
    rw [one_div_pow]
    gcongr
    · norm_num
    · omega
  exact h1.trans h2

theorem summable_pcTerm : Summable pcTerm := by
  simpa using summable_pcTerm_shift 0

/-- The partial sum of `E + 1` terms is the integer of the first bits over `2^E`. -/
theorem sum_pcTerm (E : ℕ) :
    ∑ n ∈ Finset.range (E + 1), pcTerm n
      = ((∑ n ∈ Finset.range (E + 1), pcBit n * 2 ^ (E - n) : ℕ) : ℝ) / 2 ^ E := by
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  unfold pcTerm
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add]
  congr 2
  omega

/-- The tail after `E + 1` terms lies strictly between `0` and `2^-E`: there are primes and
composites beyond every bound. -/
theorem tail_bounds' (E : ℕ) :
    0 < ∑' n, pcTerm (n + (E + 1)) ∧ ∑' n, pcTerm (n + (E + 1)) < 1 / 2 ^ E := by
  constructor
  · obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (E + 1)
    have hi : pcTerm (q - (E + 1) + (E + 1)) = 1 / 2 ^ q := by
      unfold pcTerm pcBit
      rw [Nat.sub_add_cancel hq, ite_eq_left hqp]
      simp
    calc (0 : ℝ) < 1 / 2 ^ q := by positivity
      _ = pcTerm (q - (E + 1) + (E + 1)) := hi.symm
      _ ≤ ∑' n, pcTerm (n + (E + 1)) :=
        (summable_pcTerm_shift (E + 1)).le_tsum _ (fun j _ => pcTerm_nonneg _)
  · have hsum : ∑' n : ℕ, (1 : ℝ) / 2 ^ E / 2 / 2 ^ n = 1 / 2 ^ E := tsum_geometric_two' _
    rw [← hsum]
    apply Summable.tsum_lt_tsum (i := 3 * (E + 1)) _ _ (summable_pcTerm_shift (E + 1))
      (summable_geometric_two' _)
    · intro n
      have := pcTerm_le (n + (E + 1))
      calc pcTerm (n + (E + 1)) ≤ 1 / 2 ^ (n + (E + 1)) := this
        _ = 1 / 2 ^ E / 2 / 2 ^ n := by
          rw [pow_add, pow_succ]
          field_simp
    · have hcomp : ¬ Nat.Prime (3 * (E + 1) + (E + 1)) := by
        rw [show 3 * (E + 1) + (E + 1) = 2 * (2 * (E + 1)) by ring]
        exact Nat.not_prime_mul (by norm_num) (by omega)
      have hzero : pcTerm (3 * (E + 1) + (E + 1)) = 0 := by
        unfold pcTerm pcBit
        rw [ite_eq_right hcomp]
        simp
      rw [hzero]
      positivity

/-- `ρ · 2^E` is the integer of the first bits plus a tail in `(0, 1)`. -/
theorem primeConstantReal_mul_two_pow (E : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      primeConstantReal * 2 ^ E
        = ((∑ n ∈ Finset.range (E + 1), pcBit n * 2 ^ (E - n) : ℕ) : ℝ) + θ := by
  obtain ⟨hlo, hhi⟩ := tail_bounds' E
  refine ⟨(∑' n, pcTerm (n + (E + 1))) * 2 ^ E, by positivity, ?_, ?_⟩
  · have := mul_lt_mul_of_pos_right hhi (by positivity : (0 : ℝ) < 2 ^ E)
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  · unfold primeConstantReal
    rw [← summable_pcTerm.sum_add_tsum_nat_add (E + 1), sum_pcTerm, add_mul,
      div_mul_cancel₀ _ (by positivity)]

/-- `1/4 < ρ < 1/2`. -/
theorem primeConstantReal_bounds : 1 / 4 < primeConstantReal ∧ primeConstantReal < 1 / 2 := by
  obtain ⟨θ, hθ0, hθ1, h⟩ := primeConstantReal_mul_two_pow 2
  have hsum : (∑ n ∈ Finset.range (2 + 1), pcBit n * 2 ^ (2 - n) : ℕ) = 1 := by
    simp [Finset.sum_range_succ, pcBit, Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two]
  rw [hsum] at h
  push_cast at h
  constructor <;> nlinarith

/-! ### The lift -/

/-- The prime constant is the lift of its value. -/
theorem primeConstantPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    primeConstantPrecRound p mode = liftVal₀ (some ((primeConstantReal : ℝ) : EReal)) p mode := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  unfold primeConstantPrecRound liftVal₀
  rw [ite_eq_right hp.ne']
  simp only
  set N := (p + 2) / 64 + 1 with hN
  have hK : p + 2 < 64 * N := by omega
  set s := 64 * N - (p + 2) with hs
  set ρ := primeConstantReal with hρ
  obtain ⟨hρlo, hρhi⟩ := primeConstantReal_bounds
  obtain ⟨θ, hθ0, hθ1, hX⟩ := primeConstantReal_mul_two_pow (64 * N)
  rw [← toNat_primeConstantLimbs N] at hX
  set X := (primeConstantLimbs N).toNat with hXdef
  set Y := X / 2 ^ s with hY
  have hYeq : ((primeConstantLimbs N).shiftRight s).toNat = Y := by
    rw [AzNat.toNat_shiftRight]
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
  have hρp2 : ρ * 2 ^ (p + 2) = Y + θ' := by
    have h64 : (2 : ℝ) ^ (64 * N) = 2 ^ (p + 2) * 2 ^ s := by
      rw [← pow_add]; congr 1; omega
    have := hX
    rw [h64, ← mul_assoc, hXY] at this
    rw [hθ']
    field_simp
    linarith
  set m := Y / 2 with hm
  have hmeq : ((primeConstantLimbs N).shiftRight s |>.shiftRight 1).toNat = m := by
    rw [AzNat.toNat_shiftRight, hYeq, pow_one]
  set r := Y % 2 with hr2
  have hYm : (Y : ℝ) = 2 * m + r := by
    rw [hm, hr2]; exact_mod_cast (Nat.div_add_mod Y 2).symm
  have hr1 : r < 2 := Nat.mod_lt _ two_pos
  set y : ℝ := ρ * 2 ^ (p + 1) with hy
  have hy2 : y = m + ((r : ℝ) + θ') / 2 := by
    have : y * 2 = Y + θ' := by rw [hy, mul_assoc, ← pow_succ]; exact hρp2
    rw [hYm] at this
    linarith
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hlo : (m : ℝ) ≤ y := by
    rw [hy2]
    linarith
  have hhi : y < m + 1 := by
    rw [hy2]
    have : (r : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hr1
    linarith
  have hex : false = true ↔ y = (m : ℝ) := by
    constructor
    · intro h; exact absurd h (by simp)
    · intro h
      rw [hy2] at h
      linarith
  have hodd : ((primeConstantLimbs N).shiftRight s).isOdd = true ↔ r = 1 := by
    rw [AzNat.isOdd_iff, hYeq, Nat.odd_iff]
  have hmid : (if ((primeConstantLimbs N).shiftRight s).isOdd then Ordering.gt else Ordering.lt)
      = compare y ((m : ℝ) + 1 / 2) := by
    by_cases hodd' : ((primeConstantLimbs N).shiftRight s).isOdd = true
    · have hr1' : r = 1 := hodd.mp hodd'
      have hgt : (m : ℝ) + 1 / 2 < y := by
        rw [hy2, hr1']
        push_cast
        linarith
      rw [ite_eq_left hodd', eq_comm, compare_gt_iff_gt]
      exact hgt
    · have hr0' : r = 0 := by
        have : r ≠ 1 := fun h => hodd' (hodd.mpr h)
        omega
      have hlt : y < (m : ℝ) + 1 / 2 := by
        rw [hy2, hr0']
        push_cast
        linarith
      rw [ite_eq_right hodd', eq_comm, compare_lt_iff_lt]
      exact hlt
  obtain ⟨hR, htag⟩ := roundFromFloor_spec y
    ((primeConstantLimbs N).shiftRight s |>.shiftRight 1)
    false (if ((primeConstantLimbs N).shiftRight s).isOdd then Ordering.gt else Ordering.lt) mode
    (by rw [hmeq]; exact hlo) (by rw [hmeq]; exact hhi) (by rw [hmeq]; exact hex)
    (by rw [hmeq]; exact hmid)
  set ro := roundFromFloor ((primeConstantLimbs N).shiftRight s |>.shiftRight 1) false
    (if ((primeConstantLimbs N).shiftRight s).isOdd then Ordering.gt else Ordering.lt) mode
    with hro
  clear_value ro
  have hρ0 : ρ ≠ 0 := by linarith
  have hρabs : |ρ| = ρ := abs_of_pos (by linarith)
  have hlog : Int.log 2 |ρ| = -2 := by
    rw [hρabs]
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
  have hscale : precScale 2 p ρ = (2 : ℝ) ^ (-((p : ℤ) + 1)) := by
    unfold precScale
    rw [hlog]
    push_cast
    congr 1
    ring
  have h2w : (0 : ℝ) < (2 : ℝ) ^ (-((p : ℤ) + 1)) := zpow_pos (by norm_num) _
  have hyρ : ρ / (2 : ℝ) ^ (-((p : ℤ) + 1)) = y := by
    rw [hy, zpow_neg, div_inv_eq_mul, show ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
  have hround : (round (floatSet p) mode ρ).val
      = ((((AzInt.mkNorm true ro.1).toInt : ℝ) * 2 ^ (-((p : ℤ) + 1)) : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode ρ hρ0, hscale, hyρ, hR,
      AzInt.toInt_mkNorm_true]
  have h2p : (0 : ℝ) < 2 ^ (p + 1) := by positivity
  have hylo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ y := by
    rw [hy, show ((p : ℤ) - 1) = (p + 1 : ℕ) + (-(2 : ℤ)) by push_cast; ring,
      zpow_add₀ (by norm_num), zpow_natCast, show (2 : ℝ) ^ (-(2 : ℤ)) = 1 / 4 by norm_num]
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
  · exact toVal_injective p (ofEReal_spec p mode ρ).1 (Or.inl hRprec)
      (by rw [fst_roundVal, ofVal_some, (ofEReal_spec p mode ρ).2, hround, hRval])
  · show (roundVal p mode (some (ρ : EReal))).2 = ro.2
    rw [(roundVal_coe p mode ρ).2, hround, compare_coe_coe, htag, AzInt.toInt_mkNorm_true,
      Int.cast_natCast, ← hyρ]
    conv_rhs => rw [← compare_mul_right_pos _ _ _ h2w, div_mul_cancel₀ _ h2w.ne']

end Azurite.AzFloat
