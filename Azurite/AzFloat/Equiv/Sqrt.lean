/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.RoundScaled
import Azurite.AzFloat.Sqrt
import Azurite.AzNat.Equiv.Square.Dispatch
import Azurite.AzNat.Equiv.SqrtRem
import Mathlib.Analysis.Real.Sqrt

/-!
# Correctness of the square root

`Spec.sqrt` is the real square root, undefined for negative values; `sqrtPrecRound_eq_liftVal`
says `sqrtPrecRound` is the lifted specification, via `sqrtCore_eq`: the integer square root with
remainder determines the floor, the exactness and the midpoint comparison that `roundFromFloor`
needs.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real square root: undefined (`NaN`) on negatives (including `−∞`), `√∞ = ∞`. -/
noncomputable def sqrt (a : EReal) : Option EReal :=
  if a < 0 then none else if a = ⊤ then some ⊤ else some ((Real.sqrt a.toReal : ℝ) : EReal)

theorem sqrt_coe (r : ℝ) (hr : 0 ≤ r) : sqrt (r : EReal) = some ((Real.sqrt r : ℝ) : EReal) := by
  unfold sqrt
  rw [ite_eq_right (not_lt.mpr (EReal.coe_nonneg.mpr hr)), ite_eq_right (EReal.coe_ne_top r),
    EReal.toReal_coe]

theorem sqrt_coe_neg (r : ℝ) (hr : r < 0) : sqrt (r : EReal) = none := by
  unfold sqrt
  rw [ite_eq_left (EReal.coe_neg'.mpr hr)]

@[simp] theorem sqrt_top : sqrt ⊤ = some ⊤ := by
  unfold sqrt
  rw [ite_eq_right (not_lt.mpr le_top), ite_eq_left rfl]

@[simp] theorem sqrt_bot : sqrt ⊥ = none := by
  unfold sqrt
  rw [ite_eq_left EReal.bot_lt_zero]

@[simp] theorem sqrt_zero : sqrt 0 = some 0 := by
  rw [← EReal.coe_zero, sqrt_coe 0 le_rfl, Real.sqrt_zero]

end Spec

/-- `compareScaled` compares `n · 2^t` with `c`. -/
theorem compareScaled_eq (n : AzNat) (t : AzInt) (c : AzNat) :
    compareScaled n t c = compare ((n.toNat : ℝ) * (2 : ℝ) ^ t.toInt) (c.toNat : ℝ) := by
  unfold compareScaled
  have habs : (t.abs.toNat : ℤ) = |t.toInt| := AzInt.abs_toNat_eq t
  by_cases hsg : t.sign = true
  · have hg0 : 0 ≤ t.toInt := (AzInt.sign_eq_true_iff t).mp hsg
    rw [ite_eq_left hsg]
    show AzNat.compare (n.shiftLeft t.abs.toNat) c = _
    rw [AzNat.compare_eq_compare_toNat, ← compare_natCast, AzNat.toNat_shiftLeft]
    push_cast
    rw [← zpow_natCast, show ((t.abs.toNat : ℕ) : ℤ) = t.toInt by rw [habs, abs_of_nonneg hg0]]
  · have hg0 : t.toInt < 0 := by
      have := (AzInt.sign_eq_true_iff t).not.mp hsg; push Not at this; exact this
    rw [ite_eq_right hsg]
    show AzNat.compare n (c.shiftLeft t.abs.toNat) = _
    rw [AzNat.compare_eq_compare_toNat, ← compare_natCast, AzNat.toNat_shiftLeft]
    push_cast
    rw [← zpow_natCast, show ((t.abs.toNat : ℕ) : ℤ) = -t.toInt by rw [habs, abs_of_neg hg0],
      zpow_neg]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ t.toInt := zpow_pos (by norm_num) _
    rcases lt_trichotomy ((n.toNat : ℝ) * (2 : ℝ) ^ t.toInt) (c.toNat : ℝ) with h | h | h
    · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr ((lt_mul_inv_iff₀ hpos).mpr h)]
    · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr ((eq_mul_inv_iff_mul_eq₀ hpos.ne').mpr h)]
    · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr ((mul_inv_lt_iff₀ hpos).mpr h)]

/-- The truncated scaling `⌊n · 2^t⌋` as computed by a shift, with exactness. -/
theorem scaled_floor (n : AzNat) (t : AzInt) :
    ((if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat).toNat : ℝ)
        ≤ (n.toNat : ℝ) * (2 : ℝ) ^ t.toInt ∧
      (n.toNat : ℝ) * (2 : ℝ) ^ t.toInt
        < ((if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat).toNat : ℝ) + 1 ∧
      ((n.toNat : ℝ) * (2 : ℝ) ^ t.toInt
          = ((if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat).toNat : ℝ) ↔
        (t.sign || n.isMultipleOfPow2 t.abs.toNat) = true) := by
  have habs : (t.abs.toNat : ℤ) = |t.toInt| := AzInt.abs_toNat_eq t
  by_cases hsg : t.sign = true
  · have hg0 : 0 ≤ t.toInt := (AzInt.sign_eq_true_iff t).mp hsg
    rw [ite_eq_left hsg, AzNat.toNat_shiftLeft, hsg, Bool.true_or]
    push_cast
    rw [← zpow_natCast, show ((t.abs.toNat : ℕ) : ℤ) = t.toInt by rw [habs, abs_of_nonneg hg0]]
    exact ⟨le_rfl, by linarith, by simp⟩
  · have hg0 : t.toInt < 0 := by
      have := (AzInt.sign_eq_true_iff t).not.mp hsg; push Not at this; exact this
    have hsf : t.sign = false := by simpa using hsg
    rw [ite_eq_right hsg, AzNat.toNat_shiftRight, hsf, Bool.false_or,
      AzNat.isMultipleOfPow2_eq, decide_eq_true_eq]
    set k := t.abs.toNat with hk
    have hkI : (k : ℤ) = -t.toInt := by rw [hk, habs, abs_of_neg hg0]
    have h2k : (2 : ℝ) ^ t.toInt = ((2 ^ k : ℕ) : ℝ)⁻¹ := by
      push_cast
      rw [← zpow_natCast, hkI, zpow_neg, inv_inv]
    have hpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hdiv := Nat.div_add_mod n.toNat (2 ^ k)
    have hmod := Nat.mod_lt n.toNat (by positivity : 0 < 2 ^ k)
    rw [h2k]
    set Q := n.toNat / 2 ^ k with hQ
    set R := n.toNat % 2 ^ k with hR
    have hn : (n.toNat : ℝ) = (2 ^ k : ℕ) * Q + R := by exact_mod_cast hdiv.symm
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have hRlt : (R : ℝ) < (2 ^ k : ℕ) := by exact_mod_cast hmod
    refine ⟨?_, ?_, ?_⟩
    · rw [hn, le_mul_inv_iff₀ hpos]; nlinarith
    · rw [hn, mul_inv_lt_iff₀ hpos]; nlinarith
    · constructor
      · intro h
        rw [hn, mul_inv_eq_iff_eq_mul₀ hpos.ne'] at h
        have : (R : ℝ) = 0 := by linarith
        have hR0' : R = 0 := by exact_mod_cast this
        exact Nat.dvd_of_mod_eq_zero hR0'
      · intro h
        have hR0' : R = 0 := by rw [hR]; exact Nat.mod_eq_zero_of_dvd h
        rw [hn, hR0', Nat.cast_zero, add_zero, mul_comm, inv_mul_cancel_left₀ hpos.ne']

/-- The square root of the exact value of a float at the right scale. -/
theorem sqrtCore_eq (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    sqrtCore e (coreSignificand q m) q p mode
      = roundVal p mode
          (some ((Real.sqrt (finiteVal true e (coreSignificand q m)) : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  set n := coreSignificand q m with hn
  have hn0 : n ≠ 0 := coreSignificand_ne_zero hv
  have hs : n.size = q := size_coreSignificand hv
  clear_value n
  have hb : (2 : ℝ) ^ ((q : ℤ) - 1) ≤ (n.toNat : ℝ) ∧ (n.toNat : ℝ) < (2 : ℝ) ^ (q : ℤ) := by
    obtain ⟨hlo, hhi⟩ := toNat_bounds_of_ne_zero n hn0
    rw [hs] at hlo hhi
    have hq : 0 < q := hv.pos
    constructor
    · rw [show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hlo
    · rw [zpow_natCast]; exact_mod_cast hhi
  set N : ℝ := (n.toNat : ℝ) with hN
  clear_value N
  have hNpos : 0 < N := lt_of_lt_of_le (zpow_pos (by norm_num) _) hb.1
  unfold sqrtCore
  simp only []
  -- the parity of the exponent
  set δ : ℕ := if e.isOdd then 1 else 0 with hδ_def
  have hδ : (δ : ℤ) % 2 = e.toInt % 2 := by
    rw [hδ_def]
    rcases Int.even_or_odd e.toInt with h | h
    · have : e.isOdd = false := by
        cases hi : e.isOdd
        · rfl
        · exact absurd ((AzInt.isOdd_iff e).mp hi) (Int.not_odd_iff_even.mpr h)
      rw [this]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
      rw [Int.even_iff] at h; omega
    · rw [(AzInt.isOdd_iff e).mpr h]; simp only [↓reduceIte, Nat.cast_one]
      rw [Int.odd_iff] at h; omega
  have hδle : δ ≤ 1 := by rw [hδ_def]; split_ifs <;> omega
  clear_value δ
  -- the shift `t` and the exponent `w`
  set t : AzInt := (AzNat.ofNat (2 * p)).toAzInt - (AzNat.ofNat (q + δ)).toAzInt with ht_def
  have htI : t.toInt = 2 * (p : ℤ) - q - δ := by
    rw [ht_def, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat]; push_cast; ring
  clear_value t
  set w' : AzInt := e - (AzNat.ofNat (2 * p)).toAzInt + (AzNat.ofNat δ).toAzInt with hw'_def
  have hw'I : w'.toInt = e.toInt - 2 * p + δ := by
    rw [hw'_def, AzInt.toInt_add, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat]; push_cast; ring
  clear_value w'
  set w := w'.shiftRight 1 with hw_def
  have hwI : 2 * w.toInt = w'.toInt := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, w'.toInt = 2 * k := by
      refine ⟨w'.toInt / 2, ?_⟩
      have : w'.toInt % 2 = 0 := by rw [hw'I]; omega
      omega
    have h := AzInt.toInt_shiftRight w' 1
    rw [pow_one, hk, ← hw_def] at h
    have h2 : toInt (round intSet .Floor (((2 * k : ℤ) : ℝ) / 2)) = w.toInt := toInt_eq_of_val h
    rw [show toInt (round intSet .Floor (((2 * k : ℤ) : ℝ) / 2)) = ⌊((2 * k : ℤ) : ℝ) / 2⌋ from
      toInt_eq_of_val (val_roundFloor_intSet _).symm] at h2
    rw [show ((2 * k : ℤ) : ℝ) / 2 = (k : ℝ) by push_cast; ring, Int.floor_intCast] at h2
    rw [hk, ← h2]
  clear_value w
  have htw : t.toInt + 2 * w.toInt = e.toInt - q := by rw [hwI, hw'I, htI]; ring
  -- the scaled significand `M = N · 2^t` and its truncation
  set Mr : ℝ := N * (2 : ℝ) ^ t.toInt with hMr
  have hMr0 : 0 < Mr := by positivity
  obtain ⟨hMle, hMlt, hMex⟩ := scaled_floor n t
  rw [← hN] at hMle hMlt hMex
  set M := if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat with hM_def
  clear_value M
  rw [← hMr] at hMle hMlt hMex
  -- bounds on `M`: `2^(2p−2) ≤ Mr < 2^(2p)`
  have hMlo : (2 : ℝ) ^ (2 * (p : ℤ) - 2) ≤ Mr := by
    rw [hMr, htI]
    calc (2 : ℝ) ^ (2 * (p : ℤ) - 2) ≤ 2 ^ ((q : ℤ) - 1) * 2 ^ (2 * (p : ℤ) - q - δ) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ ≤ N * 2 ^ (2 * (p : ℤ) - q - δ) :=
          mul_le_mul_of_nonneg_right hb.1 (zpow_pos (by norm_num) _).le
  have hMhi : Mr < (2 : ℝ) ^ (2 * (p : ℤ)) := by
    rw [hMr, htI]
    calc N * 2 ^ (2 * (p : ℤ) - q - δ) < 2 ^ (q : ℤ) * 2 ^ (2 * (p : ℤ) - q - δ) :=
          mul_lt_mul_of_pos_right hb.2 (zpow_pos (by norm_num) _)
      _ ≤ 2 ^ (2 * (p : ℤ)) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  -- the integer square root
  set sr := AzNat.sqrtRem M with hsr
  clear_value sr
  have hsN : sr.1.toNat = Nat.sqrt M.toNat := by rw [hsr]; exact AzNat.toNat_sqrtRem_fst M
  have hrN : sr.2.toNat = M.toNat - Nat.sqrt M.toNat * Nat.sqrt M.toNat := by
    rw [hsr]; exact AzNat.toNat_sqrtRem_snd M
  set y : ℝ := Real.sqrt Mr with hy_def
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hsq_le : Nat.sqrt M.toNat ^ 2 ≤ M.toNat := Nat.sqrt_le' _
  have hlt_sq : M.toNat < (Nat.sqrt M.toNat + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hlo : (sr.1.toNat : ℝ) ≤ y := by
    rw [hsN, hy_def]
    exact le_trans Real.nat_sqrt_le_real_sqrt (Real.sqrt_le_sqrt hMle)
  have hhi : y < sr.1.toNat + 1 := by
    rw [hsN, hy_def]
    calc Real.sqrt Mr < Real.sqrt (M.toNat + 1) := Real.sqrt_lt_sqrt hMr0.le hMlt
      _ ≤ Nat.sqrt M.toNat + 1 := by
          rw [Real.sqrt_le_left (by positivity)]
          exact_mod_cast hlt_sq
  have hex : (decide (sr.2 = 0) && (t.sign || n.isMultipleOfPow2 t.abs.toNat)) = true ↔
      y = sr.1.toNat := by
    rw [Bool.and_eq_true, decide_eq_true_eq, ← hMex, hsN, hy_def,
      Real.sqrt_eq_iff_eq_sq hMr0.le (Nat.cast_nonneg _)]
    constructor
    · rintro ⟨hr, hM⟩
      have hr' : sr.2.toNat = 0 := by rw [hr]; rfl
      rw [hrN] at hr'
      have hM2 : M.toNat = Nat.sqrt M.toNat * Nat.sqrt M.toNat := by
        have := Nat.sqrt_le M.toNat; omega
      have hMs : (M.toNat : ℝ) = (Nat.sqrt M.toNat : ℝ) ^ 2 := by rw [sq]; exact_mod_cast hM2
      rw [hM, hMs]
    · intro h
      have hMle' : Mr ≤ (M.toNat : ℝ) := by
        rw [h]; exact_mod_cast hsq_le
      have hMeq : Mr = (M.toNat : ℝ) := le_antisymm hMle' hMle
      refine ⟨?_, hMeq⟩
      have : (M.toNat : ℝ) = (Nat.sqrt M.toNat : ℝ) ^ 2 := by rw [← hMeq, h]
      have hM2 : M.toNat = Nat.sqrt M.toNat * Nat.sqrt M.toNat := by
        have : (M.toNat : ℝ) = ((Nat.sqrt M.toNat * Nat.sqrt M.toNat : ℕ) : ℝ) := by
          rw [this]; push_cast; ring
        exact_mod_cast this
      apply AzNat.toNat_injective
      rw [hrN, AzNat.toNat_zero]
      exact Nat.sub_eq_zero_of_le hM2.le
  have hmid : compareScaled n (t + (AzNat.ofNat 2).toAzInt)
      (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1))
      = compare y ((sr.1.toNat : ℝ) + 1 / 2) := by
    have htt : (t + (AzNat.ofNat 2).toAzInt).toInt = t.toInt + 2 := by
      rw [AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat]; push_cast; ring
    have hL : N * (2 : ℝ) ^ (t.toInt + 2) = Mr * 4 := by
      rw [hMr, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), show (2 : ℝ) ^ (2 : ℤ) = 4 by norm_num]; ring
    have hRt : ((AzNat.square ((sr.1.shiftLeft 1).addUInt64 1)).toNat : ℝ)
        = ((sr.1.toNat : ℝ) + 1 / 2) ^ 2 * 4 := by
      rw [AzNat.toNat_square, AzNat.toNat_addUInt64, AzNat.toNat_shiftLeft, UInt64.toNat_one]
      push_cast; ring
    rw [compareScaled_eq, htt, ← hN, hL, hRt, hy_def, compare_mul_right_pos _ _ _ (by norm_num)]
    have hmid_pos : (0 : ℝ) < (sr.1.toNat : ℝ) + 1 / 2 := by positivity
    rcases lt_trichotomy (Real.sqrt Mr) ((sr.1.toNat : ℝ) + 1 / 2) with h | h | h
    · rw [compare_lt_iff_lt.mpr h]
      rw [Real.sqrt_lt' hmid_pos] at h
      exact compare_lt_iff_lt.mpr h
    · rw [compare_eq_iff_eq.mpr h]
      rw [Real.sqrt_eq_iff_eq_sq hMr0.le hmid_pos.le] at h
      exact compare_eq_iff_eq.mpr h
    · rw [compare_gt_iff_gt.mpr h]
      rw [Real.lt_sqrt hmid_pos.le] at h
      exact compare_gt_iff_gt.mpr h
  obtain ⟨hR, htag⟩ := roundFromFloor_spec y sr.1 _ _ mode hlo hhi hex hmid
  set ro := roundFromFloor sr.1 (decide (sr.2 = 0) && (t.sign || n.isMultipleOfPow2 t.abs.toNat))
    (compareScaled n (t + (AzNat.ofNat 2).toAzInt)
      (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1))) mode with hro
  clear_value ro
  -- the exact value and its logarithm
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w.toInt := zpow_pos (by norm_num) _
  set v : ℝ := Real.sqrt (finiteVal true e n) with hv_def
  have hv : v = y * (2 : ℝ) ^ w.toInt := by
    rw [hv_def, hy_def, finiteVal_true_eq, hs, ← hN, ← htw, zpow_add₀ (by norm_num),
      show (2 : ℝ) ^ (2 * w.toInt) = (2 ^ w.toInt) ^ 2 by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring,
      ← mul_assoc, ← hMr, Real.sqrt_mul hMr0.le, Real.sqrt_sq h2w.le]
  clear_value v
  have hylo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ y := by
    rw [hy_def, Real.le_sqrt (zpow_pos (by norm_num) _).le hMr0.le, ← zpow_natCast, ← zpow_mul]
    convert hMlo using 2; push_cast; ring
  have hyhi : y < (2 : ℝ) ^ (p : ℤ) := by
    rw [hy_def, Real.sqrt_lt' (zpow_pos (by norm_num) _), ← zpow_natCast, ← zpow_mul]
    convert hMhi using 2; push_cast; ring
  have hypos : 0 < y := lt_of_lt_of_le (zpow_pos (by norm_num) _) hylo
  have hv0 : v ≠ 0 := by rw [hv]; positivity
  have hvabs : |v| = y * (2 : ℝ) ^ w.toInt := by rw [hv, abs_of_pos (by positivity)]
  have hvpos : 0 < |v| := by rw [hvabs]; positivity
  have hlog : Int.log 2 |v| = w.toInt + p - 1 := by
    apply le_antisymm
    · have h := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hvpos).mp (by
        rw [hvabs, zpow_add₀ (by norm_num), mul_comm]
        exact mul_lt_mul_of_pos_left hyhi h2w)
      omega
    · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hvpos).mp (by
        rw [hvabs, show w.toInt + p - 1 = ((p : ℤ) - 1) + w.toInt by ring, zpow_add₀ (by norm_num)]
        exact mul_le_mul_of_nonneg_right hylo h2w.le)
  have hscale : precScale 2 p v = (2 : ℝ) ^ w.toInt := by
    unfold precScale
    rw [hlog]
    push_cast
    congr 1
    ring
  have hyv : v / (2 : ℝ) ^ w.toInt = y := by rw [hv, mul_div_cancel_right₀ _ h2w.ne']
  have hround : (round (floatSet p) mode v).val
      = ((((AzInt.mkNorm true ro.1).toInt : ℝ) * 2 ^ w.toInt : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode v hv0, hscale, hyv, hR,
      AzInt.toInt_mkNorm_true]
  -- bounds on the rounded integer
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
  obtain ⟨hRval, hRprec⟩ := normalizeCarry_spec (AzInt.mkNorm true ro.1) p hp
    (w + (AzNat.ofNat p).toAzInt) hlo' hhi'
  have hep : (w + (AzNat.ofNat p).toAzInt).toInt - p = w.toInt := by
    rw [AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat]; ring
  rw [hep] at hRval
  symm
  refine Prod.ext ?_ ?_
  · have hgoal : (roundVal p mode (some (v : EReal))).1
        = normalizeCarry (AzInt.mkNorm true ro.1) (w + (AzNat.ofNat p).toAzInt) p :=
      toVal_injective p (ofEReal_spec p mode v).1 (Or.inl hRprec)
        (by rw [fst_roundVal, ofVal_some, (ofEReal_spec p mode v).2, hround, hRval])
    exact hgoal
  · show (roundVal p mode (some (v : EReal))).2 = ro.2
    rw [(roundVal_coe p mode v).2, hround, compare_coe_coe, htag, AzInt.toInt_mkNorm_true,
      Int.cast_natCast, hv, compare_mul_right_pos _ _ _ h2w]

/-- Square root is the float lift of `Spec.sqrt`. -/
theorem sqrtPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrtPrecRound x p mode = liftVal Spec.sqrt x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [sqrtPrecRound]
  | zero => simp [sqrtPrecRound]
  | finite s e q m hv =>
    cases s with
    | true =>
      simp only [sqrtPrecRound, toVal_finite, Option.bind_some, ↓reduceIte]
      rw [finiteVal_eq_core true e hv,
        Spec.sqrt_coe _ (finiteVal_true_pos' e _ (coreSignificand_ne_zero hv)).le,
        sqrtCore_eq e hv p mode]
    | false =>
      simp only [sqrtPrecRound, toVal_finite, Option.bind_some, Bool.false_eq_true, ↓reduceIte]
      rw [finiteVal_eq_core false e hv, finiteVal_false,
        Spec.sqrt_coe_neg _ (neg_neg_iff_pos.mpr
          (finiteVal_true_pos' e _ (coreSignificand_ne_zero hv))), roundVal_none]

end Azurite.AzFloat
