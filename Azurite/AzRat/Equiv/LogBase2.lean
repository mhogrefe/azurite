/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.LogBase2
import Azurite.AzRat.Parse
import Azurite.AzRat.Equiv.Basic
import Azurite.AzRat.Equiv.Pow2
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzNat.Equiv.Pow2
import Azurite.AzInt.Equiv.Sub
import Azurite.AzInt.Instances
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.NormalizedCompare
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Correctness of `AzRat.floorLogBase2Abs` / `ceilingLogBase2Abs`

`floorLogBase2Abs q = ⌊logb 2 |toRat q|⌋` and `ceilingLogBase2Abs q = ⌈logb 2 |toRat q|⌉`
for `q` with nonzero numerator.

The boundary comparison is justified directly from `AzNat.normalizedCompare_eq_cross` (the
allocation-free comparison).
-/

open Real

namespace Azurite.AzRat

/-- `Nat.size N` straddles `logb 2 N`: `size N - 1 ≤ logb 2 N < size N`. -/
private lemma size_bounds (N : ℕ) (hN : N > 0) :
    ((Nat.size N - 1 : ℕ) : ℝ) ≤ logb 2 (N : ℝ) ∧ logb 2 (N : ℝ) < (Nat.size N : ℝ) := by
  have hl1 : 2 ^ (Nat.size N - 1) ≤ N := Nat.lt_size.mp (Nat.pred_lt (Nat.size_pos.mpr hN).ne')
  have hl2 : N < 2 ^ Nat.size N := Nat.size_le.mp (le_refl _)
  have h_base : (1 : ℝ) < 2 := by norm_num
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  constructor
  · have hcast1 : (2 : ℝ) ^ (Nat.size N - 1) ≤ (N : ℝ) := by exact_mod_cast hl1
    have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.size N - 1) := by positivity
    have hlog1 : logb 2 ((2 : ℝ) ^ (Nat.size N - 1)) ≤ logb 2 (N : ℝ) :=
      (logb_le_logb h_base h_pow_pos hN_pos).mpr hcast1
    have h_simp : logb 2 ((2 : ℝ) ^ (Nat.size N - 1)) = ((Nat.size N - 1 : ℕ) : ℝ) := by
      rw [logb_pow, logb_self_eq_one h_base, mul_one]
    rwa [h_simp] at hlog1
  · have hcast2 : (N : ℝ) < (2 : ℝ) ^ Nat.size N := by exact_mod_cast hl2
    have hN_pow_pos : (0 : ℝ) < (2 : ℝ) ^ Nat.size N := by positivity
    have hlog2 : logb 2 (N : ℝ) < logb 2 ((2 : ℝ) ^ Nat.size N) :=
      (logb_lt_logb_iff h_base hN_pos hN_pow_pos).mpr hcast2
    have h_simp : logb 2 ((2 : ℝ) ^ Nat.size N) = (Nat.size N : ℝ) := by
      rw [logb_pow, logb_self_eq_one h_base, mul_one]
    rwa [h_simp] at hlog2

/-- `normalizedCompare` equals the comparison of the size-normalized real fractions. -/
private lemma normalizedCompare_eq_realFrac (x y : AzNat) (hx : 0 < x.toNat) (hy : 0 < y.toNat) :
    AzNat.normalizedCompare x y =
      compare ((x.toNat : ℝ) / 2 ^ x.size) ((y.toNat : ℝ) / 2 ^ y.size) := by
  rw [AzNat.normalizedCompare_eq_cross x y hx hy]
  have hsx : (0 : ℝ) < 2 ^ x.size := by positivity
  have hsy : (0 : ℝ) < 2 ^ y.size := by positivity
  have ordNat : Ord.compare (x.toNat * 2 ^ y.size) (y.toNat * 2 ^ x.size) =
      if x.toNat * 2 ^ y.size < y.toNat * 2 ^ x.size then Ordering.lt
      else if x.toNat * 2 ^ y.size = y.toNat * 2 ^ x.size then Ordering.eq
      else Ordering.gt := rfl
  rw [ordNat]
  rcases lt_trichotomy (x.toNat * 2 ^ y.size) (y.toNat * 2 ^ x.size) with h | h | h
  · rw [ite_eq_left h]
    have hf : (x.toNat : ℝ) / 2 ^ x.size < (y.toNat : ℝ) / 2 ^ y.size := by
      rw [div_lt_div_iff₀ hsx hsy]; exact_mod_cast h
    exact (compare_lt_iff_lt.mpr hf).symm
  · rw [ite_eq_right (by omega), ite_eq_left h]
    have hf : (x.toNat : ℝ) / 2 ^ x.size = (y.toNat : ℝ) / 2 ^ y.size := by
      rw [div_eq_div_iff hsx.ne' hsy.ne']; exact_mod_cast h
    exact (compare_eq_iff_eq.mpr hf).symm
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hf : (y.toNat : ℝ) / 2 ^ y.size < (x.toNat : ℝ) / 2 ^ x.size := by
      rw [div_lt_div_iff₀ hsy hsx]; exact_mod_cast h
    exact (compare_gt_iff_gt.mpr hf).symm

/-- `logb 2` of the size-normalized fraction. -/
private lemma logb_frac (x : AzNat) (hx : 0 < x.toNat) :
    logb 2 ((x.toNat : ℝ) / 2 ^ x.size) = logb 2 (x.toNat : ℝ) - (x.size : ℝ) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hxr : (x.toNat : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [logb_div hxr (by positivity), logb_pow, logb_self_eq_one hb, mul_one]

private lemma logb_diff_lt (x y : AzNat) (hx : 0 < x.toNat) (hy : 0 < y.toNat)
    (h : AzNat.normalizedCompare x y = Ordering.lt) :
    logb 2 (x.toNat : ℝ) - logb 2 (y.toNat : ℝ) < (x.size : ℝ) - (y.size : ℝ) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hpx : (0 : ℝ) < (x.toNat : ℝ) / 2 ^ x.size := div_pos (by exact_mod_cast hx) (by positivity)
  have hpy : (0 : ℝ) < (y.toNat : ℝ) / 2 ^ y.size := div_pos (by exact_mod_cast hy) (by positivity)
  have hc := normalizedCompare_eq_realFrac x y hx hy
  rw [h] at hc
  have hf : (x.toNat : ℝ) / 2 ^ x.size < (y.toNat : ℝ) / 2 ^ y.size := compare_lt_iff_lt.mp hc.symm
  have := (logb_lt_logb_iff hb hpx hpy).mpr hf
  rw [logb_frac x hx, logb_frac y hy] at this
  linarith

private lemma logb_diff_ge (x y : AzNat) (hx : 0 < x.toNat) (hy : 0 < y.toNat)
    (h : AzNat.normalizedCompare x y ≠ Ordering.lt) :
    (x.size : ℝ) - (y.size : ℝ) ≤ logb 2 (x.toNat : ℝ) - logb 2 (y.toNat : ℝ) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hpx : (0 : ℝ) < (x.toNat : ℝ) / 2 ^ x.size := div_pos (by exact_mod_cast hx) (by positivity)
  have hpy : (0 : ℝ) < (y.toNat : ℝ) / 2 ^ y.size := div_pos (by exact_mod_cast hy) (by positivity)
  have hc := normalizedCompare_eq_realFrac x y hx hy
  have hcne : compare ((x.toNat : ℝ) / 2 ^ x.size) ((y.toNat : ℝ) / 2 ^ y.size) ≠ Ordering.lt :=
    hc ▸ h
  have hf : (y.toNat : ℝ) / 2 ^ y.size ≤ (x.toNat : ℝ) / 2 ^ x.size :=
    not_lt.mp (fun hlt => hcne (compare_lt_iff_lt.mpr hlt))
  have := (logb_le_logb hb hpy hpx).mpr hf
  rw [logb_frac x hx, logb_frac y hy] at this
  linarith

private lemma logb_diff_gt (x y : AzNat) (hx : 0 < x.toNat) (hy : 0 < y.toNat)
    (h : AzNat.normalizedCompare x y = Ordering.gt) :
    (x.size : ℝ) - (y.size : ℝ) < logb 2 (x.toNat : ℝ) - logb 2 (y.toNat : ℝ) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hpx : (0 : ℝ) < (x.toNat : ℝ) / 2 ^ x.size := div_pos (by exact_mod_cast hx) (by positivity)
  have hpy : (0 : ℝ) < (y.toNat : ℝ) / 2 ^ y.size := div_pos (by exact_mod_cast hy) (by positivity)
  have hc := normalizedCompare_eq_realFrac x y hx hy
  rw [h] at hc
  have hf : (y.toNat : ℝ) / 2 ^ y.size < (x.toNat : ℝ) / 2 ^ x.size := compare_gt_iff_gt.mp hc.symm
  have := (logb_lt_logb_iff hb hpy hpx).mpr hf
  rw [logb_frac x hx, logb_frac y hy] at this
  linarith

private lemma logb_diff_le (x y : AzNat) (hx : 0 < x.toNat) (hy : 0 < y.toNat)
    (h : AzNat.normalizedCompare x y ≠ Ordering.gt) :
    logb 2 (x.toNat : ℝ) - logb 2 (y.toNat : ℝ) ≤ (x.size : ℝ) - (y.size : ℝ) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hpx : (0 : ℝ) < (x.toNat : ℝ) / 2 ^ x.size := div_pos (by exact_mod_cast hx) (by positivity)
  have hpy : (0 : ℝ) < (y.toNat : ℝ) / 2 ^ y.size := div_pos (by exact_mod_cast hy) (by positivity)
  have hc := normalizedCompare_eq_realFrac x y hx hy
  have hcne : compare ((x.toNat : ℝ) / 2 ^ x.size) ((y.toNat : ℝ) / 2 ^ y.size) ≠ Ordering.gt :=
    hc ▸ h
  have hf : (x.toNat : ℝ) / 2 ^ x.size ≤ (y.toNat : ℝ) / 2 ^ y.size :=
    not_lt.mp (fun hlt => hcne (compare_gt_iff_gt.mpr hlt))
  have := (logb_le_logb hb hpx hpy).mpr hf
  rw [logb_frac x hx, logb_frac y hy] at this
  linarith

/-- Shared setup for both correctness proofs: positivity, `|toRat q|`, and the size casts. -/
private lemma logb_abs_setup (q : AzRat) (hq : q.num ≠ 0) :
    0 < q.num.toNat ∧ 0 < q.den.toNat ∧
    logb 2 |(AzRat.toRat q : ℝ)| = logb 2 (q.num.toNat : ℝ) - logb 2 (q.den.toNat : ℝ) := by
  have hN : 0 < q.num.toNat :=
    Nat.pos_of_ne_zero (fun h => hq (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)))
  have hD : 0 < q.den.toNat :=
    Nat.pos_of_ne_zero (fun h => q.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)))
  refine ⟨hN, hD, ?_⟩
  have hN_pos : (0 : ℝ) < q.num.toNat := by exact_mod_cast hN
  have hD_pos : (0 : ℝ) < q.den.toNat := by exact_mod_cast hD
  have hnum : (AzRat.toRat q).num = if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ) := rfl
  have hden : (AzRat.toRat q).den = q.den.toNat := rfl
  have h_abs : |(AzRat.toRat q : ℝ)| = (q.num.toNat : ℝ) / (q.den.toNat : ℝ) := by
    rw [Rat.cast_def, abs_div, hnum, hden]
    congr 1
    · cases q.sign <;> push_cast <;> simp
    · exact abs_of_nonneg (by positivity)
  rw [h_abs, logb_div hN_pos.ne' hD_pos.ne']

lemma floorLogBase2Abs_eq (q : AzRat) (hq : q.num ≠ 0) :
    floorLogBase2Abs q = ⌊logb 2 |(AzRat.toRat q : ℝ)|⌋ := by
  obtain ⟨hN, hD, h_log_div⟩ := logb_abs_setup q hq
  have h_exp : (floorLogBase2Abs q : ℝ) =
      if AzNat.normalizedCompare q.num q.den == Ordering.lt then
        (q.num.size : ℝ) - (q.den.size : ℝ) - 1
      else
        (q.num.size : ℝ) - (q.den.size : ℝ) := by
    unfold floorLogBase2Abs
    split_ifs <;> push_cast <;> ring
  have h_floor_iff : ⌊logb 2 |(AzRat.toRat q : ℝ)|⌋ = floorLogBase2Abs q ↔
      (floorLogBase2Abs q : ℝ) ≤ logb 2 |(AzRat.toRat q : ℝ)| ∧
        logb 2 |(AzRat.toRat q : ℝ)| < (floorLogBase2Abs q : ℝ) + 1 :=
    Int.floor_eq_iff (z := floorLogBase2Abs q) (a := logb 2 |(AzRat.toRat q : ℝ)|)
  rw [eq_comm, h_floor_iff, h_exp, h_log_div]
  have h_sizeN := size_bounds q.num.toNat hN
  have h_sizeD := size_bounds q.den.toNat hD
  rw [AzNat.size_toNat q.num] at h_sizeN
  rw [AzNat.size_toNat q.den] at h_sizeD
  have hsN1 : 1 ≤ q.num.size := by rw [← AzNat.size_toNat]; exact Nat.size_pos.mpr hN
  have hsD1 : 1 ≤ q.den.size := by rw [← AzNat.size_toNat]; exact Nat.size_pos.mpr hD
  have hcastN : ((q.num.size - 1 : ℕ) : ℝ) = (q.num.size : ℝ) - 1 := by
    rw [Nat.cast_sub hsN1, Nat.cast_one]
  have hcastD : ((q.den.size - 1 : ℕ) : ℝ) = (q.den.size : ℝ) - 1 := by
    rw [Nat.cast_sub hsD1, Nat.cast_one]
  rw [hcastN] at h_sizeN
  rw [hcastD] at h_sizeD
  split_ifs with h_lt
  · rw [beq_iff_eq] at h_lt
    have h_cmp := logb_diff_lt q.num q.den hN hD h_lt
    exact ⟨by linarith [h_sizeN.1, h_sizeD.2], by linarith [h_cmp]⟩
  · have h_lt_ne : AzNat.normalizedCompare q.num q.den ≠ Ordering.lt := by
      intro hc; rw [hc] at h_lt; simp at h_lt
    have h_cmp := logb_diff_ge q.num q.den hN hD h_lt_ne
    exact ⟨by linarith [h_cmp], by linarith [h_sizeN.2, h_sizeD.1]⟩

lemma ceilingLogBase2Abs_eq (q : AzRat) (hq : q.num ≠ 0) :
    ceilingLogBase2Abs q = ⌈logb 2 |(AzRat.toRat q : ℝ)|⌉ := by
  obtain ⟨hN, hD, h_log_div⟩ := logb_abs_setup q hq
  have h_exp : (ceilingLogBase2Abs q : ℝ) =
      if AzNat.normalizedCompare q.num q.den == Ordering.gt then
        (q.num.size : ℝ) - (q.den.size : ℝ) + 1
      else
        (q.num.size : ℝ) - (q.den.size : ℝ) := by
    unfold ceilingLogBase2Abs
    split_ifs <;> push_cast <;> ring
  have h_ceil_iff : ⌈logb 2 |(AzRat.toRat q : ℝ)|⌉ = ceilingLogBase2Abs q ↔
      (ceilingLogBase2Abs q : ℝ) - 1 < logb 2 |(AzRat.toRat q : ℝ)| ∧
        logb 2 |(AzRat.toRat q : ℝ)| ≤ (ceilingLogBase2Abs q : ℝ) :=
    Int.ceil_eq_iff (z := ceilingLogBase2Abs q) (a := logb 2 |(AzRat.toRat q : ℝ)|)
  rw [eq_comm, h_ceil_iff, h_exp, h_log_div]
  have h_sizeN := size_bounds q.num.toNat hN
  have h_sizeD := size_bounds q.den.toNat hD
  rw [AzNat.size_toNat q.num] at h_sizeN
  rw [AzNat.size_toNat q.den] at h_sizeD
  have hsN1 : 1 ≤ q.num.size := by rw [← AzNat.size_toNat]; exact Nat.size_pos.mpr hN
  have hsD1 : 1 ≤ q.den.size := by rw [← AzNat.size_toNat]; exact Nat.size_pos.mpr hD
  have hcastN : ((q.num.size - 1 : ℕ) : ℝ) = (q.num.size : ℝ) - 1 := by
    rw [Nat.cast_sub hsN1, Nat.cast_one]
  have hcastD : ((q.den.size - 1 : ℕ) : ℝ) = (q.den.size : ℝ) - 1 := by
    rw [Nat.cast_sub hsD1, Nat.cast_one]
  rw [hcastN] at h_sizeN
  rw [hcastD] at h_sizeD
  split_ifs with h_gt
  · rw [beq_iff_eq] at h_gt
    have h_cmp := logb_diff_gt q.num q.den hN hD h_gt
    exact ⟨by linarith [h_cmp], by linarith [h_sizeN.2, h_sizeD.1]⟩
  · have h_gt_ne : AzNat.normalizedCompare q.num q.den ≠ Ordering.gt := by
      intro hc; rw [hc] at h_gt; simp at h_gt
    have h_cmp := logb_diff_le q.num q.den hN hD h_gt_ne
    exact ⟨by linarith [h_sizeN.1, h_sizeD.2], by linarith [h_cmp]⟩

-- Computational sanity checks.
#guard (floorLogBase2Abs <$> parse "1/3") == some (-2)
#guard (floorLogBase2Abs <$> parse "1/8") == some (-3)
#guard (floorLogBase2Abs <$> parse "-22/7") == some 1
#guard (floorLogBase2Abs <$> parse "100") == some 6
#guard (ceilingLogBase2Abs <$> parse "1/3") == some (-1)
#guard (ceilingLogBase2Abs <$> parse "22/7") == some 2
#guard (ceilingLogBase2Abs <$> parse "100") == some 7
#guard (ceilingLogBase2Abs <$> parse "-4294967297") == some 33


/-! ### Checked base-2 logarithm -/

theorem toRat_cast_eq (q : AzRat) :
    (toRat q : ℝ) = (((if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) : ℤ) : ℝ)
      / (q.den.toNat : ℝ) := by
  rw [Rat.cast_def]
  rfl

theorem toInt_toAzInt' (n : AzNat) : n.toAzInt.toInt = n.toNat := rfl

/-- A rational power of two is `2^(powerOfTwoExponent q)`. -/
theorem toRat_of_isPowerOfTwo (q : AzRat) (h : q.isPowerOfTwo = true) :
    (toRat q : ℝ) = (2 : ℝ) ^ q.powerOfTwoExponent.toInt := by
  obtain ⟨hs, ⟨a, ha⟩, ⟨b, hb⟩⟩ := (isPowerOfTwo_iff q).mp h
  have hsa : q.num.size = a + 1 := by rw [← AzNat.size_toNat, ha, Nat.size_pow]
  have hsb : q.den.size = b + 1 := by rw [← AzNat.size_toNat, hb, Nat.size_pow]
  rw [toRat_cast_eq, hs, ha, hb, powerOfTwoExponent, AzInt.toInt_sub, toInt_toAzInt',
    toInt_toAzInt', AzNat.toNat_ofNat, AzNat.toNat_ofNat, hsa, hsb]
  simp only [↓reduceIte]
  push_cast
  rw [show ((a : ℤ) + 1 - ((b : ℤ) + 1)) = (a : ℤ) - b by ring, zpow_sub₀ (by norm_num),
    zpow_natCast, zpow_natCast]

/-- Conversely, a rational equal to `2^j` passes the test, with exponent `j`. -/
theorem isPowerOfTwo_of_toRat_eq_zpow (q : AzRat) (j : ℤ) (h : (toRat q : ℝ) = (2 : ℝ) ^ j) :
    q.isPowerOfTwo = true ∧ q.powerOfTwoExponent.toInt = j := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hden : (0 : ℝ) < q.den.toNat := by
    have : q.den.toNat ≠ 0 := fun h0 =>
      q.den_nz (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero]))
    exact_mod_cast Nat.pos_of_ne_zero this
  have hs : q.sign = true := by
    by_contra hs
    rw [Bool.not_eq_true] at hs
    rw [toRat_cast_eq, hs] at h
    simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast] at h
    have : -(q.num.toNat : ℝ) / q.den.toNat ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hden.le
    linarith
  rw [toRat_cast_eq, hs] at h
  simp only [↓reduceIte, Int.cast_natCast] at h
  have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
  have hexp : q.powerOfTwoExponent.toInt = (q.num.size : ℤ) - q.den.size := by
    rw [powerOfTwoExponent, AzInt.toInt_sub, toInt_toAzInt', toInt_toAzInt', AzNat.toNat_ofNat,
      AzNat.toNat_ofNat]
  rcases le_or_gt 0 j with hj | hj
  · have hnum : q.num.toNat = q.den.toNat * 2 ^ j.toNat := by
      have : (q.num.toNat : ℝ) = q.den.toNat * 2 ^ j.toNat := by
        rw [div_eq_iff hden.ne'] at h
        rw [h, ← zpow_natCast, Int.toNat_of_nonneg hj]
        ring
      exact_mod_cast this
    have hden1 : q.den.toNat = 1 := Nat.eq_one_of_dvd_coprimes hcop ⟨_, hnum⟩ (dvd_refl _)
    rw [hden1, one_mul] at hnum
    have hsn : q.num.size = j.toNat + 1 := by rw [← AzNat.size_toNat, hnum, Nat.size_pow]
    have hsd : q.den.size = 1 := by rw [← AzNat.size_toNat, hden1, Nat.size_one]
    refine ⟨(isPowerOfTwo_iff q).mpr
      ⟨hs, ⟨j.toNat, hnum⟩, ⟨0, by rw [hden1, pow_zero]⟩⟩, ?_⟩
    rw [hexp, hsn, hsd]
    omega
  · have hden' : q.den.toNat = q.num.toNat * 2 ^ (-j).toNat := by
      have : (q.den.toNat : ℝ) = q.num.toNat * 2 ^ (-j).toNat := by
        rw [div_eq_iff hden.ne'] at h
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), h, mul_comm ((2 : ℝ) ^ j),
          mul_assoc, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero,
          mul_one]
      exact_mod_cast this
    have hnum1 : q.num.toNat = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop.symm ⟨_, hden'⟩ (dvd_refl _)
    rw [hnum1, one_mul] at hden'
    have hsd : q.den.size = (-j).toNat + 1 := by rw [← AzNat.size_toNat, hden', Nat.size_pow]
    have hsn : q.num.size = 1 := by rw [← AzNat.size_toNat, hnum1, Nat.size_one]
    refine ⟨(isPowerOfTwo_iff q).mpr
      ⟨hs, ⟨0, by rw [hnum1, pow_zero]⟩, ⟨(-j).toNat, hden'⟩⟩, ?_⟩
    rw [hexp, hsn, hsd]
    omega

theorem checkedLogBase2_eq_some_iff (q : AzRat) (k : AzInt) :
    q.checkedLogBase2 = some k ↔ (toRat q : ℝ) = (2 : ℝ) ^ k.toInt := by
  unfold checkedLogBase2
  constructor
  · intro h
    split_ifs at h with hp
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact toRat_of_isPowerOfTwo q hp
  · intro h
    obtain ⟨hp, he⟩ := isPowerOfTwo_of_toRat_eq_zpow q k.toInt h
    rw [ite_eq_left hp, Option.some.injEq]
    rw [← AzInt.ofInt_toInt k, ← AzInt.ofInt_toInt q.powerOfTwoExponent, he]

theorem checkedLogBase2_eq_none_iff (q : AzRat) :
    q.checkedLogBase2 = none ↔ ∀ j : ℤ, (toRat q : ℝ) ≠ (2 : ℝ) ^ j := by
  constructor
  · intro h j hj
    obtain ⟨hp, -⟩ := isPowerOfTwo_of_toRat_eq_zpow q j hj
    unfold checkedLogBase2 at h
    rw [ite_eq_left hp] at h
    cases h
  · intro h
    unfold checkedLogBase2
    rw [ite_eq_right]
    intro hp
    exact h _ (toRat_of_isPowerOfTwo q hp)

theorem isPowerOfTwo_eq_false_of_checkedLogBase2_eq_none (q : AzRat)
    (h : q.checkedLogBase2 = none) : q.isPowerOfTwo = false := by
  unfold checkedLogBase2 at h
  by_contra hp
  rw [Bool.not_eq_false] at hp
  rw [ite_eq_left hp] at h
  cases h

theorem checkedLogBase2_eq_some (q : AzRat) (k : AzInt) (h : q.checkedLogBase2 = some k) :
    q.isPowerOfTwo = true ∧ k = q.powerOfTwoExponent := by
  unfold checkedLogBase2 at h
  split_ifs at h with hp
  · exact ⟨hp, (Option.some.inj h).symm⟩

end Azurite.AzRat
