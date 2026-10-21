/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RoundToInteger
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.Float64
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Equiv.Sum
import Azurite.AzInt.Equiv.ShiftRightRound
import Azurite.AzNat.Equiv.IsMultipleOfPow2
import Azurite.Rounding.IntPrecision

/-!
# Equivalence: rounding to an integer

`roundToIntegerPrecRound_spec`: for a float of value `v`, the result's value is
`round (intPrecisionSet p) mode v` (the one-step rounding of `v` to an integer representable at
`p` bits), the `Ordering` compares that with `v`, and the `Bool` says whether `v` is an integer.
The two branches of the implementation are the two characterizations of `intPrecisionSet`:
from exponent `p` on, `setPrecRound` (`val_round_intPrecision_large`); below, the rounded shift
(`val_round_intPrecision_small`).
-/

namespace Azurite.AzFloat

open RoundingTarget

/-- A finite value through its core significand: `(±1) · core · 2^(e − q)`. -/
theorem finiteVal_eq_core_mul (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    finiteVal s e m
      = (if s then 1 else -1) * ((coreSignificand q m).toNat : ℝ)
        * (2 : ℝ) ^ (e.toInt - q) := by
  rw [finiteVal_eq_core s e hv, finiteVal_sign, finiteVal_true_eq, size_coreSignificand hv]
  ring

theorem abs_sign_mul (s : Bool) (r : ℝ) : |(if s then (1 : ℝ) else -1) * r| = |r| := by
  cases s <;> simp

/-- `isInteger` decides whether a finite value is an integer. -/
theorem isInteger_finite (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    isInteger (finite s e q m hv) = true ↔ ∃ n : ℤ, finiteVal s e m = n := by
  have hval := finiteVal_eq_core_mul s e hv
  set c := coreSignificand q m with hc
  simp only [isInteger, Bool.or_eq_true, decide_eq_true_eq, AzNat.isMultipleOfPow2_eq,
    AzInt.le_iff_toInt_le, toInt_toAzInt, AzNat.toNat_ofNat]
  by_cases hqe : (q : ℤ) ≤ e.toInt
  · simp only [hqe, true_or, true_iff]
    refine ⟨(if s then 1 else -1) * c.toNat * 2 ^ (e.toInt - q).toNat, ?_⟩
    rw [hval]
    push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  · simp only [hqe, false_or]
    set j : ℕ := ((AzNat.ofNat q).toAzInt - e).abs.toNat with hj
    have hjI : (j : ℤ) = q - e.toInt := by
      rw [hj, AzInt.abs_toNat_eq, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat,
        abs_of_pos (by omega)]
    have h2 : (2 : ℝ) ^ (e.toInt - q) = ((2 : ℝ) ^ j)⁻¹ := by
      rw [← zpow_natCast, hjI, ← zpow_neg]; congr 1; ring
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    rw [hval, h2]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨(if s then 1 else -1) * t, ?_⟩
      rw [ht]
      push_cast
      rw [mul_assoc, mul_assoc, mul_comm ((2 : ℝ) ^ j), mul_assoc, inv_mul_cancel₀ h2pos.ne',
        mul_one]
    · rintro ⟨n, hn⟩
      have habs : (c.toNat : ℝ) * ((2 : ℝ) ^ j)⁻¹ = (n.natAbs : ℝ) := by
        have h' : |(if s then (1 : ℝ) else -1) * (c.toNat : ℝ) * ((2 : ℝ) ^ j)⁻¹|
            = |(n : ℝ)| := by
          rw [hn]
        rw [mul_assoc, abs_sign_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
          abs_of_pos (inv_pos.mpr h2pos)] at h'
        rw [h', ← Int.cast_natCast (R := ℝ) n.natAbs, Int.natCast_natAbs, Int.cast_abs]
      have hc' : c.toNat = n.natAbs * 2 ^ j := by
        have : (c.toNat : ℝ) = (n.natAbs : ℝ) * (2 : ℝ) ^ j := by
          rw [← habs]; field_simp
        exact_mod_cast this
      exact Dvd.intro_left _ hc'.symm

@[simp] theorem roundToIntegerPrecRound_nan (p : ℕ) (mode : RoundingMode) :
    roundToIntegerPrecRound nan p mode = (nan, .eq, false) := rfl

@[simp] theorem roundToIntegerPrecRound_infinity (s : Bool) (p : ℕ) (mode : RoundingMode) :
    roundToIntegerPrecRound (infinity s) p mode = (infinity s, .eq, false) := rfl

@[simp] theorem roundToIntegerPrecRound_zero (p : ℕ) (mode : RoundingMode) :
    roundToIntegerPrecRound zero p mode = (zero, .eq, true) := rfl

/-- **Rounding to an integer is correctly rounded.**  For a float of value `v`: the result is
the rounding of `v` to `intPrecisionSet p` in `mode`, the `Ordering` compares it with `v`, and
the `Bool` says whether `v` is an integer. -/
theorem roundToIntegerPrecRound_spec (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (v : ℝ) (hx : x.toVal = some (v : EReal)) :
    (roundToIntegerPrecRound x p mode).1.toVal = some (round (intPrecisionSet p) mode v).val ∧
      (roundToIntegerPrecRound x p mode).2.1
        = compare (round (intPrecisionSet p) mode v).val (v : EReal) ∧
      ((roundToIntegerPrecRound x p mode).2.2 = true ↔ ∃ n : ℤ, v = n) := by
  have hp : 1 ≤ p := Nat.pos_of_ne_zero (NeZero.ne p)
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero =>
    have hv : v = 0 := by
      simp only [toVal_zero, Option.some.injEq] at hx
      exact EReal.coe_eq_zero.mp hx.symm
    subst hv
    have h0 : (round (intPrecisionSet p) mode (0 : ℝ)).val = (((0 : ℝ)) : EReal) :=
      val_round_of_mem _ mode (by simpa using int_mem_intPrecisionSet (p := p) 0 (by simp))
    refine ⟨?_, ?_, ?_⟩
    · rw [roundToIntegerPrecRound_zero, h0]; rfl
    · rw [roundToIntegerPrecRound_zero, h0]; simp
    · simp only [roundToIntegerPrecRound_zero, true_iff]
      exact ⟨0, by simp⟩
  | finite s e q m hv =>
  simp only [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
  subst hx
  obtain ⟨hlo, hhi⟩ := abs_finiteVal_bounds s e hv
  have hval := finiteVal_eq_core_mul s e hv
  set c := coreSignificand q m with hc
  have hc0 : c ≠ 0 := coreSignificand_ne_zero hv
  have hint := isInteger_finite s e hv
  unfold roundToIntegerPrecRound
  simp only []
  by_cases hbr : ((AzNat.ofNat p).toAzInt ≤ e || (AzNat.ofNat q).toAzInt ≤ e) = true
  · rw [ite_eq_left hbr]
    simp only [Bool.or_eq_true, decide_eq_true_eq, AzInt.le_iff_toInt_le, toInt_toAzInt,
      AzNat.toNat_ofNat] at hbr
    rw [setPrecRound_eq_liftE]
    unfold liftE liftVal
    rw [toVal_finite, Option.bind_some]
    simp only [id_eq]
    obtain ⟨h1, h2⟩ := roundVal_coe p mode (finiteVal s e m)
    rw [val_round_floatSet] at h1 h2
    refine ⟨?_, ?_, hint⟩
    all_goals
      rcases le_or_gt (p : ℤ) e.toInt with hpe | hpe
      · -- `2^(p−1) ≤ |v|`: `p`-bit rounding
        have hlarge : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |finiteVal s e m| :=
          (zpow_le_zpow_right₀ (by norm_num) (by omega)).trans hlo
        rw [val_round_intPrecision_large mode _ hlarge]
        first | exact h1 | exact h2
      · -- an integer below `2^(p−1)`: exact
        have hqe : (q : ℤ) ≤ e.toInt := by omega
        obtain ⟨n₀, hn₀⟩ := hint.mp (by
          simp only [isInteger, Bool.or_eq_true, decide_eq_true_eq, AzInt.le_iff_toInt_le,
            toInt_toAzInt, AzNat.toNat_ofNat]
          exact Or.inl hqe)
        have hsmall : |finiteVal s e m| < (2 : ℝ) ^ ((p : ℤ) - 1) :=
          hhi.trans_le (zpow_le_zpow_right₀ (by norm_num) (by omega))
        have hbound : |n₀| < 2 ^ p := by
          rw [hn₀, two_zpow_pred_eq hp, ← Int.cast_abs] at hsmall
          have : |n₀| < 2 ^ (p - 1) := by exact_mod_cast hsmall
          exact this.trans (two_pow_pred_lt hp)
        have hS : (round (intPrecisionSet p) mode (finiteVal s e m)).val
            = ((finiteVal s e m : ℝ) : EReal) := by
          rw [val_round_intPrecision_small mode _ hsmall, ← toInt_spec, hn₀,
            toInt_round_intCast]
        have hP : (round (precisionSet 2 p) mode (finiteVal s e m)).val
            = ((finiteVal s e m : ℝ) : EReal) := by
          rw [hn₀]; exact val_round_of_mem _ mode (int_mem_precisionSet n₀ hbound)
        rw [hS]
        first | (rw [h1, hP]) | (rw [h2, hP])
  · rw [ite_eq_right hbr]
    simp only [Bool.or_eq_true, decide_eq_true_eq, AzInt.le_iff_toInt_le, toInt_toAzInt,
      AzNat.toNat_ofNat, not_or, not_le] at hbr
    obtain ⟨hpe, hqe⟩ := hbr
    set z := AzInt.mkNorm s c with hz_def
    set sh : ℕ := ((AzNat.ofNat q).toAzInt - e).abs.toNat with hsh
    have hshI : (sh : ℤ) = q - e.toInt := by
      rw [hsh, AzInt.abs_toNat_eq, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat,
        abs_of_pos (by omega)]
    have hz : (z.toInt : ℝ) = (if s then 1 else -1) * (c.toNat : ℝ) := by
      rcases Bool.eq_false_or_eq_true s with hs | hs <;>
        simp [hz_def, hs, AzInt.toInt_mkNorm_true, AzInt.toInt_mkNorm_false c hc0]
    have heq : (z.toInt : ℝ) / (2 : ℝ) ^ sh = finiteVal s e m := by
      rw [hz, hval, ← zpow_natCast, hshI, show e.toInt - q = -((q : ℤ) - e.toInt) by ring,
        zpow_neg, div_eq_mul_inv]
    set r := z.shiftRightRound mode sh with hr_def
    have hr1 : ((r.1.toInt : ℝ) : EReal) = (round intSet mode (finiteVal s e m)).val := by
      rw [← heq]; exact AzInt.toInt_shiftRightRound z mode sh
    have hr2 : r.2 = compare (r.1.toInt : ℝ) (finiteVal s e m) := by
      rw [← heq]; exact AzInt.snd_shiftRightRound z mode sh
    have hsmall : |finiteVal s e m| < (2 : ℝ) ^ ((p : ℤ) - 1) :=
      hhi.trans_le (zpow_le_zpow_right₀ (by norm_num) (by omega))
    have hS : (round (intPrecisionSet p) mode (finiteVal s e m)).val
        = ((r.1.toInt : ℝ) : EReal) := by
      rw [val_round_intPrecision_small mode _ hsmall, hr1]
    have hti : toInt (round intSet mode (finiteVal s e m)) = r.1.toInt := toInt_eq_of_val hr1
    refine ⟨?_, ?_, ?_⟩
    · rw [setPrecRound_eq_liftE]
      unfold liftE liftVal
      rw [toVal_ofAzInt, Option.bind_some]
      simp only [id_eq]
      have hk : |r.1.toInt| ≤ 2 ^ p := by
        rw [← hti]
        have hB : |finiteVal s e m| ≤ ((2 ^ (p - 1) : ℤ) : ℝ) := by
          rw [← two_zpow_pred_eq hp]; exact hsmall.le
        exact (abs_toInt_round_le mode _ _ hB).trans (two_pow_pred_lt hp).le
      have hmem := mem_floatSet_mul_zpow p r.1.toInt 0 hk
      simp only [zpow_zero, mul_one] at hmem
      rw [(roundVal_of_mem p mode _ hmem).1, hS]
    · rw [hS, compare_coe_coe, hr2]
    · rw [decide_eq_true_iff, hr2, compare_eq_iff_eq]
      constructor
      · intro h; exact ⟨r.1.toInt, h.symm⟩
      · rintro ⟨n, hn⟩
        rw [hn, ← hti, hn, toInt_round_intCast]

end Azurite.AzFloat
