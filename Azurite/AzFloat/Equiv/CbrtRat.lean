/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CbrtRat
import Azurite.AzFloat.Equiv.Cbrt
import Azurite.AzFloat.Equiv.SqrtRat
import Azurite.AzInt.Equiv.DivMod

/-!
# Correctness of the cube root of a rational

`cbrtRatPrecRound_eq`: `cbrtRatPrecRound q p mode = roundVal p mode (Spec.cbrt q)`, through
`cbrtRatCore_eq` for a positive fraction `n / d`: `floorLog2_bounds` for the exponent, the
identity `⌊∛⌊x⌋⌋ = ⌊∛x⌋` for the integer quotient, `AzNat.compareProduct_eq` for the exactness
and midpoint tests, and `roundFromFloor_normalizeCarry_eq`; negative inputs through
`roundVal_neg` and `realCbrt_neg`.
-/

namespace Azurite.AzFloat

open RoundingTarget

set_option maxHeartbeats 1000000 in
/-- The cube root of a positive fraction at the right scale. -/
theorem cbrtRatCore_eq (n d : AzNat) (hn : n ≠ 0) (hd : d ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cbrtRatCore n d p mode
      = roundVal p mode (some ((realCbrt ((n.toNat : ℝ) / d.toNat) : ℝ) : EReal)) := by
  have hd0 : 0 < d.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hd)
  have hdR : (0 : ℝ) < d.toNat := by exact_mod_cast hd0
  have hnR : (0 : ℝ) < n.toNat := by
    exact_mod_cast Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn)
  set x : ℝ := (n.toNat : ℝ) / d.toNat with hx
  have hxpos : 0 < x := by rw [hx]; exact div_pos hnR hdR
  unfold cbrtRatCore
  simp only []
  have h3I : ((AzNat.ofNat 3).toAzInt).toInt = 3 := by rw [toInt_toAzInt, AzNat.toNat_ofNat]; rfl
  -- the exponent `e = ⌊log₂ x⌋`
  obtain ⟨hxlo, hxhi⟩ := floorLog2_bounds n d hn hd
  rw [← hx] at hxlo hxhi
  set e : AzInt := if AzNat.normalizedCompare n d == .lt then
      (AzNat.ofNat n.size).toAzInt - (AzNat.ofNat d.size).toAzInt - (AzNat.ofNat 1).toAzInt
    else (AzNat.ofNat n.size).toAzInt - (AzNat.ofNat d.size).toAzInt with he_def
  have heI : e.toInt
      = (n.size : ℤ) - d.size - if AzNat.normalizedCompare n d == .lt then 1 else 0 := by
    rw [he_def]
    split_ifs <;> simp only [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat] <;> push_cast <;>
      ring
  rw [← heI] at hxlo hxhi
  clear_value e
  -- `h = ⌊e / 3⌋`
  set h₁ : AzInt := e / (AzNat.ofNat 3).toAzInt + (AzNat.ofNat 1).toAzInt with hh₁_def
  have hh : 3 * h₁.toInt - 3 ≤ e.toInt ∧ e.toInt < 3 * h₁.toInt := by
    rw [hh₁_def, AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat]
    have : (e / (AzNat.ofNat 3).toAzInt).toInt = e.toInt / 3 := by
      show (AzInt.div e (AzNat.ofNat 3).toAzInt).toInt = _
      rw [AzInt.toInt_div, h3I]
    rw [this]
    push_cast
    omega
  clear_value h₁
  -- `k = p − 1 − h`, the third of the shift
  set k : AzInt := (AzNat.ofNat p).toAzInt - h₁ with hk_def
  have hkI : k.toInt = p - h₁.toInt := by
    rw [hk_def, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
  clear_value k
  have habs : (k.abs.toNat : ℤ) = |k.toInt| := AzInt.abs_toNat_eq k
  -- the scaled fraction `A / D = x · 2^(3k)`
  set Mr : ℝ := x * (2 : ℝ) ^ (3 * k.toInt) with hMr
  have hMr0 : 0 < Mr := by positivity
  set A := if k.sign then n.shiftLeft (3 * k.abs.toNat) else n with hA_def
  set D := if k.sign then d else d.shiftLeft (3 * k.abs.toNat) with hD_def
  have hD0 : 0 < D.toNat := by
    rw [hD_def]; split_ifs
    · exact hd0
    · rw [AzNat.toNat_shiftLeft]; positivity
  have hDR : (0 : ℝ) < D.toNat := by exact_mod_cast hD0
  have hAD : (A.toNat : ℝ) / D.toNat = Mr := by
    rw [hMr, hx, hA_def, hD_def]
    by_cases hsg : k.sign = true
    · have hg0 : 0 ≤ k.toInt := (AzInt.sign_eq_true_iff k).mp hsg
      rw [ite_eq_left hsg, ite_eq_left hsg, AzNat.toNat_shiftLeft]
      push_cast
      rw [← zpow_natCast, show ((3 * k.abs.toNat : ℕ) : ℤ) = 3 * k.toInt by
        push_cast; rw [habs, abs_of_nonneg hg0]]
      ring
    · have hg0 : k.toInt < 0 := by
        have := (AzInt.sign_eq_true_iff k).not.mp hsg; push Not at this; exact this
      rw [ite_eq_right hsg, ite_eq_right hsg, AzNat.toNat_shiftLeft]
      push_cast
      rw [← zpow_natCast, show ((3 * k.abs.toNat : ℕ) : ℤ) = -(3 * k.toInt) by
        push_cast; rw [habs, abs_of_neg hg0]; ring, zpow_neg]
      field_simp
  clear_value A D
  -- bounds on `Mr`: `2^(3p−3) ≤ Mr < 2^(3p)`
  have hMlo : (2 : ℝ) ^ (3 * (p : ℤ) - 3) ≤ Mr := by
    rw [hMr]
    calc (2 : ℝ) ^ (3 * (p : ℤ) - 3) ≤ 2 ^ e.toInt * 2 ^ (3 * k.toInt) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ ≤ x * 2 ^ (3 * k.toInt) := mul_le_mul_of_nonneg_right hxlo (zpow_pos (by norm_num) _).le
  have hMhi : Mr < (2 : ℝ) ^ (3 * (p : ℤ)) := by
    rw [hMr]
    calc x * 2 ^ (3 * k.toInt) < 2 ^ (e.toInt + 1) * 2 ^ (3 * k.toInt) :=
          mul_lt_mul_of_pos_right hxhi (zpow_pos (by norm_num) _)
      _ ≤ 2 ^ (3 * (p : ℤ)) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  -- the integer cube root of the integer quotient
  set c := AzNat.rootInt (A / D) 3 with hc_def
  have hcN : c.toNat = AzNat.rootIntNat (A.toNat / D.toNat) 3 := by
    rw [hc_def, AzNat.toNat_rootInt, AzNat.toNat_div]
  clear_value c
  set Q := A.toNat / D.toNat with hQ
  have hQle : (Q : ℝ) ≤ Mr := by rw [← hAD, hQ]; exact Nat.cast_div_le
  have hQlt : Mr < Q + 1 := by
    rw [← hAD, div_lt_iff₀ hDR, hQ]
    have := Nat.lt_div_mul_add (a := A.toNat) hD0
    have : (A.toNat : ℝ) < (A.toNat / D.toNat : ℕ) * D.toNat + D.toNat := by exact_mod_cast this
    linarith
  obtain ⟨hc3, hlt3⟩ := AzNat.rootIntNat_spec Q 3 (by norm_num)
  rw [← hcN] at hc3 hlt3
  set y : ℝ := realCbrt Mr with hy_def
  have hy0 : 0 ≤ y := realCbrt_nonneg hMr0.le
  have hy3 : y ^ 3 = Mr := realCbrt_pow_three Mr
  have hc0 : (0 : ℝ) ≤ c.toNat := Nat.cast_nonneg _
  have hc3R : (c.toNat : ℝ) ^ 3 ≤ (Q : ℝ) := by exact_mod_cast hc3
  have hlt3R : (Q : ℝ) + 1 ≤ ((c.toNat : ℝ) + 1) ^ 3 := by
    have : ((Q + 1 : ℕ) : ℝ) ≤ (((c.toNat + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hlt3
    push_cast at this
    exact this
  have hlo : (c.toNat : ℝ) ≤ y := by
    rw [← pow_le_pow_iff_left₀ hc0 hy0 (by norm_num : (3 : ℕ) ≠ 0), hy3]
    linarith
  have hhi : y < c.toNat + 1 := by
    rw [← pow_lt_pow_iff_left₀ hy0 (by positivity) (by norm_num : (3 : ℕ) ≠ 0), hy3]
    linarith
  -- exactness: `c³ · D = A`
  have hex : (AzNat.compareProduct (c.pow 3) D A == .eq) = true ↔ y = c.toNat := by
    rw [beq_iff_eq, AzNat.compareProduct_eq, AzNat.toNat_pow, compare_eq_iff_eq,
      ← pow_left_inj₀ hy0 hc0 (by norm_num : (3 : ℕ) ≠ 0), hy3, ← hAD, div_eq_iff hDR.ne']
    constructor
    · intro h; exact_mod_cast h.symm
    · intro h; exact_mod_cast h.symm
  -- the midpoint test: `8A` against `(2c + 1)³ · D`
  have hmid : (AzNat.compareProduct (((c.shiftLeft 1).addUInt64 1).pow 3) D
      (A.shiftLeft 3)).swap = compare y ((c.toNat : ℝ) + 1 / 2) := by
    rw [AzNat.compareProduct_eq, AzNat.toNat_pow, AzNat.toNat_addUInt64, AzNat.toNat_shiftLeft,
      AzNat.toNat_shiftLeft, UInt64.toNat_one, ← compare_natCast]
    push_cast
    have hL : ((c.toNat : ℝ) * 2 + 1) ^ 3 * D.toNat
        = ((c.toNat : ℝ) + 1 / 2) ^ 3 * (8 * D.toNat) := by
      ring
    have hR : (A.toNat : ℝ) * 8 = Mr * (8 * D.toNat) := by
      rw [← hAD]; field_simp
    rw [hL, hR, compare_mul_right_pos _ _ _ (by positivity), ← hy3]
    have hmid_pos : (0 : ℝ) ≤ (c.toNat : ℝ) + 1 / 2 := by positivity
    rcases lt_trichotomy y ((c.toNat : ℝ) + 1 / 2) with h | h | h
    · rw [compare_lt_iff_lt.mpr h]
      rw [compare_gt_iff_gt.mpr (pow_lt_pow_left₀ h hy0 (by norm_num))]; rfl
    · rw [compare_eq_iff_eq.mpr h]
      rw [compare_eq_iff_eq.mpr (by rw [h])]; rfl
    · rw [compare_gt_iff_gt.mpr h]
      rw [compare_lt_iff_lt.mpr (pow_lt_pow_left₀ h hmid_pos (by norm_num))]; rfl
  -- bounds on `y`
  have hylo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ y := by
    rw [← pow_le_pow_iff_left₀ (zpow_pos (by norm_num) _).le hy0 (by norm_num : (3 : ℕ) ≠ 0), hy3,
      ← zpow_natCast, ← zpow_mul]
    convert hMlo using 2; push_cast; ring
  have hyhi : y < (2 : ℝ) ^ (p : ℤ) := by
    rw [← pow_lt_pow_iff_left₀ hy0 (zpow_pos (by norm_num) _).le (by norm_num : (3 : ℕ) ≠ 0), hy3,
      ← zpow_natCast, ← zpow_mul]
    convert hMhi using 2; push_cast; ring
  rw [roundFromFloor_normalizeCarry_eq p mode y c _ _ h₁ hylo hyhi hlo hhi hex hmid]
  congr 3
  -- `∛x = y · 2^(h + 1 − p)`
  symm
  apply realCbrt_eq_of_pow_three (by positivity)
  rw [mul_pow, hy3, hMr, mul_assoc, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (by norm_num),
    show 3 * k.toInt + (h₁.toInt - p) * ((3 : ℕ) : ℤ) = 0 by rw [hkI]; push_cast; ring,
    zpow_zero, mul_one]

/-- **Correctness of `cbrtRatPrecRound`.** -/
theorem cbrtRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cbrtRatPrecRound q p mode = roundVal p mode (Spec.cbrt ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold cbrtRatPrecRound
  by_cases hq : q.num = 0
  · rw [ite_eq_left hq, (AzRat.toRat_eq_zero_iff q).mpr hq, EReal.coe_zero, Spec.cbrt_zero,
      roundVal_zero]
  · rw [ite_eq_right hq, ite_eq_right (NeZero.ne p), Spec.cbrt_coe]
    cases hs : q.sign
    · have hval : (AzRat.toRat q : ℝ) = -((q.num.toNat : ℝ) / q.den.toNat) := by
        rw [coe_toRat_eq, hs]
        simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
        ring
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hval, realCbrt_neg, roundVal_neg, cbrtRatCore_eq q.num q.den hq q.den_nz]
    · have hval : (AzRat.toRat q : ℝ) = (q.num.toNat : ℝ) / q.den.toNat := by
        rw [coe_toRat_eq, hs]; simp
      rw [ite_eq_left rfl, hval, cbrtRatCore_eq q.num q.den hq q.den_nz]

end Azurite.AzFloat
