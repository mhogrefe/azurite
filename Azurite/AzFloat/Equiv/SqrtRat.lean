/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AddSubRat
import Azurite.AzFloat.Equiv.Rsqrt
import Azurite.AzFloat.Equiv.Sqrt
import Azurite.AzFloat.SqrtRat
import Azurite.AzNat.Equiv.CompareProduct
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.NormalizedCompare
import Azurite.AzRat.Equiv.ToSci

/-!
# Correctness of the square root and reciprocal square root of a rational

`sqrtRatPrecRound_eq`: `sqrtRatPrecRound q p mode = roundVal p mode (Spec.sqrt q)`, through
`sqrtRatCore_eq` for a positive fraction `n / d`.  The ingredients are `floorLog2_bounds` (the
exponent read off the sizes and the normalized comparison), the identity `⌊√⌊x⌋⌋ = ⌊√x⌋` for the
integer quotient, `AzNat.compareProduct_eq` for the exactness and midpoint tests, and
`roundFromFloor_normalizeCarry_eq`, the common tail of every `roundFromFloor` algorithm: a
floor with the exactness and midpoint facts, rounded and normalized, is `roundVal` of the value.
`rsqrtRatPrecRound_eq` follows from `sqrtRatCore_eq` on the reciprocal fraction, as
`(√(n / d))⁻¹ = √(d / n)`.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-- `roundFromFloor` followed by `normalizeCarry` with exponent `E` rounds `y · 2^(E − p)`
correctly, for a floor `s` of `y ∈ [2^(p−1), 2^p)` with the exactness and midpoint facts. -/
theorem roundFromFloor_normalizeCarry_eq (p : ℕ) [NeZero p] (mode : RoundingMode) (y : ℝ)
    (s : AzNat) (exact : Bool) (cmpMid : Ordering) (E : AzInt)
    (hylo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ y) (hyhi : y < (2 : ℝ) ^ (p : ℤ))
    (hlo : (s.toNat : ℝ) ≤ y) (hhi : y < s.toNat + 1) (hex : exact = true ↔ y = s.toNat)
    (hmid : cmpMid = compare y ((s.toNat : ℝ) + 1 / 2)) :
    (normalizeCarry (AzInt.mkNorm true (roundFromFloor s exact cmpMid mode).1) E p,
        (roundFromFloor s exact cmpMid mode).2)
      = roundVal p mode (some ((y * (2 : ℝ) ^ (E.toInt - p) : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨hR, htag⟩ := roundFromFloor_spec y s exact cmpMid mode hlo hhi hex hmid
  set ro := roundFromFloor s exact cmpMid mode with hro
  clear_value ro
  set w : ℤ := E.toInt - p with hw
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w := zpow_pos (by norm_num) _
  set v : ℝ := y * (2 : ℝ) ^ w with hv
  have hypos : 0 < y := lt_of_lt_of_le (zpow_pos (by norm_num) _) hylo
  have hv0 : v ≠ 0 := by rw [hv]; positivity
  have hvabs : |v| = y * (2 : ℝ) ^ w := by rw [hv, abs_of_pos (by positivity)]
  have hvpos : 0 < |v| := by rw [hvabs]; positivity
  have hlog : Int.log 2 |v| = w + p - 1 := by
    apply le_antisymm
    · have h := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hvpos).mp (by
        rw [hvabs, zpow_add₀ (by norm_num), mul_comm]
        exact mul_lt_mul_of_pos_left hyhi h2w)
      omega
    · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hvpos).mp (by
        rw [hvabs, show w + p - 1 = ((p : ℤ) - 1) + w by ring, zpow_add₀ (by norm_num)]
        exact mul_le_mul_of_nonneg_right hylo h2w.le)
  have hscale : precScale 2 p v = (2 : ℝ) ^ w := by
    unfold precScale
    rw [hlog]
    push_cast
    congr 1
    ring
  have hyv : v / (2 : ℝ) ^ w = y := by rw [hv, mul_div_cancel_right₀ _ h2w.ne']
  have hround : (round (floatSet p) mode v).val
      = ((((AzInt.mkNorm true ro.1).toInt : ℝ) * 2 ^ w : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode v hv0, hscale, hyv, hR,
      AzInt.toInt_mkNorm_true]
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
  obtain ⟨hRval, hRprec⟩ := normalizeCarry_spec (AzInt.mkNorm true ro.1) p hp E hlo' hhi'
  rw [← hw] at hRval
  symm
  refine Prod.ext ?_ ?_
  · exact toVal_injective p (ofEReal_spec p mode v).1 (Or.inl hRprec)
      (by rw [fst_roundVal, ofVal_some, (ofEReal_spec p mode v).2, hround, hRval])
  · show (roundVal p mode (some (v : EReal))).2 = ro.2
    rw [(roundVal_coe p mode v).2, hround, compare_coe_coe, htag, AzInt.toInt_mkNorm_true,
      Int.cast_natCast, hv, compare_mul_right_pos _ _ _ h2w]

/-- The exponent `⌊log₂ (n / d)⌋` from the sizes and the normalized comparison. -/
theorem floorLog2_bounds (n d : AzNat) (hn : n ≠ 0) (hd : d ≠ 0) :
    (2 : ℝ) ^ ((n.size : ℤ) - d.size - if AzNat.normalizedCompare n d == .lt then 1 else 0)
        ≤ (n.toNat : ℝ) / d.toNat ∧
      (n.toNat : ℝ) / d.toNat
        < (2 : ℝ) ^ ((n.size : ℤ) - d.size - (if AzNat.normalizedCompare n d == .lt then 1 else 0)
          + 1) := by
  obtain ⟨hn1, hn2⟩ := toNat_bounds_of_ne_zero n hn
  obtain ⟨hd1, hd2⟩ := toNat_bounds_of_ne_zero d hd
  have hns : 1 ≤ n.size := size_pos_of_ne_zero hn
  have hds : 1 ≤ d.size := size_pos_of_ne_zero hd
  have hn0 : 0 < n.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn)
  have hd0 : 0 < d.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hd)
  have hdR : (0 : ℝ) < d.toNat := by exact_mod_cast hd0
  have hcross := AzNat.normalizedCompare_eq_cross n d hn0 hd0
  -- real forms of the size bounds
  have hn1R : (2 : ℝ) ^ ((n.size : ℤ) - 1) ≤ n.toNat := by
    rw [show (n.size : ℤ) - 1 = ((n.size - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hn1
  have hn2R : (n.toNat : ℝ) < (2 : ℝ) ^ (n.size : ℤ) := by rw [zpow_natCast]; exact_mod_cast hn2
  have hd1R : (2 : ℝ) ^ ((d.size : ℤ) - 1) ≤ d.toNat := by
    rw [show (d.size : ℤ) - 1 = ((d.size - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hd1
  have hd2R : (d.toNat : ℝ) < (2 : ℝ) ^ (d.size : ℤ) := by rw [zpow_natCast]; exact_mod_cast hd2
  have h2 : ∀ a b : ℤ, (2 : ℝ) ^ (a - b) = 2 ^ a / 2 ^ b := fun a b => zpow_sub₀ (by norm_num) a b
  by_cases hlt : AzNat.normalizedCompare n d == .lt
  · rw [ite_eq_left hlt]
    have h : n.toNat * 2 ^ d.size < d.toNat * 2 ^ n.size := by
      rw [hcross, beq_iff_eq, compare_lt_iff_lt] at hlt; exact hlt
    have hR : (n.toNat : ℝ) * 2 ^ (d.size : ℤ) < d.toNat * 2 ^ (n.size : ℤ) := by
      rw [zpow_natCast, zpow_natCast]; exact_mod_cast h
    constructor
    · rw [le_div_iff₀ hdR, show (n.size : ℤ) - d.size - 1 = ((n.size : ℤ) - 1) - d.size by ring,
        h2]
      calc (2 : ℝ) ^ ((n.size : ℤ) - 1) / 2 ^ (d.size : ℤ) * d.toNat
          ≤ (2 : ℝ) ^ ((n.size : ℤ) - 1) / 2 ^ (d.size : ℤ) * 2 ^ (d.size : ℤ) :=
            mul_le_mul_of_nonneg_left hd2R.le (by positivity)
        _ = (2 : ℝ) ^ ((n.size : ℤ) - 1) := div_mul_cancel₀ _ (by positivity)
        _ ≤ n.toNat := hn1R
    · rw [div_lt_iff₀ hdR, show (n.size : ℤ) - d.size - 1 + 1 = (n.size : ℤ) - d.size by ring, h2,
        div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
      linarith
  · rw [ite_eq_right hlt]
    have h : d.toNat * 2 ^ n.size ≤ n.toNat * 2 ^ d.size := by
      rw [hcross, beq_iff_eq] at hlt
      exact not_lt.mp (fun h => hlt (compare_lt_iff_lt.mpr h))
    have hR : (d.toNat : ℝ) * 2 ^ (n.size : ℤ) ≤ n.toNat * 2 ^ (d.size : ℤ) := by
      rw [zpow_natCast, zpow_natCast]; exact_mod_cast h
    constructor
    · rw [sub_zero, le_div_iff₀ hdR, h2, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
    · rw [sub_zero, div_lt_iff₀ hdR,
        show (n.size : ℤ) - d.size + 1 = (n.size : ℤ) - ((d.size : ℤ) - 1) by ring, h2]
      calc (n.toNat : ℝ) < 2 ^ (n.size : ℤ) := hn2R
        _ = 2 ^ (n.size : ℤ) / 2 ^ ((d.size : ℤ) - 1) * 2 ^ ((d.size : ℤ) - 1) :=
            (div_mul_cancel₀ _ (by positivity)).symm
        _ ≤ 2 ^ (n.size : ℤ) / 2 ^ ((d.size : ℤ) - 1) * d.toNat :=
            mul_le_mul_of_nonneg_left hd1R (by positivity)

/-- The square root of a positive fraction at the right scale. -/
theorem sqrtRatCore_eq (n d : AzNat) (hn : n ≠ 0) (hd : d ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    sqrtRatCore n d p mode
      = roundVal p mode (some ((Real.sqrt ((n.toNat : ℝ) / d.toNat) : ℝ) : EReal)) := by
  have hd0 : 0 < d.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hd)
  have hdR : (0 : ℝ) < d.toNat := by exact_mod_cast hd0
  have hnR : (0 : ℝ) < n.toNat := by
    exact_mod_cast Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn)
  set x : ℝ := (n.toNat : ℝ) / d.toNat with hx
  have hxpos : 0 < x := by rw [hx]; exact div_pos hnR hdR
  unfold sqrtRatCore
  simp only []
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
  -- `h = ⌊e / 2⌋`
  set h₁ : AzInt := e.shiftRight 1 + (AzNat.ofNat 1).toAzInt with hh₁_def
  have hh : 2 * h₁.toInt - 2 ≤ e.toInt ∧ e.toInt < 2 * h₁.toInt := by
    rw [hh₁_def, AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat, AzInt.toInt_shiftRight_one]
    push_cast
    omega
  clear_value h₁
  -- `k = p − 1 − h`, the half shift
  set k : AzInt := (AzNat.ofNat p).toAzInt - h₁ with hk_def
  have hkI : k.toInt = p - h₁.toInt := by
    rw [hk_def, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
  clear_value k
  have habs : (k.abs.toNat : ℤ) = |k.toInt| := AzInt.abs_toNat_eq k
  -- the scaled fraction `A / D = x · 2^(2k)`
  set Mr : ℝ := x * (2 : ℝ) ^ (2 * k.toInt) with hMr
  have hMr0 : 0 < Mr := by positivity
  set A := if k.sign then n.shiftLeft (2 * k.abs.toNat) else n with hA_def
  set D := if k.sign then d else d.shiftLeft (2 * k.abs.toNat) with hD_def
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
      rw [← zpow_natCast, show ((2 * k.abs.toNat : ℕ) : ℤ) = 2 * k.toInt by
        push_cast; rw [habs, abs_of_nonneg hg0]]
      ring
    · have hg0 : k.toInt < 0 := by
        have := (AzInt.sign_eq_true_iff k).not.mp hsg; push Not at this; exact this
      rw [ite_eq_right hsg, ite_eq_right hsg, AzNat.toNat_shiftLeft]
      push_cast
      rw [← zpow_natCast, show ((2 * k.abs.toNat : ℕ) : ℤ) = -(2 * k.toInt) by
        push_cast; rw [habs, abs_of_neg hg0]; ring, zpow_neg]
      field_simp
  clear_value A D
  -- bounds on `Mr`: `2^(2p−2) ≤ Mr < 2^(2p)`
  have hMlo : (2 : ℝ) ^ (2 * (p : ℤ) - 2) ≤ Mr := by
    rw [hMr]
    calc (2 : ℝ) ^ (2 * (p : ℤ) - 2) ≤ 2 ^ e.toInt * 2 ^ (2 * k.toInt) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ ≤ x * 2 ^ (2 * k.toInt) := mul_le_mul_of_nonneg_right hxlo (zpow_pos (by norm_num) _).le
  have hMhi : Mr < (2 : ℝ) ^ (2 * (p : ℤ)) := by
    rw [hMr]
    calc x * 2 ^ (2 * k.toInt) < 2 ^ (e.toInt + 1) * 2 ^ (2 * k.toInt) :=
          mul_lt_mul_of_pos_right hxhi (zpow_pos (by norm_num) _)
      _ ≤ 2 ^ (2 * (p : ℤ)) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  -- the integer square root of the integer quotient
  set s := AzNat.sqrt (A / D) with hs_def
  have hsN : s.toNat = Nat.sqrt (A.toNat / D.toNat) := by
    rw [hs_def, AzNat.toNat_sqrt, AzNat.toNat_div]
  clear_value s
  set Q := A.toNat / D.toNat with hQ
  have hQle : (Q : ℝ) ≤ Mr := by rw [← hAD, hQ]; exact Nat.cast_div_le
  have hQlt : Mr < Q + 1 := by
    rw [← hAD, div_lt_iff₀ hDR, hQ]
    have := Nat.lt_div_mul_add (a := A.toNat) hD0
    have : (A.toNat : ℝ) < (A.toNat / D.toNat : ℕ) * D.toNat + D.toNat := by exact_mod_cast this
    linarith
  set y : ℝ := Real.sqrt Mr with hy_def
  have hsq_le : Nat.sqrt Q ^ 2 ≤ Q := Nat.sqrt_le' _
  have hlt_sq : Q < (Nat.sqrt Q + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hlo : (s.toNat : ℝ) ≤ y := by
    rw [hsN, hy_def]
    exact le_trans Real.nat_sqrt_le_real_sqrt (Real.sqrt_le_sqrt hQle)
  have hhi : y < s.toNat + 1 := by
    rw [hsN, hy_def]
    calc Real.sqrt Mr < Real.sqrt (Q + 1) := Real.sqrt_lt_sqrt hMr0.le hQlt
      _ ≤ Nat.sqrt Q + 1 := by
          rw [Real.sqrt_le_left (by positivity)]
          exact_mod_cast hlt_sq
  -- exactness: `s² · D = A`
  have hex : (AzNat.compareProduct (AzNat.square s) D A == .eq) = true ↔ y = s.toNat := by
    rw [beq_iff_eq, AzNat.compareProduct_eq, AzNat.toNat_square, compare_eq_iff_eq, hy_def,
      Real.sqrt_eq_iff_eq_sq hMr0.le (Nat.cast_nonneg _), ← hAD, div_eq_iff hDR.ne']
    constructor
    · intro h; exact_mod_cast h.symm
    · intro h; exact_mod_cast h.symm
  -- the midpoint test: `4A` against `(2s + 1)² · D`
  have hmid : (AzNat.compareProduct (AzNat.square ((s.shiftLeft 1).addUInt64 1)) D
      (A.shiftLeft 2)).swap = compare y ((s.toNat : ℝ) + 1 / 2) := by
    rw [AzNat.compareProduct_eq, AzNat.toNat_square, AzNat.toNat_addUInt64, AzNat.toNat_shiftLeft,
      AzNat.toNat_shiftLeft, UInt64.toNat_one, ← compare_natCast]
    push_cast
    have hL : ((s.toNat : ℝ) * 2 + 1) ^ 2 * D.toNat
        = ((s.toNat : ℝ) + 1 / 2) ^ 2 * (4 * D.toNat) := by
      ring
    have hR : (A.toNat : ℝ) * 4 = Mr * (4 * D.toNat) := by
      rw [← hAD]; field_simp
    rw [hL, hR, compare_mul_right_pos _ _ _ (by positivity), hy_def]
    have hmid_pos : (0 : ℝ) < (s.toNat : ℝ) + 1 / 2 := by positivity
    rcases lt_trichotomy (Real.sqrt Mr) ((s.toNat : ℝ) + 1 / 2) with h | h | h
    · rw [compare_lt_iff_lt.mpr h]
      rw [Real.sqrt_lt' hmid_pos] at h
      rw [compare_gt_iff_gt.mpr h]; rfl
    · rw [compare_eq_iff_eq.mpr h]
      rw [Real.sqrt_eq_iff_eq_sq hMr0.le hmid_pos.le] at h
      rw [compare_eq_iff_eq.mpr h.symm]; rfl
    · rw [compare_gt_iff_gt.mpr h]
      rw [Real.lt_sqrt hmid_pos.le] at h
      rw [compare_lt_iff_lt.mpr h]; rfl
  -- bounds on `y`
  have hylo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ y := by
    rw [hy_def, Real.le_sqrt (zpow_pos (by norm_num) _).le hMr0.le, ← zpow_natCast, ← zpow_mul]
    convert hMlo using 2; push_cast; ring
  have hyhi : y < (2 : ℝ) ^ (p : ℤ) := by
    rw [hy_def, Real.sqrt_lt' (zpow_pos (by norm_num) _), ← zpow_natCast, ← zpow_mul]
    convert hMhi using 2; push_cast; ring
  rw [roundFromFloor_normalizeCarry_eq p mode y s _ _ h₁ hylo hyhi hlo hhi hex hmid]
  congr 3
  -- `√x = y · 2^(h + 1 − p)`
  rw [hy_def, hMr, Real.sqrt_mul hxpos.le, show (2 : ℝ) ^ (2 * k.toInt) = (2 ^ k.toInt) ^ 2 by
      rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring,
    Real.sqrt_sq (zpow_pos (by norm_num) _).le, mul_assoc, ← zpow_add₀ (by norm_num),
    show k.toInt + (h₁.toInt - p) = 0 by rw [hkI]; ring, zpow_zero, mul_one]

/-- **Correctness of `sqrtRatPrecRound`.** -/
theorem sqrtRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrtRatPrecRound q p mode = roundVal p mode (Spec.sqrt ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold sqrtRatPrecRound
  by_cases hq : q.num = 0
  · rw [ite_eq_left hq, (AzRat.toRat_eq_zero_iff q).mpr hq, EReal.coe_zero, Spec.sqrt_zero,
      roundVal_zero]
  · rw [ite_eq_right hq]
    have hnum : (0 : ℝ) < q.num.toNat := by exact_mod_cast AzRat.num_toNat_pos q hq
    have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
    cases hs : q.sign
    · have hneg : (AzRat.toRat q : ℝ) < 0 := by
        rw [coe_toRat_eq, hs]
        simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
        exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden
      rw [Spec.sqrt_coe_neg _ hneg, roundVal_none]; rfl
    · have hval : (AzRat.toRat q : ℝ) = (q.num.toNat : ℝ) / q.den.toNat := by
        rw [coe_toRat_eq, hs]; simp
      rw [ite_eq_left rfl, hval, Spec.sqrt_coe _ (div_pos hnum hden).le,
        sqrtRatCore_eq q.num q.den hq q.den_nz]

/-- **Correctness of `rsqrtRatPrecRound`.** -/
theorem rsqrtRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    rsqrtRatPrecRound q p mode = roundVal p mode (Spec.rsqrt ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold rsqrtRatPrecRound
  by_cases hq : q.num = 0
  · rw [ite_eq_left hq, (AzRat.toRat_eq_zero_iff q).mpr hq, EReal.coe_zero, Spec.rsqrt_zero,
      roundVal_top]
  · rw [ite_eq_right hq]
    have hnum : (0 : ℝ) < q.num.toNat := by exact_mod_cast AzRat.num_toNat_pos q hq
    have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
    cases hs : q.sign
    · have hneg : (AzRat.toRat q : ℝ) < 0 := by
        rw [coe_toRat_eq, hs]
        simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
        exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden
      rw [Spec.rsqrt_coe_neg _ hneg, roundVal_none]; rfl
    · have hval : (AzRat.toRat q : ℝ) = (q.num.toNat : ℝ) / q.den.toNat := by
        rw [coe_toRat_eq, hs]; simp
      rw [ite_eq_left rfl, hval, Spec.rsqrt_coe _ (div_pos hnum hden), ← Real.sqrt_inv, inv_div,
        sqrtRatCore_eq q.den q.num q.den_nz hq]

end Azurite.AzFloat
