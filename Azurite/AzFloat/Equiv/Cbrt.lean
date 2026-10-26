/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cbrt
import Azurite.AzFloat.Equiv.NegRound
import Azurite.AzFloat.Equiv.Sqrt
import Azurite.AzInt.Equiv.DivMod
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.RootInt

/-!
# Correctness of the cube root

`realCbrt` is the real cube root (odd, `realCbrt x ^ 3 = x`), `Spec.cbrt` its extended-real
lift (`±∞` fixed); `cbrtPrecRound_eq_liftVal` says `cbrtPrecRound` is the lifted specification,
via `cbrtCore_eq` (the integer cube root determines the floor, the exactness and the midpoint
comparison that `roundFromFloor` needs) and `roundVal_neg` for negative inputs.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The real cube root -/

/-- The real cube root: `x^(1/3)` for `x ≥ 0`, `−(−x)^(1/3)` for `x < 0`. -/
noncomputable def realCbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ (((3 : ℕ) : ℝ)⁻¹) else -((-x) ^ (((3 : ℕ) : ℝ)⁻¹))

theorem realCbrt_of_nonneg {x : ℝ} (hx : 0 ≤ x) : realCbrt x = x ^ (((3 : ℕ) : ℝ)⁻¹) := by
  unfold realCbrt
  rw [ite_eq_left hx]

theorem realCbrt_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ realCbrt x := by
  rw [realCbrt_of_nonneg hx]
  exact Real.rpow_nonneg hx _

theorem realCbrt_pow_three (x : ℝ) : realCbrt x ^ 3 = x := by
  unfold realCbrt
  split_ifs with hx
  · exact Real.rpow_inv_natCast_pow hx (by norm_num)
  · rw [Odd.neg_pow (by decide : Odd 3), Real.rpow_inv_natCast_pow (by linarith) (by norm_num),
      neg_neg]

/-- The nonnegative cube root is determined by its cube. -/
theorem realCbrt_eq_of_pow_three {x y : ℝ} (hy : 0 ≤ y) (h : y ^ 3 = x) : realCbrt x = y := by
  rw [← h, realCbrt_of_nonneg (by positivity)]
  exact Real.pow_rpow_inv_natCast hy (by norm_num)

theorem realCbrt_neg (x : ℝ) : realCbrt (-x) = -realCbrt x := by
  rcases lt_trichotomy x 0 with h | h | h
  · unfold realCbrt
    rw [ite_eq_left (by linarith), ite_eq_right (not_le.mpr h), neg_neg]
  · subst h
    unfold realCbrt
    simp only [neg_zero, le_refl, ↓reduceIte]
    rw [Real.zero_rpow (by norm_num), neg_zero]
  · unfold realCbrt
    rw [ite_eq_right (not_le.mpr (by linarith)), ite_eq_left h.le, neg_neg]

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real cube root: `∛(±∞) = ±∞`, the real cube root otherwise. -/
noncomputable def cbrt (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a = ⊥ then some ⊥ else some ((realCbrt a.toReal : ℝ) : EReal)

theorem cbrt_coe (r : ℝ) : cbrt (r : EReal) = some ((realCbrt r : ℝ) : EReal) := by
  unfold cbrt
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem cbrt_top : cbrt ⊤ = some ⊤ := by
  unfold cbrt
  rw [ite_eq_left rfl]

@[simp] theorem cbrt_bot : cbrt ⊥ = some ⊥ := by
  unfold cbrt
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

@[simp] theorem cbrt_zero : cbrt 0 = some 0 := by
  rw [← EReal.coe_zero, cbrt_coe, realCbrt_eq_of_pow_three le_rfl (by norm_num), EReal.coe_zero]

end Spec

/-! ### The core -/

set_option maxHeartbeats 1000000 in
/-- The cube root of the exact value of a float at the right scale. -/
theorem cbrtCore_eq (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    cbrtCore e (coreSignificand q m) q p mode
      = roundVal p mode
          (some ((realCbrt (finiteVal true e (coreSignificand q m)) : ℝ) : EReal)) := by
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
  unfold cbrtCore
  simp only []
  have h3I : ((AzNat.ofNat 3).toAzInt).toInt = 3 := by rw [toInt_toAzInt, AzNat.toNat_ofNat]; rfl
  -- the residue `δ = (−e) mod 3`
  set δ : ℕ := ((-e) % (AzNat.ofNat 3).toAzInt).abs.toNat with hδ_def
  have hδ : (δ : ℤ) = (-e.toInt) % 3 := by
    rw [hδ_def, AzInt.abs_toNat_eq]
    show |(AzInt.mod (-e) (AzNat.ofNat 3).toAzInt).toInt| = _
    rw [AzInt.toInt_mod, AzInt.toInt_neg, h3I]
    exact abs_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hδle : δ ≤ 2 := by
    have h1 : (-e.toInt) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have h2 : 0 ≤ (-e.toInt) % 3 := Int.emod_nonneg _ (by norm_num)
    omega
  clear_value δ
  -- the shift `t` and the exponent `w`
  set t : AzInt := (AzNat.ofNat (3 * p)).toAzInt - (AzNat.ofNat (q + δ)).toAzInt with ht_def
  have htI : t.toInt = 3 * (p : ℤ) - q - δ := by
    rw [ht_def, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat]; push_cast; ring
  clear_value t
  set w' : AzInt := e - (AzNat.ofNat (3 * p)).toAzInt + (AzNat.ofNat δ).toAzInt with hw'_def
  have hw'I : w'.toInt = e.toInt - 3 * p + δ := by
    rw [hw'_def, AzInt.toInt_add, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat]; push_cast; ring
  clear_value w'
  set w := w' / (AzNat.ofNat 3).toAzInt with hw_def
  have hwI : 3 * w.toInt = w'.toInt := by
    rw [hw_def]
    show 3 * (AzInt.div w' (AzNat.ofNat 3).toAzInt).toInt = _
    rw [AzInt.toInt_div, h3I]
    have : w'.toInt % 3 = 0 := by rw [hw'I]; omega
    omega
  clear_value w
  have htw : t.toInt + 3 * w.toInt = e.toInt - q := by rw [hwI, hw'I, htI]; ring
  -- the scaled significand `M = N · 2^t` and its truncation
  set Mr : ℝ := N * (2 : ℝ) ^ t.toInt with hMr
  have hMr0 : 0 < Mr := by positivity
  obtain ⟨hMle, hMlt, hMex⟩ := scaled_floor n t
  rw [← hN] at hMle hMlt hMex
  set M := if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat with hM_def
  clear_value M
  rw [← hMr] at hMle hMlt hMex
  -- bounds on `M`: `2^(3p−3) ≤ Mr < 2^(3p)`
  have hMlo : (2 : ℝ) ^ (3 * (p : ℤ) - 3) ≤ Mr := by
    rw [hMr, htI]
    calc (2 : ℝ) ^ (3 * (p : ℤ) - 3) ≤ 2 ^ ((q : ℤ) - 1) * 2 ^ (3 * (p : ℤ) - q - δ) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ ≤ N * 2 ^ (3 * (p : ℤ) - q - δ) :=
          mul_le_mul_of_nonneg_right hb.1 (zpow_pos (by norm_num) _).le
  have hMhi : Mr < (2 : ℝ) ^ (3 * (p : ℤ)) := by
    rw [hMr, htI]
    calc N * 2 ^ (3 * (p : ℤ) - q - δ) < 2 ^ (q : ℤ) * 2 ^ (3 * (p : ℤ) - q - δ) :=
          mul_lt_mul_of_pos_right hb.2 (zpow_pos (by norm_num) _)
      _ ≤ 2 ^ (3 * (p : ℤ)) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  -- the integer cube root
  set c := AzNat.rootInt M 3 with hc
  clear_value c
  have hcN : c.toNat = AzNat.rootIntNat M.toNat 3 := by rw [hc]; exact AzNat.toNat_rootInt M 3
  obtain ⟨hc3, hlt3⟩ := AzNat.rootIntNat_spec M.toNat 3 (by norm_num)
  rw [← hcN] at hc3 hlt3
  set y : ℝ := realCbrt Mr with hy_def
  have hy0 : 0 ≤ y := realCbrt_nonneg hMr0.le
  have hy3 : y ^ 3 = Mr := realCbrt_pow_three Mr
  have hc0 : (0 : ℝ) ≤ c.toNat := Nat.cast_nonneg _
  have hc3R : (c.toNat : ℝ) ^ 3 ≤ (M.toNat : ℝ) := by exact_mod_cast hc3
  have hlt3R : (M.toNat : ℝ) + 1 ≤ ((c.toNat : ℝ) + 1) ^ 3 := by
    have : ((M.toNat + 1 : ℕ) : ℝ) ≤ (((c.toNat + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hlt3
    push_cast at this
    exact this
  have hlo : (c.toNat : ℝ) ≤ y := by
    rw [← pow_le_pow_iff_left₀ hc0 hy0 (by norm_num : (3 : ℕ) ≠ 0), hy3]
    linarith
  have hhi : y < c.toNat + 1 := by
    rw [← pow_lt_pow_iff_left₀ hy0 (by positivity) (by norm_num : (3 : ℕ) ≠ 0), hy3]
    linarith
  have hex : (decide (c.pow 3 = M) && (t.sign || n.isMultipleOfPow2 t.abs.toNat)) = true ↔
      y = c.toNat := by
    rw [Bool.and_eq_true, decide_eq_true_eq, ← hMex]
    constructor
    · rintro ⟨hr, hM⟩
      have hr' : (c.toNat : ℝ) ^ 3 = (M.toNat : ℝ) := by
        have := congrArg AzNat.toNat hr
        rw [AzNat.toNat_pow] at this
        exact_mod_cast this
      rw [← pow_left_inj₀ hy0 hc0 (by norm_num : (3 : ℕ) ≠ 0), hy3, hr', hM]
    · intro h
      have hMeq : Mr = (M.toNat : ℝ) := by
        apply le_antisymm _ hMle
        rw [← hy3, h]
        exact hc3R
      refine ⟨?_, hMeq⟩
      have hM3 : (M.toNat : ℝ) = ((c.toNat ^ 3 : ℕ) : ℝ) := by
        rw [← hMeq, ← hy3, h]; push_cast; ring
      apply AzNat.toNat_injective
      rw [AzNat.toNat_pow]
      exact_mod_cast hM3.symm
  have hmid : compareScaled n (t + (AzNat.ofNat 3).toAzInt)
      (((c.shiftLeft 1).addUInt64 1).pow 3)
      = compare y ((c.toNat : ℝ) + 1 / 2) := by
    have htt : (t + (AzNat.ofNat 3).toAzInt).toInt = t.toInt + 3 := by
      rw [AzInt.toInt_add, h3I]
    have hL : N * (2 : ℝ) ^ (t.toInt + 3) = Mr * 8 := by
      rw [hMr, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), show (2 : ℝ) ^ (3 : ℤ) = 8 by norm_num]; ring
    have hRt : ((((c.shiftLeft 1).addUInt64 1).pow 3).toNat : ℝ)
        = ((c.toNat : ℝ) + 1 / 2) ^ 3 * 8 := by
      rw [AzNat.toNat_pow, AzNat.toNat_addUInt64, AzNat.toNat_shiftLeft, UInt64.toNat_one]
      push_cast; ring
    rw [compareScaled_eq, htt, ← hN, hL, hRt, compare_mul_right_pos _ _ _ (by norm_num), ← hy3]
    have hmid_pos : (0 : ℝ) ≤ (c.toNat : ℝ) + 1 / 2 := by positivity
    rcases lt_trichotomy y ((c.toNat : ℝ) + 1 / 2) with h | h | h
    · rw [compare_lt_iff_lt.mpr h]
      exact compare_lt_iff_lt.mpr (pow_lt_pow_left₀ h hy0 (by norm_num))
    · rw [compare_eq_iff_eq.mpr h]
      exact compare_eq_iff_eq.mpr (by rw [h])
    · rw [compare_gt_iff_gt.mpr h]
      exact compare_gt_iff_gt.mpr (pow_lt_pow_left₀ h hmid_pos (by norm_num))
  obtain ⟨hR, htag⟩ := roundFromFloor_spec y c _ _ mode hlo hhi hex hmid
  set ro := roundFromFloor c (decide (c.pow 3 = M) && (t.sign || n.isMultipleOfPow2 t.abs.toNat))
    (compareScaled n (t + (AzNat.ofNat 3).toAzInt) (((c.shiftLeft 1).addUInt64 1).pow 3))
    mode with hro
  clear_value ro
  -- the exact value and its logarithm
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w.toInt := zpow_pos (by norm_num) _
  set v : ℝ := realCbrt (finiteVal true e n) with hv_def
  have hv : v = y * (2 : ℝ) ^ w.toInt := by
    rw [hv_def]
    apply realCbrt_eq_of_pow_three (by positivity)
    rw [mul_pow, hy3, finiteVal_true_eq, hs, ← hN, ← htw, zpow_add₀ (by norm_num),
      show (2 : ℝ) ^ (3 * w.toInt) = (2 ^ w.toInt) ^ 3 by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring,
      ← mul_assoc, ← hMr]
  clear_value v
  have hylo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ y := by
    rw [← pow_le_pow_iff_left₀ (zpow_pos (by norm_num) _).le hy0 (by norm_num : (3 : ℕ) ≠ 0), hy3,
      ← zpow_natCast, ← zpow_mul]
    convert hMlo using 2; push_cast; ring
  have hyhi : y < (2 : ℝ) ^ (p : ℤ) := by
    rw [← pow_lt_pow_iff_left₀ hy0 (zpow_pos (by norm_num) _).le (by norm_num : (3 : ℕ) ≠ 0), hy3,
      ← zpow_natCast, ← zpow_mul]
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

/-- Cube root is the float lift of `Spec.cbrt`. -/
theorem cbrtPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cbrtPrecRound x p mode = liftVal Spec.cbrt x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [cbrtPrecRound]
  | zero => simp [cbrtPrecRound]
  | finite s e q m hv =>
    simp only [cbrtPrecRound, toVal_finite, Option.bind_some, Spec.cbrt_coe]
    rw [ite_eq_right (NeZero.ne p)]
    cases s with
    | true =>
      simp only [↓reduceIte]
      rw [finiteVal_eq_core true e hv, cbrtCore_eq e hv p mode]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [finiteVal_eq_core false e hv, finiteVal_false, realCbrt_neg, roundVal_neg,
        cbrtCore_eq e hv p (-mode)]

end Azurite.AzFloat
