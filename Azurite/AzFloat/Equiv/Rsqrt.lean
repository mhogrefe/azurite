/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.RoundScaled
import Azurite.AzFloat.Rsqrt
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Square.Dispatch
import Azurite.AzNat.Equiv.SqrtRem
import Mathlib.Analysis.Real.Sqrt

/-!
# Correctness of the reciprocal square root

`Spec.rsqrt` is `1 / √x`, undefined for negative values (`+∞` at `0`, `0` at `+∞`);
`rsqrtPrecRound_eq_liftVal` says `rsqrtPrecRound` is the lifted specification, via `rsqrtCore_eq`
and the three scalings `D` that put `√(2^D / n)` in `[2^(p−1), 2^p)`.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real reciprocal square root: undefined (`NaN`) on negatives (including `−∞`),
`0 ↦ ∞`, `∞ ↦ 0`. -/
noncomputable def rsqrt (a : EReal) : Option EReal :=
  if a < 0 then none else if a = 0 then some ⊤ else if a = ⊤ then some 0
  else some (((Real.sqrt a.toReal)⁻¹ : ℝ) : EReal)

theorem rsqrt_coe (r : ℝ) (hr : 0 < r) :
    rsqrt (r : EReal) = some (((Real.sqrt r)⁻¹ : ℝ) : EReal) := by
  unfold rsqrt
  rw [ite_eq_right (not_lt.mpr (EReal.coe_nonneg.mpr hr.le)),
    ite_eq_right (fun h => hr.ne' (EReal.coe_eq_zero.mp h)), ite_eq_right (EReal.coe_ne_top r),
    EReal.toReal_coe]

theorem rsqrt_coe_neg (r : ℝ) (hr : r < 0) : rsqrt (r : EReal) = none := by
  unfold rsqrt
  rw [ite_eq_left (EReal.coe_neg'.mpr hr)]

@[simp] theorem rsqrt_zero : rsqrt 0 = some ⊤ := by
  unfold rsqrt
  rw [ite_eq_right (lt_irrefl 0), ite_eq_left rfl]

@[simp] theorem rsqrt_top : rsqrt ⊤ = some 0 := by
  unfold rsqrt
  rw [ite_eq_right (not_lt.mpr le_top), ite_eq_right EReal.top_ne_zero, ite_eq_left rfl]

@[simp] theorem rsqrt_bot : rsqrt ⊥ = none := by
  unfold rsqrt
  rw [ite_eq_left EReal.bot_lt_zero]

end Spec

/-- The reciprocal square root of the exact value of a float, at the right scale. -/
theorem rsqrtCore_eq (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    rsqrtCore e (coreSignificand q m) q p mode
      = roundVal p mode
          (some (((Real.sqrt (finiteVal true e (coreSignificand q m)))⁻¹ : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  set n := coreSignificand q m with hn
  have hn0 : n ≠ 0 := coreSignificand_ne_zero hv
  have hs : n.size = q := size_coreSignificand hv
  have hq : 0 < q := hv.pos
  clear_value n
  obtain ⟨hNlo, hNhi⟩ := toNat_bounds_of_ne_zero n hn0
  rw [hs] at hNlo hNhi
  have hb : (2 : ℝ) ^ ((q : ℤ) - 1) ≤ (n.toNat : ℝ) ∧ (n.toNat : ℝ) < (2 : ℝ) ^ (q : ℤ) := by
    constructor
    · rw [show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hNlo
    · rw [zpow_natCast]; exact_mod_cast hNhi
  set N : ℝ := (n.toNat : ℝ) with hN
  have hNpos : 0 < N := lt_of_lt_of_le (zpow_pos (by norm_num) _) hb.1
  clear_value N
  unfold rsqrtCore
  simp only []
  -- the parity and the boundary flag
  set odd := e.isOdd with hodd_def
  have hodd : odd = true ↔ Odd e.toInt := by rw [hodd_def]; exact AzInt.isOdd_iff e
  set bnd := (odd && decide (n = (1 : AzNat).shiftLeft (q - 1))) with hbnd_def
  have hbnd : bnd = true ↔ (odd = true ∧ n.toNat = 2 ^ (q - 1)) := by
    rw [hbnd_def, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h2, AzNat.toNat_shiftLeft, AzNat.toNat_one, one_mul]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, AzNat.toNat_injective ?_⟩
      rw [h2, AzNat.toNat_shiftLeft, AzNat.toNat_one, one_mul]
  clear_value odd bnd
  -- `D`, `f`, `w`
  set D : ℕ := (if odd then (if bnd then 2 * p + q - 3 else 2 * p + q - 1) else 2 * p + q - 2)
    with hD_def
  set f : AzInt := (if (!odd || bnd) then (1 : AzInt) else 0) - e.shiftRight 1 with hf_def
  have hfI : f.toInt = (if (!odd || bnd) then 1 else 0) - e.toInt / 2 := by
    rw [hf_def, AzInt.toInt_sub, AzInt.toInt_shiftRight_one]
    split_ifs <;> rfl
  clear_value f
  set w := f - (AzNat.ofNat p).toAzInt with hw_def
  have hwI : w.toInt = f.toInt - p := by
    rw [hw_def, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
  clear_value w
  -- the key relation `D + 2w = q − e`, by cases
  have hkey : (D : ℤ) + 2 * w.toInt = q - e.toInt := by
    rw [hwI, hfI, hD_def]
    rcases Bool.eq_false_or_eq_true odd with ho | ho
    · -- odd
      have hmod : e.toInt % 2 = 1 := Int.odd_iff.mp (hodd.mp ho)
      rcases Bool.eq_false_or_eq_true bnd with hbo | hbo
      · simp only [ho, hbo, ↓reduceIte, Bool.not_true, Bool.false_or]
        push_cast [show 3 ≤ 2 * p + q by omega]
        omega
      · simp only [ho, hbo, ↓reduceIte, Bool.not_true, Bool.false_or, Bool.false_eq_true]
        push_cast [show 1 ≤ 2 * p + q by omega]
        omega
    · have hmod : e.toInt % 2 = 0 := by
        have hev : ¬ Odd e.toInt := fun h => by rw [← hodd] at h; simp [ho] at h
        rw [Int.not_odd_iff_even, Int.even_iff] at hev; exact hev
      simp only [ho, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.false_eq_true]
      push_cast [show 2 ≤ 2 * p + q by omega]
      omega
  -- the scaled quotient `r = 2^D / N` and its bounds `2^(2p−2) ≤ r < 2^(2p)`
  set Mr : ℝ := (2 : ℝ) ^ (D : ℕ) / N with hMr
  have hMr0 : 0 < Mr := by positivity
  have hMlo : (2 : ℝ) ^ (2 * (p : ℤ) - 2) ≤ Mr := by
    rw [hMr, le_div_iff₀ hNpos, hD_def]
    rcases Bool.eq_false_or_eq_true odd with ho | ho
    · rcases Bool.eq_false_or_eq_true bnd with hbo | hbo
      · obtain ⟨-, hn2⟩ := hbnd.mp hbo
        have hN2 : N = (2 : ℝ) ^ ((q : ℤ) - 1) := by
          rw [hN, hn2, show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]; push_cast; rfl
        rw [ho, hbo, ite_eq_left rfl, ite_eq_left rfl, hN2, ← zpow_natCast,
          ← zpow_add₀ (by norm_num)]
        apply zpow_le_zpow_right₀ (by norm_num)
        push_cast [show 3 ≤ 2 * p + q by omega]; omega
      · rw [ho, hbo, ite_eq_left rfl, ite_eq_right (by simp)]
        calc (2 : ℝ) ^ (2 * (p : ℤ) - 2) * N ≤ 2 ^ (2 * (p : ℤ) - 2) * 2 ^ (q : ℤ) :=
              mul_le_mul_of_nonneg_left hb.2.le (zpow_pos (by norm_num) _).le
          _ ≤ (2 : ℝ) ^ (2 * p + q - 1 : ℕ) := by
              rw [← zpow_add₀ (by norm_num), ← zpow_natCast]
              apply zpow_le_zpow_right₀ (by norm_num)
              push_cast [show 1 ≤ 2 * p + q by omega]; omega
    · rw [ho, ite_eq_right (by simp)]
      calc (2 : ℝ) ^ (2 * (p : ℤ) - 2) * N ≤ 2 ^ (2 * (p : ℤ) - 2) * 2 ^ (q : ℤ) :=
            mul_le_mul_of_nonneg_left hb.2.le (zpow_pos (by norm_num) _).le
        _ = (2 : ℝ) ^ (2 * p + q - 2 : ℕ) := by
            rw [← zpow_add₀ (by norm_num), ← zpow_natCast]
            congr 1
            push_cast [show 2 ≤ 2 * p + q by omega]; ring
  have hMhi : Mr < (2 : ℝ) ^ (2 * (p : ℤ)) := by
    rw [hMr, div_lt_iff₀ hNpos, hD_def]
    rcases Bool.eq_false_or_eq_true odd with ho | ho
    · rcases Bool.eq_false_or_eq_true bnd with hbo | hbo
      · obtain ⟨-, hn2⟩ := hbnd.mp hbo
        have hN2 : N = (2 : ℝ) ^ ((q : ℤ) - 1) := by
          rw [hN, hn2, show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]; push_cast; rfl
        rw [ho, hbo, ite_eq_left rfl, ite_eq_left rfl, hN2, ← zpow_add₀ (by norm_num),
          ← zpow_natCast]
        apply zpow_lt_zpow_right₀ (by norm_num)
        push_cast [show 3 ≤ 2 * p + q by omega]; omega
      · -- `N > 2^(q−1)` strictly
        have hne : n.toNat ≠ 2 ^ (q - 1) := fun h => by
          have := hbnd.mpr ⟨ho, h⟩; rw [this] at hbo; exact Bool.noConfusion hbo
        have hNgt : (2 : ℝ) ^ ((q : ℤ) - 1) < N := by
          rcases lt_or_eq_of_le hb.1 with h | h
          · exact h
          · exfalso; apply hne
            have : (n.toNat : ℝ) = ((2 ^ (q - 1) : ℕ) : ℝ) := by
              rw [← hN, ← h, show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]
              push_cast; rfl
            exact_mod_cast this
        rw [ho, hbo, ite_eq_left rfl, ite_eq_right (by simp)]
        calc (2 : ℝ) ^ (2 * p + q - 1 : ℕ) = 2 ^ (2 * (p : ℤ)) * 2 ^ ((q : ℤ) - 1) := by
              rw [← zpow_add₀ (by norm_num), ← zpow_natCast]
              congr 1
              push_cast [show 1 ≤ 2 * p + q by omega]; ring
          _ < 2 ^ (2 * (p : ℤ)) * N := mul_lt_mul_of_pos_left hNgt (zpow_pos (by norm_num) _)
    · rw [ho, ite_eq_right (by simp)]
      calc (2 : ℝ) ^ (2 * p + q - 2 : ℕ) = 2 ^ (2 * (p : ℤ) - 1) * 2 ^ ((q : ℤ) - 1) := by
            rw [← zpow_add₀ (by norm_num), ← zpow_natCast]
            congr 1
            push_cast [show 2 ≤ 2 * p + q by omega]; ring
        _ ≤ 2 ^ (2 * (p : ℤ) - 1) * N :=
            mul_le_mul_of_nonneg_left hb.1 (zpow_pos (by norm_num) _).le
        _ < 2 ^ (2 * (p : ℤ)) * N := by
            apply mul_lt_mul_of_pos_right _ hNpos
            exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  -- the integer square root of `⌊r⌋`
  set pow := (1 : AzNat).shiftLeft D with hpow
  have hpowN : pow.toNat = 2 ^ D := by rw [hpow, AzNat.toNat_shiftLeft, AzNat.toNat_one, one_mul]
  clear_value pow
  set Q := pow / n with hQ
  have hQN : Q.toNat = 2 ^ D / n.toNat := by rw [hQ, AzNat.toNat_div, hpowN]
  clear_value Q
  have hQle : (Q.toNat : ℝ) ≤ Mr := by
    rw [hQN, hMr, le_div_iff₀ hNpos, hN]
    exact_mod_cast Nat.div_mul_le_self (2 ^ D) n.toNat
  have hQlt : Mr < Q.toNat + 1 := by
    rw [hQN, hMr, div_lt_iff₀ hNpos, hN]
    have := Nat.lt_div_mul_add (a := 2 ^ D) (Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn0))
    have h' : 2 ^ D < (2 ^ D / n.toNat + 1) * n.toNat := by
      have := Nat.div_add_mod (2 ^ D) n.toNat
      have := Nat.mod_lt (2 ^ D) (Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn0))
      nlinarith
    exact_mod_cast h'
  set sr := AzNat.sqrtRem Q with hsr
  clear_value sr
  have hsN : sr.1.toNat = Nat.sqrt Q.toNat := by rw [hsr]; exact AzNat.toNat_sqrtRem_fst Q
  set y : ℝ := Real.sqrt Mr with hy_def
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hsq_le : Nat.sqrt Q.toNat ^ 2 ≤ Q.toNat := Nat.sqrt_le' _
  have hlt_sq : Q.toNat < (Nat.sqrt Q.toNat + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hlo : (sr.1.toNat : ℝ) ≤ y := by
    rw [hsN, hy_def]
    exact le_trans Real.nat_sqrt_le_real_sqrt (Real.sqrt_le_sqrt hQle)
  have hhi : y < sr.1.toNat + 1 := by
    rw [hsN, hy_def]
    calc Real.sqrt Mr < Real.sqrt (Q.toNat + 1) := Real.sqrt_lt_sqrt hMr0.le hQlt
      _ ≤ Nat.sqrt Q.toNat + 1 := by
          rw [Real.sqrt_le_left (by positivity)]
          exact_mod_cast hlt_sq
  have hex : (compare (AzNat.square sr.1 * n) pow == .eq) = true ↔ y = sr.1.toNat := by
    rw [beq_iff_eq, show compare (AzNat.square sr.1 * n) pow = AzNat.compare _ _ from rfl,
      AzNat.compare_eq_compare_toNat, ← compare_natCast, compare_eq_iff_eq, AzNat.toNat_mul,
      AzNat.toNat_square, hpowN, hy_def, Real.sqrt_eq_iff_eq_sq hMr0.le (Nat.cast_nonneg _), hMr,
      div_eq_iff hNpos.ne', hN]
    push_cast
    constructor <;> intro h <;> linarith
  have hmid : compare ((1 : AzNat).shiftLeft (D + 2))
      (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1) * n)
      = compare y ((sr.1.toNat : ℝ) + 1 / 2) := by
    rw [show compare ((1 : AzNat).shiftLeft (D + 2))
        (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1) * n) = AzNat.compare _ _ from rfl,
      AzNat.compare_eq_compare_toNat, ← compare_natCast,
      AzNat.toNat_shiftLeft, AzNat.toNat_one, one_mul, AzNat.toNat_mul, AzNat.toNat_square,
      AzNat.toNat_addUInt64, AzNat.toNat_shiftLeft, UInt64.toNat_one]
    push_cast
    rw [← hN]
    have hmid_pos : (0 : ℝ) < (sr.1.toNat : ℝ) + 1 / 2 := by positivity
    have hL : (2 : ℝ) ^ (D + 2) = Mr * (4 * N) := by
      rw [hMr, pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num, mul_comm (4 : ℝ) N, ← mul_assoc,
        div_mul_cancel₀ _ hNpos.ne']
    have hRt : ((sr.1.toNat : ℝ) * 2 + 1) ^ 2 * N
        = ((sr.1.toNat : ℝ) + 1 / 2) ^ 2 * (4 * N) := by ring
    rw [hL, hRt, compare_mul_right_pos _ _ _ (by positivity), hy_def]
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
  set ro := roundFromFloor sr.1 (compare (AzNat.square sr.1 * n) pow == .eq)
    (compare ((1 : AzNat).shiftLeft (D + 2))
      (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1) * n)) mode with hro
  clear_value ro
  -- the exact value `v = 1/√x = y · 2^w`
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w.toInt := zpow_pos (by norm_num) _
  set v : ℝ := (Real.sqrt (finiteVal true e n))⁻¹ with hv_def
  have hv : v = y * (2 : ℝ) ^ w.toInt := by
    rw [hv_def, hy_def, finiteVal_true_eq, hs, ← hN, ← Real.sqrt_inv, mul_inv,
      show ((2 : ℝ) ^ (e.toInt - q))⁻¹ = 2 ^ ((q : ℤ) - e.toInt) by
        rw [← zpow_neg]; congr 1; ring,
      show ((q : ℤ) - e.toInt) = D + 2 * w.toInt by rw [hkey], zpow_add₀ (by norm_num),
      show (2 : ℝ) ^ (2 * w.toInt) = (2 ^ w.toInt) ^ 2 by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring,
      zpow_natCast, ← mul_assoc, ← div_eq_inv_mul, ← hMr, Real.sqrt_mul hMr0.le,
      Real.sqrt_sq h2w.le]
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

/-- Reciprocal square root is the float lift of `Spec.rsqrt`. -/
theorem rsqrtPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    rsqrtPrecRound x p mode = liftVal Spec.rsqrt x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [rsqrtPrecRound]
  | zero => simp [rsqrtPrecRound]
  | finite s e q m hv =>
    cases s with
    | true =>
      simp only [rsqrtPrecRound, toVal_finite, Option.bind_some, ↓reduceIte]
      rw [finiteVal_eq_core true e hv,
        Spec.rsqrt_coe _ (finiteVal_true_pos' e _ (coreSignificand_ne_zero hv)),
        rsqrtCore_eq e hv p mode]
    | false =>
      simp only [rsqrtPrecRound, toVal_finite, Option.bind_some, Bool.false_eq_true, ↓reduceIte]
      rw [finiteVal_eq_core false e hv, finiteVal_false,
        Spec.rsqrt_coe_neg _ (neg_neg_iff_pos.mpr
          (finiteVal_true_pos' e _ (coreSignificand_ne_zero hv))), roundVal_none]

end Azurite.AzFloat
