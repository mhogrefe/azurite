/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.LogBase
import Azurite.AzRat.Equiv.LogBase2
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Pow
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Correctness of `AzRat.floorLogBaseAbs`

`floorLogBaseAbs_eq : floorLogBaseAbs b q = Int.log b |toRat q|` for `2 ≤ b` and `q ≠ 0`
(and the `⌊logb b |q|⌋` form via `Real.floor_logb_natCast`).  The binary search keeps the
bracket `b^lo ≤ |q| < b^hi`, and `cmpPowAbs` is `compare (b^e) |q|` by cross-multiplication;
the power-of-two shortcut is `Int.log (2^k) x = Int.log 2 x / k`.
-/

namespace Azurite.AzRat

open Real

/-- `|toRat q|` as a quotient of the limb values. -/
lemma abs_toRat_eq (q : AzRat) :
    |(toRat q : ℝ)| = (q.num.toNat : ℝ) / (q.den.toNat : ℝ) := by
  have hnum : (toRat q).num = if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ) := rfl
  have hden : (toRat q).den = q.den.toNat := rfl
  rw [Rat.cast_def, abs_div, hnum, hden]
  congr 1
  · cases q.sign <;> push_cast <;> simp
  · exact abs_of_nonneg (by positivity)

/-- The denominator is positive. -/
lemma den_toNat_pos (q : AzRat) : 0 < q.den.toNat :=
  Nat.pos_of_ne_zero (fun h => q.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)))

/-- A nonzero numerator is positive. -/
lemma num_toNat_pos (q : AzRat) (hq : q.num ≠ 0) : 0 < q.num.toNat :=
  Nat.pos_of_ne_zero (fun h => hq (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)))

/-- `|toRat q| > 0` for a nonzero numerator. -/
lemma abs_toRat_pos (q : AzRat) (hq : q.num ≠ 0) : 0 < |(toRat q : ℝ)| := by
  rw [abs_toRat_eq]
  have h1 := num_toNat_pos q hq
  have h2 := den_toNat_pos q
  positivity

private lemma compare_natCast (x y : ℕ) :
    compare (x : ℝ) (y : ℝ) = compare x y := by
  rcases lt_trichotomy x y with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (Nat.cast_lt.mpr h)]
  · subst h; rw [compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (Nat.cast_lt.mpr h)]

private lemma compare_div_div (a b c d : ℝ) (hb : 0 < b) (hd : 0 < d) :
    compare (a / b) (c / d) = compare (a * d) (c * b) := by
  rcases lt_trichotomy (a / b) (c / d) with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr ((div_lt_div_iff₀ hb hd).mp h)]
  · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr ((div_eq_div_iff hb.ne' hd.ne').mp h)]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr ((div_lt_div_iff₀ hd hb).mp h)]

/-- `cmpPowAbs b e q` compares `b^e` with `|toRat q|`. -/
lemma cmpPowAbs_eq (b : UInt64) (hb : 0 < b.toNat) (e : ℤ) (q : AzRat) :
    cmpPowAbs b e q = compare ((b.toNat : ℝ) ^ e) |(toRat q : ℝ)| := by
  have hD : (0 : ℝ) < q.den.toNat := by exact_mod_cast den_toNat_pos q
  have hbR : (0 : ℝ) < b.toNat := by exact_mod_cast hb
  rw [abs_toRat_eq]
  cases e with
  | ofNat n =>
    simp only [cmpPowAbs]
    rw [AzNat.compare_eq_compare_toNat, AzNat.toNat_mul, AzNat.toNat_pow, AzNat.toNat_ofNat]
    rw [show ((b.toNat : ℝ) ^ (Int.ofNat n : ℤ)) = ((b.toNat ^ n : ℕ) : ℝ) / 1 from by
      rw [div_one, Int.ofNat_eq_natCast, zpow_natCast, Nat.cast_pow]]
    rw [compare_div_div _ _ _ _ one_pos hD, mul_one, ← Nat.cast_mul, compare_natCast,
      Nat.mul_comm]
  | negSucc n =>
    simp only [cmpPowAbs]
    rw [AzNat.compare_eq_compare_toNat, AzNat.toNat_mul, AzNat.toNat_pow, AzNat.toNat_ofNat]
    rw [zpow_negSucc, inv_eq_one_div,
      compare_div_div _ _ _ _ (pow_pos hbR _) hD, one_mul, ← Nat.cast_pow, ← Nat.cast_mul,
      compare_natCast]

/-- The binary search returns `Int.log b |q|` from any bracket `b^lo ≤ |q| < b^hi`. -/
lemma floorLogSearch_eq (b : UInt64) (hb : 1 < b.toNat) (q : AzRat) (hq : q.num ≠ 0)
    (lo hi : ℤ) (hlo : (b.toNat : ℝ) ^ lo ≤ |(toRat q : ℝ)|)
    (hhi : |(toRat q : ℝ)| < (b.toNat : ℝ) ^ hi) :
    floorLogSearch b q lo hi = Int.log b.toNat |(toRat q : ℝ)| := by
  have hpos := abs_toRat_pos q hq
  have hbR : (1 : ℝ) < b.toNat := by exact_mod_cast hb
  induction h_sub : (hi - lo).toNat using Nat.strong_induction_on generalizing lo hi with
  | _ n ih =>
  rw [floorLogSearch]
  split_ifs with h
  · dsimp only
    set mid := (lo + hi) / 2 with hmid_def
    have hmid1 : lo < mid := by omega
    have hmid2 : mid < hi := by omega
    rw [cmpPowAbs_eq b (by omega) mid q]
    rcases lt_trichotomy ((b.toNat : ℝ) ^ mid) |(toRat q : ℝ)| with hlt | heq | hgt
    · rw [compare_lt_iff_lt.mpr hlt]
      exact ih _ (by omega) mid hi hlt.le hhi rfl
    · rw [compare_eq_iff_eq.mpr heq]
      exact ih _ (by omega) mid hi heq.le hhi rfl
    · rw [compare_gt_iff_gt.mpr hgt]
      exact ih _ (by omega) lo mid hlo hgt rfl
  · have hlohi : lo < hi := by
      by_contra hcon
      push Not at hcon
      have : (b.toNat : ℝ) ^ hi ≤ (b.toNat : ℝ) ^ lo := zpow_le_zpow_right₀ hbR.le hcon
      linarith
    have hhi' : hi = lo + 1 := by omega
    rw [hhi'] at hhi
    apply le_antisymm
    · exact (Int.zpow_le_iff_le_log hb hpos).mp hlo
    · have := (Int.lt_zpow_iff_log_lt hb hpos).mp hhi
      omega

/-- `Int.log (2^k) x = Int.log 2 x / k` for `0 < k` and `0 < x`. -/
private lemma int_log_pow_two (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : 0 < x) :
    Int.log (2 ^ k) x = Int.log 2 x / (k : ℤ) := by
  have hb : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  set L := Int.log 2 x with hL
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hdiv := Int.emod_def L k
  have hr0 := Int.emod_nonneg L hkZ.ne'
  have hrk := Int.emod_lt_of_pos L hkZ
  set d := L / (k : ℤ) with hd
  set r := L % (k : ℤ) with hr
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k : ℤ) := by push_cast; rw [zpow_natCast]
  have h2 : (1 : ℝ) < 2 := by norm_num
  apply le_antisymm
  · -- Int.log (2^k) x ≤ d  ⟸  x < (2^k)^(d+1)
    have hx_lt : x < (2 : ℝ) ^ (L + 1) := by
      exact_mod_cast Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) x
    have hle : L + 1 ≤ (k : ℤ) * (d + 1) := by nlinarith
    have : x < ((2 ^ k : ℕ) : ℝ) ^ (d + 1) := by
      rw [hcast, ← zpow_mul]
      exact lt_of_lt_of_le hx_lt (zpow_le_zpow_right₀ h2.le hle)
    have := (Int.lt_zpow_iff_log_lt hb hx).mp this
    omega
  · -- d ≤ Int.log (2^k) x  ⟸  (2^k)^d ≤ x
    have hx_ge : (2 : ℝ) ^ L ≤ x := by
      exact_mod_cast Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) hx
    have hle : (k : ℤ) * d ≤ L := by nlinarith
    have : ((2 ^ k : ℕ) : ℝ) ^ d ≤ x := by
      rw [hcast, ← zpow_mul]
      exact le_trans (zpow_le_zpow_right₀ h2.le hle) hx_ge
    exact (Int.zpow_le_iff_le_log hb hx).mp this

/-- `floorLogBase2Abs` in `Int.log` form. -/
lemma floorLogBase2Abs_eq_log (q : AzRat) (hq : q.num ≠ 0) :
    floorLogBase2Abs q = Int.log 2 |(toRat q : ℝ)| := by
  rw [floorLogBase2Abs_eq q hq, ← Real.floor_logb_natCast (b := 2) (abs_toRat_pos q hq).le]
  norm_num

/-- Correctness of `floorLogBaseAbs`: it is `Int.log b |toRat q|`. -/
theorem floorLogBaseAbs_eq (b : UInt64) (hb : 2 ≤ b.toNat) (q : AzRat) (hq : q.num ≠ 0) :
    floorLogBaseAbs b q = Int.log b.toNat |(toRat q : ℝ)| := by
  have hpos := abs_toRat_pos q hq
  have hb1 : 1 < b.toNat := hb
  have hbR : (2 : ℝ) ≤ b.toNat := by exact_mod_cast hb
  have h2 : (1 : ℝ) < 2 := by norm_num
  unfold floorLogBaseAbs
  simp only [hq, ↓reduceIte]
  rw [floorLogBase2Abs_eq_log q hq]
  set L := Int.log 2 |(toRat q : ℝ)| with hL
  split_ifs with hpow
  · -- `b = 2^k`
    set k := b.toNat.log2 with hk
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0] at hpow; simp at hpow; omega
      · exact h0
    rw [← hpow]
    exact (int_log_pow_two k hk0 _ hpos).symm
  · apply floorLogSearch_eq b hb1 q hq
    · -- lower bound
      have hL_le : (2 : ℝ) ^ L ≤ |(toRat q : ℝ)| := by
        have h := Int.zpow_log_le_self (R := ℝ) (by norm_num : (1 : ℕ) < 2) hpos
        rw [Nat.cast_ofNat] at h
        exact h
      rcases le_or_gt L 0 with hL0 | hL0
      · rw [min_eq_left hL0]
        refine le_trans ?_ hL_le
        -- b^L ≤ 2^L for L ≤ 0
        obtain ⟨m, hm⟩ : ∃ m : ℕ, L = -(m : ℤ) := ⟨(-L).toNat, by omega⟩
        rw [hm, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hbR m)
      · rw [min_eq_right hL0.le, zpow_zero]
        exact le_trans (one_le_zpow₀ h2.le hL0.le) hL_le
    · -- upper bound
      have hL_lt : |(toRat q : ℝ)| < (2 : ℝ) ^ (L + 1) := by
        have h := Int.lt_zpow_succ_log_self (R := ℝ) (by norm_num : (1 : ℕ) < 2) |(toRat q : ℝ)|
        rw [Nat.cast_ofNat] at h
        exact h
      rcases le_or_gt 0 (L + 1) with hL1 | hL1
      · rw [max_eq_left hL1]
        obtain ⟨m, hm⟩ : ∃ m : ℕ, L + 1 = (m : ℤ) := ⟨(L + 1).toNat, by omega⟩
        rw [hm] at hL_lt ⊢
        rw [zpow_natCast] at hL_lt ⊢
        exact lt_of_lt_of_le hL_lt (pow_le_pow_left₀ (by norm_num) hbR m)
      · rw [max_eq_right hL1.le, zpow_zero]
        obtain ⟨m, hm⟩ : ∃ m : ℕ, L + 1 = -(m : ℤ) ∧ 0 < m :=
          ⟨(-(L + 1)).toNat, by omega, by omega⟩
        rw [hm.1, zpow_neg, zpow_natCast] at hL_lt
        exact lt_trans hL_lt (inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) hm.2.ne'))

/-- `floorLogBaseAbs` in the `⌊logb⌋` form. -/
theorem floorLogBaseAbs_eq_floor_logb (b : UInt64) (hb : 2 ≤ b.toNat) (q : AzRat)
    (hq : q.num ≠ 0) :
    floorLogBaseAbs b q = ⌊logb (b.toNat : ℝ) |(toRat q : ℝ)|⌋ := by
  rw [floorLogBaseAbs_eq b hb q hq, Real.floor_logb_natCast (abs_toRat_pos q hq).le]

end Azurite.AzRat
