/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.LogBase
import Azurite.AzRat.Equiv.LogBase2
import Azurite.AzRat.Equiv.Unary
import Azurite.AzNat.Equiv.Size
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


/-! ### Ceiling and checked logarithms -/

theorem ceilingLogBaseAbs_eq (b : UInt64) (hb : 2 ≤ b.toNat) (q : AzRat) (hq : q.num ≠ 0) :
    ceilingLogBaseAbs b q = Int.clog b.toNat |(toRat q : ℝ)| := by
  unfold ceilingLogBaseAbs
  rw [ite_eq_right hq]
  simp only []
  have hpos := abs_toRat_pos q hq
  have hb1 : 1 < b.toNat := hb
  rw [floorLogBaseAbs_eq b hb q hq, cmpPowAbs_eq b (by omega)]
  set e := Int.log b.toNat |(toRat q : ℝ)| with he
  have hlo : (b.toNat : ℝ) ^ e ≤ |(toRat q : ℝ)| := Int.zpow_log_le_self hb1 hpos
  have hhi : |(toRat q : ℝ)| < (b.toNat : ℝ) ^ (e + 1) := Int.lt_zpow_succ_log_self hb1 _
  rcases hc : compare ((b.toNat : ℝ) ^ e) |(toRat q : ℝ)| with _ | _ | _
  · rw [compare_lt_iff_lt] at hc
    simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte]
    symm
    apply le_antisymm
    · exact (Int.le_zpow_iff_clog_le hb1 hpos).mp hhi.le
    · exact (Int.zpow_lt_iff_lt_clog hb1 hpos).mp hc
  · rw [compare_eq_iff_eq] at hc
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [← hc, Int.clog_zpow hb1]
  · rw [compare_gt_iff_gt] at hc
    exact absurd hlo (not_le.mpr hc)

theorem checkedLogBaseAbs_eq_some_iff (b : UInt64) (hb : 2 ≤ b.toNat) (q : AzRat) (e : ℤ) :
    checkedLogBaseAbs b q = some e ↔ |(toRat q : ℝ)| = (b.toNat : ℝ) ^ e := by
  unfold checkedLogBaseAbs
  have hb1 : 1 < b.toNat := hb
  by_cases hq : q.num = 0
  · rw [ite_eq_left hq, abs_toRat_eq,
      show (q.num.toNat : ℝ) = 0 by rw [hq, AzNat.toNat_zero, Nat.cast_zero], zero_div]
    constructor
    · intro h; cases h
    · intro h; exact absurd h.symm (zpow_pos (by exact_mod_cast (by omega : 0 < b.toNat)) _).ne'
  · rw [ite_eq_right hq]
    simp only []
    have hpos := abs_toRat_pos q hq
    rw [floorLogBaseAbs_eq b hb q hq, cmpPowAbs_eq b (by omega)]
    constructor
    · intro h
      split_ifs at h with hc
      · simp only [Option.some.injEq] at h
        rw [beq_iff_eq, compare_eq_iff_eq] at hc
        rw [← h, hc]
    · intro h
      have hlog : Int.log b.toNat |(toRat q : ℝ)| = e := by rw [h, Int.log_zpow hb1]
      rw [hlog, ite_eq_left (by rw [beq_iff_eq, compare_eq_iff_eq, h])]

theorem checkedLogBaseAbs_eq_none_iff (b : UInt64) (hb : 2 ≤ b.toNat) (q : AzRat) :
    checkedLogBaseAbs b q = none ↔ ∀ e : ℤ, |(toRat q : ℝ)| ≠ (b.toNat : ℝ) ^ e := by
  constructor
  · intro h e he
    have := (checkedLogBaseAbs_eq_some_iff b hb q e).mpr he
    rw [h] at this
    cases this
  · intro h
    rcases hc : checkedLogBaseAbs b q with _ | e
    · rfl
    · exact absurd ((checkedLogBaseAbs_eq_some_iff b hb q e).mp hc) (h e)


/-! ### Rational bases -/

/-- A positive rational is `num / den` with a positive numerator. -/
theorem toRat_eq_div_of_pos (b : AzRat) (hb : 0 < (toRat b : ℝ)) :
    (toRat b : ℝ) = (b.num.toNat : ℝ) / b.den.toNat ∧ b.sign = true ∧ 0 < b.num.toNat := by
  have hD : (0 : ℝ) < b.den.toNat := by exact_mod_cast den_toNat_pos b
  have hcast := toRat_cast_eq b
  have hs : b.sign = true := by
    by_contra hs
    rw [Bool.not_eq_true] at hs
    rw [hcast, hs] at hb
    simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast] at hb
    have : -(b.num.toNat : ℝ) / b.den.toNat ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hD.le
    linarith
  rw [hcast, hs] at hb ⊢
  simp only [↓reduceIte, Int.cast_natCast] at hb ⊢
  refine ⟨by simp, by simp, ?_⟩
  have : (0 : ℝ) < b.num.toNat := by
    by_contra h
    push Not at h
    have := div_nonpos_of_nonpos_of_nonneg h hD.le
    linarith
  exact_mod_cast this

/-- `cmpPowRatAbs b e q` compares `b^e` with `|toRat q|` for a positive rational base. -/
lemma cmpPowRatAbs_eq (b q : AzRat) (hb : 0 < (toRat b : ℝ)) (e : ℤ) :
    cmpPowRatAbs b e q = compare ((toRat b : ℝ) ^ e) |(toRat q : ℝ)| := by
  obtain ⟨hbv, -, hN⟩ := toRat_eq_div_of_pos b hb
  have hD : (0 : ℝ) < q.den.toNat := by exact_mod_cast den_toNat_pos q
  have hDb : (0 : ℝ) < b.den.toNat := by exact_mod_cast den_toNat_pos b
  have hNb : (0 : ℝ) < b.num.toNat := by exact_mod_cast hN
  rw [abs_toRat_eq, hbv]
  cases e with
  | ofNat n =>
    simp only [cmpPowRatAbs]
    rw [AzNat.compare_eq_compare_toNat, AzNat.toNat_mul, AzNat.toNat_mul, AzNat.toNat_pow,
      AzNat.toNat_pow, Int.ofNat_eq_natCast, zpow_natCast, div_pow,
      compare_div_div _ _ _ _ (pow_pos hDb n) hD, ← Nat.cast_pow, ← Nat.cast_pow,
      ← Nat.cast_mul, ← Nat.cast_mul, compare_natCast, Nat.mul_comm q.num.toNat]
  | negSucc n =>
    simp only [cmpPowRatAbs]
    rw [AzNat.compare_eq_compare_toNat, AzNat.toNat_mul, AzNat.toNat_mul, AzNat.toNat_pow,
      AzNat.toNat_pow, zpow_negSucc, div_pow, inv_div,
      compare_div_div _ _ _ _ (pow_pos hNb _) hD, ← Nat.cast_pow, ← Nat.cast_pow,
      ← Nat.cast_mul, ← Nat.cast_mul, compare_natCast, Nat.mul_comm q.num.toNat]

theorem logb_zpow' {b : ℝ} (hb0 : 0 < b) (hb1 : b ≠ 1) (z : ℤ) : Real.logb b (b ^ z) = z := by
  rw [← Real.rpow_intCast, Real.logb_rpow hb0 hb1]

/-- `⌊logb b x⌋ = z` from `b^z ≤ x < b^(z+1)`. -/
theorem floor_logb_eq {b x : ℝ} (hb : 1 < b) (hx : 0 < x) (z : ℤ)
    (hlo : b ^ z ≤ x) (hhi : x < b ^ (z + 1)) : ⌊Real.logb b x⌋ = z := by
  have hb0 : 0 < b := by linarith
  rw [Int.floor_eq_iff]
  constructor
  · rw [← logb_zpow' hb0 hb.ne' z]
    exact (Real.logb_le_logb hb (zpow_pos hb0 _) hx).mpr hlo
  · rw [show ((z : ℝ) + 1) = ((z + 1 : ℤ) : ℝ) by push_cast; ring, ← logb_zpow' hb0 hb.ne' (z + 1)]
    exact (Real.logb_lt_logb_iff hb hx (zpow_pos hb0 _)).mpr hhi

/-- `⌈logb b x⌉ = z` from `b^(z−1) < x ≤ b^z`. -/
theorem ceil_logb_eq {b x : ℝ} (hb : 1 < b) (hx : 0 < x) (z : ℤ)
    (hlo : b ^ (z - 1) < x) (hhi : x ≤ b ^ z) : ⌈Real.logb b x⌉ = z := by
  have hb0 : 0 < b := by linarith
  rw [Int.ceil_eq_iff]
  constructor
  · rw [show ((z : ℝ) - 1) = ((z - 1 : ℤ) : ℝ) by push_cast; ring, ← logb_zpow' hb0 hb.ne' (z - 1)]
    exact (Real.logb_lt_logb_iff hb (zpow_pos hb0 _) hx).mpr hlo
  · rw [← logb_zpow' hb0 hb.ne' z]
    exact (Real.logb_le_logb hb hx (zpow_pos hb0 _)).mpr hhi

/-- The search returns `⌊log_b |q|⌋` from any valid bracket. -/
lemma floorLogSearchRat_eq (b q : AzRat) (hb : 1 < (toRat b : ℝ)) (hq : q.num ≠ 0)
    (lo hi : ℤ) (hlo : (toRat b : ℝ) ^ lo ≤ |(toRat q : ℝ)|)
    (hhi : |(toRat q : ℝ)| < (toRat b : ℝ) ^ hi) :
    floorLogSearchRat b q lo hi = ⌊Real.logb (toRat b) |(toRat q : ℝ)|⌋ := by
  have hpos := abs_toRat_pos q hq
  have hb0 : (0 : ℝ) < toRat b := by linarith
  induction h_sub : (hi - lo).toNat using Nat.strong_induction_on generalizing lo hi with
  | _ n ih =>
  rw [floorLogSearchRat]
  split_ifs with h
  · dsimp only
    set mid := (lo + hi) / 2 with hmid_def
    have hmid1 : lo < mid := by omega
    have hmid2 : mid < hi := by omega
    rw [cmpPowRatAbs_eq b q hb0 mid]
    rcases lt_trichotomy ((toRat b : ℝ) ^ mid) |(toRat q : ℝ)| with hlt | heq | hgt
    · rw [compare_lt_iff_lt.mpr hlt]
      exact ih _ (by omega) mid hi hlt.le hhi rfl
    · rw [compare_eq_iff_eq.mpr heq]
      exact ih _ (by omega) mid hi heq.le hhi rfl
    · rw [compare_gt_iff_gt.mpr hgt]
      exact ih _ (by omega) lo mid hlo hgt rfl
  · have hlohi : lo < hi := by
      by_contra hcon
      push Not at hcon
      have : (toRat b : ℝ) ^ hi ≤ (toRat b : ℝ) ^ lo := zpow_le_zpow_right₀ hb.le hcon
      linarith
    have hhi' : hi = lo + 1 := by omega
    rw [hhi'] at hhi
    exact (floor_logb_eq hb hpos lo hlo hhi).symm

theorem bracketHi_spec (b q : AzRat) :
    ∀ (fuel hi : ℕ), cmpPowRatAbs b (bracketHi b q hi fuel) q = .gt ∨
      bracketHi b q hi fuel = hi * 2 ^ fuel := by
  intro fuel
  induction fuel with
  | zero => intro hi; right; simp [bracketHi]
  | succ fuel ih =>
    intro hi
    simp only [bracketHi]
    split_ifs with h
    · exact Or.inl (beq_iff_eq.mp h)
    · rcases ih (2 * hi) with h1 | h1
      · exact Or.inl h1
      · right; rw [h1]; ring

theorem bracketLo_spec (b q : AzRat) :
    ∀ (fuel lo : ℕ), cmpPowRatAbs b (-(bracketLo b q lo fuel : ℤ)) q ≠ .gt ∨
      bracketLo b q lo fuel = lo * 2 ^ fuel := by
  intro fuel
  induction fuel with
  | zero => intro lo; right; simp [bracketLo]
  | succ fuel ih =>
    intro lo
    simp only [bracketLo]
    split_ifs with h
    · rcases ih (2 * lo) with h1 | h1
      · exact Or.inl h1
      · right; rw [h1]; ring
    · exact Or.inl (fun h' => h (beq_iff_eq.mpr h'))

/-- Bernoulli: for a rational base `b > 1`, `b^(2^F) > m` once `F ≥ size (den b) + size m`. -/
theorem lt_pow_two_pow (b : AzRat) (hb : 1 < (toRat b : ℝ)) (m F : ℕ)
    (hF : b.den.size + m.size ≤ F) : (m : ℝ) < (toRat b : ℝ) ^ (2 ^ F : ℕ) := by
  obtain ⟨hbv, -, hN⟩ := toRat_eq_div_of_pos b (by linarith)
  have hDpos : 0 < b.den.toNat := den_toNat_pos b
  have hD : (0 : ℝ) < b.den.toNat := by exact_mod_cast hDpos
  have hND : b.den.toNat < b.num.toNat := by
    rw [hbv, one_lt_div hD] at hb
    exact_mod_cast hb
  -- `b − 1 ≥ 1 / den`
  have hb1 : (1 : ℝ) / b.den.toNat ≤ (toRat b : ℝ) - 1 := by
    rw [hbv, div_sub_one hD.ne', div_le_div_iff_of_pos_right hD]
    have : (b.den.toNat : ℝ) + 1 ≤ b.num.toNat := by exact_mod_cast hND
    linarith
  -- `den · m < 2^F`
  have hDm : b.den.toNat * m < 2 ^ F := by
    have h1 : b.den.toNat < 2 ^ b.den.size := by rw [← AzNat.size_toNat]; exact Nat.lt_size_self _
    have h2 : m < 2 ^ m.size := Nat.lt_size_self _
    calc b.den.toNat * m < (b.den.toNat + 1) * (m + 1) := by nlinarith
      _ ≤ 2 ^ b.den.size * 2 ^ m.size := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 ^ (b.den.size + m.size) := by rw [pow_add]
      _ ≤ 2 ^ F := Nat.pow_le_pow_right (by norm_num) hF
  have hDmR : (m : ℝ) ≤ (2 ^ F : ℕ) / b.den.toNat := by
    rw [le_div_iff₀ hD]
    have : ((b.den.toNat * m : ℕ) : ℝ) ≤ ((2 ^ F : ℕ) : ℝ) := by exact_mod_cast hDm.le
    push_cast at this ⊢
    linarith
  have hbern := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ toRat b by linarith) (2 ^ F)
  have h2F : (0 : ℝ) < (2 ^ F : ℕ) := by positivity
  calc (m : ℝ) ≤ (2 ^ F : ℕ) / b.den.toNat := hDmR
    _ = (2 ^ F : ℕ) * (1 / b.den.toNat) := by ring
    _ ≤ (2 ^ F : ℕ) * ((toRat b : ℝ) - 1) := by gcongr
    _ < 1 + (2 ^ F : ℕ) * ((toRat b : ℝ) - 1) := by linarith
    _ ≤ (toRat b : ℝ) ^ (2 ^ F : ℕ) := hbern

theorem one_lt_toRat_iff (b : AzRat) (hb : 0 < (toRat b : ℝ)) :
    1 < (toRat b : ℝ) ↔ b.den < b.num := by
  obtain ⟨hbv, -, -⟩ := toRat_eq_div_of_pos b hb
  have hD : (0 : ℝ) < b.den.toNat := by exact_mod_cast den_toNat_pos b
  rw [hbv, one_lt_div hD, AzNat.lt_iff_toNat_lt]
  exact Nat.cast_lt

theorem abs_toRat_le_num (q : AzRat) : |(toRat q : ℝ)| ≤ q.num.toNat := by
  rw [abs_toRat_eq]
  exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast den_toNat_pos q)

theorem inv_abs_toRat_le_den (q : AzRat) (hq : q.num ≠ 0) :
    |(toRat q : ℝ)|⁻¹ ≤ q.den.toNat := by
  rw [abs_toRat_eq, inv_div]
  exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast num_toNat_pos q hq)

theorem floorLogBaseRatAbsCore_eq (b q : AzRat) (hb : 1 < (toRat b : ℝ)) (hq : q.num ≠ 0) :
    floorLogBaseRatAbsCore b q = ⌊Real.logb (toRat b) |(toRat q : ℝ)|⌋ := by
  unfold floorLogBaseRatAbsCore
  simp only []
  have hb0 : (0 : ℝ) < toRat b := by linarith
  have hpos := abs_toRat_pos q hq
  have hD : (0 : ℝ) < q.den.toNat := by exact_mod_cast den_toNat_pos q
  split_ifs with hbr hge
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hbr
    obtain ⟨h1, h2⟩ := hbr
    rw [cmpPowRatAbs_eq b q hb0] at h1 h2
    apply floorLogSearchRat_eq b q hb hq
    · exact le_of_not_gt (fun h => h1 (compare_gt_iff_gt.mpr h))
    · exact compare_gt_iff_gt.mp h2
  · -- `|q| ≥ 1`: bracket `[0, bracketHi)`
    apply floorLogSearchRat_eq b q hb hq
    · rw [zpow_zero, abs_toRat_eq, le_div_iff₀ hD, one_mul]
      rw [AzNat.le_iff_toNat_le] at hge
      exact_mod_cast hge
    · rcases bracketHi_spec b q (bracketFuel b q) 1 with h | h
      · rw [cmpPowRatAbs_eq b q hb0] at h
        exact compare_gt_iff_gt.mp h
      · rw [h, one_mul, zpow_natCast]
        calc |(toRat q : ℝ)| ≤ q.num.toNat := abs_toRat_le_num q
          _ < (toRat b : ℝ) ^ (2 ^ bracketFuel b q : ℕ) :=
            lt_pow_two_pow b hb _ _ (by unfold bracketFuel; rw [AzNat.size_toNat]; omega)
  · -- `|q| < 1`: bracket `[−bracketLo, 0)`
    apply floorLogSearchRat_eq b q hb hq
    · rcases bracketLo_spec b q (bracketFuel b q) 1 with h | h
      · rw [cmpPowRatAbs_eq b q hb0] at h
        exact le_of_not_gt (fun hh => h (compare_gt_iff_gt.mpr hh))
      · rw [h, one_mul, zpow_neg, zpow_natCast, inv_le_comm₀ (pow_pos hb0 _) hpos]
        exact (calc |(toRat q : ℝ)|⁻¹ ≤ q.den.toNat := inv_abs_toRat_le_den q hq
          _ < (toRat b : ℝ) ^ (2 ^ bracketFuel b q : ℕ) :=
            lt_pow_two_pow b hb _ _ (by unfold bracketFuel; rw [AzNat.size_toNat]; omega)).le
    · rw [zpow_zero, abs_toRat_eq, div_lt_one hD]
      rw [AzNat.le_iff_toNat_le] at hge
      push Not at hge
      exact_mod_cast hge

/-- The floor brackets `|q|`: `b^e ≤ |q| < b^(e+1)`. -/
theorem zpow_floor_logb_bounds {b x : ℝ} (hb : 1 < b) (hx : 0 < x) :
    b ^ ⌊Real.logb b x⌋ ≤ x ∧ x < b ^ (⌊Real.logb b x⌋ + 1) := by
  have hb0 : 0 < b := by linarith
  constructor
  · rw [← Real.logb_le_logb hb (zpow_pos hb0 _) hx, logb_zpow' hb0 hb.ne']
    exact Int.floor_le _
  · rw [← Real.logb_lt_logb_iff hb hx (zpow_pos hb0 _), logb_zpow' hb0 hb.ne']
    push_cast
    exact Int.lt_floor_add_one _

theorem ceilingLogBaseRatAbsCore_eq (b q : AzRat) (hb : 1 < (toRat b : ℝ)) (hq : q.num ≠ 0) :
    ceilingLogBaseRatAbsCore b q = ⌈Real.logb (toRat b) |(toRat q : ℝ)|⌉ := by
  unfold ceilingLogBaseRatAbsCore
  simp only []
  have hb0 : (0 : ℝ) < toRat b := by linarith
  have hpos := abs_toRat_pos q hq
  rw [floorLogBaseRatAbsCore_eq b q hb hq, cmpPowRatAbs_eq b q hb0]
  obtain ⟨hlo, hhi⟩ := zpow_floor_logb_bounds hb hpos
  set e := ⌊Real.logb (toRat b) |(toRat q : ℝ)|⌋ with he
  rcases hc : compare ((toRat b : ℝ) ^ e) |(toRat q : ℝ)| with _ | _ | _
  · rw [compare_lt_iff_lt] at hc
    simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte]
    symm
    apply ceil_logb_eq hb hpos
    · rw [add_sub_cancel_right]; exact hc
    · exact hhi.le
  · rw [compare_eq_iff_eq] at hc
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [← hc, logb_zpow' hb0 hb.ne', Int.ceil_intCast]
  · rw [compare_gt_iff_gt] at hc
    exact absurd hlo (not_le.mpr hc)

/-- The exactness test at the floor decides whether `|q|` is a power of `b`. -/
theorem cmpPowRatAbs_floor_eq_iff (b q : AzRat) (hb : 1 < (toRat b : ℝ)) (hq : q.num ≠ 0)
    (e : ℤ) :
    (cmpPowRatAbs b (floorLogBaseRatAbsCore b q) q = .eq ∧ floorLogBaseRatAbsCore b q = e) ↔
      |(toRat q : ℝ)| = (toRat b : ℝ) ^ e := by
  have hb0 : (0 : ℝ) < toRat b := by linarith
  rw [floorLogBaseRatAbsCore_eq b q hb hq, cmpPowRatAbs_eq b q hb0, compare_eq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [← h2, h1]
  · intro h
    have : ⌊Real.logb (toRat b) |(toRat q : ℝ)|⌋ = e := by
      rw [h, logb_zpow' hb0 hb.ne', Int.floor_intCast]
    exact ⟨by rw [this, h], this⟩

theorem isLogBase_eq_true (b : AzRat) (hb0 : 0 < (toRat b : ℝ)) (hb1 : (toRat b : ℝ) ≠ 1) :
    isLogBase b = true := by
  obtain ⟨hbv, hs, hN⟩ := toRat_eq_div_of_pos b hb0
  have hD : (0 : ℝ) < b.den.toNat := by exact_mod_cast den_toNat_pos b
  unfold isLogBase
  rw [hs, Bool.true_and, Bool.and_eq_true, bne_iff_ne, bne_iff_ne]
  refine ⟨fun h => by rw [h, AzNat.toNat_zero] at hN; omega, fun h => hb1 ?_⟩
  rw [hbv, h, div_self hD.ne']

theorem lt_one_toRat_inv (b : AzRat) (hb0 : 0 < (toRat b : ℝ)) (hb1 : (toRat b : ℝ) ≠ 1)
    (hlt : ¬ b.den < b.num) : 1 < (toRat b⁻¹ : ℝ) := by
  rw [toRat_inv, Rat.cast_inv, one_lt_inv₀ hb0]
  exact lt_of_le_of_ne (not_lt.mp (fun h => hlt ((one_lt_toRat_iff b hb0).mp h))) hb1

theorem floorLogBaseRatAbs_eq (b q : AzRat) (hb0 : 0 < (toRat b : ℝ))
    (hb1 : (toRat b : ℝ) ≠ 1) (hq : q.num ≠ 0) :
    floorLogBaseRatAbs b q = some ⌊Real.logb (toRat b) |(toRat q : ℝ)|⌋ := by
  unfold floorLogBaseRatAbs
  rw [ite_eq_right (not_or.mpr ⟨hq, not_not.mpr (isLogBase_eq_true b hb0 hb1)⟩)]
  split_ifs with hlt
  · rw [floorLogBaseRatAbsCore_eq b q ((one_lt_toRat_iff b hb0).mpr hlt) hq]
  · rw [ceilingLogBaseRatAbsCore_eq b⁻¹ q (lt_one_toRat_inv b hb0 hb1 hlt) hq, toRat_inv,
      Rat.cast_inv, Real.logb_inv_base, Int.ceil_neg, neg_neg]

theorem ceilingLogBaseRatAbs_eq (b q : AzRat) (hb0 : 0 < (toRat b : ℝ))
    (hb1 : (toRat b : ℝ) ≠ 1) (hq : q.num ≠ 0) :
    ceilingLogBaseRatAbs b q = some ⌈Real.logb (toRat b) |(toRat q : ℝ)|⌉ := by
  unfold ceilingLogBaseRatAbs
  rw [ite_eq_right (not_or.mpr ⟨hq, not_not.mpr (isLogBase_eq_true b hb0 hb1)⟩)]
  split_ifs with hlt
  · rw [ceilingLogBaseRatAbsCore_eq b q ((one_lt_toRat_iff b hb0).mpr hlt) hq]
  · rw [floorLogBaseRatAbsCore_eq b⁻¹ q (lt_one_toRat_inv b hb0 hb1 hlt) hq, toRat_inv,
      Rat.cast_inv, Real.logb_inv_base, Int.floor_neg, neg_neg]

theorem checkedLogBaseRatAbs_eq_some_iff (b q : AzRat) (hb0 : 0 < (toRat b : ℝ))
    (hb1 : (toRat b : ℝ) ≠ 1) (e : ℤ) :
    checkedLogBaseRatAbs b q = some e ↔ |(toRat q : ℝ)| = (toRat b : ℝ) ^ e := by
  unfold checkedLogBaseRatAbs
  by_cases hq : q.num = 0
  · rw [ite_eq_left (Or.inl hq), abs_toRat_eq,
      show (q.num.toNat : ℝ) = 0 by rw [hq, AzNat.toNat_zero, Nat.cast_zero], zero_div]
    constructor
    · intro h; cases h
    · intro h; exact absurd h.symm (zpow_pos hb0 _).ne'
  · rw [ite_eq_right (not_or.mpr ⟨hq, not_not.mpr (isLogBase_eq_true b hb0 hb1)⟩)]
    simp only []
    split_ifs with hlt hc hc
    · rw [Option.some.injEq,
        ← cmpPowRatAbs_floor_eq_iff b q ((one_lt_toRat_iff b hb0).mpr hlt) hq e]
      exact ⟨fun h => ⟨beq_iff_eq.mp hc, h⟩, fun h => h.2⟩
    · rw [← cmpPowRatAbs_floor_eq_iff b q ((one_lt_toRat_iff b hb0).mpr hlt) hq e]
      exact ⟨fun h => h.elim, fun h => absurd (beq_iff_eq.mpr h.1) hc⟩
    · have key := cmpPowRatAbs_floor_eq_iff b⁻¹ q (lt_one_toRat_inv b hb0 hb1 hlt) hq (-e)
      rw [toRat_inv, Rat.cast_inv, inv_zpow, zpow_neg, inv_inv] at key
      rw [Option.some.injEq, ← key]
      exact ⟨fun h => ⟨beq_iff_eq.mp hc, by omega⟩, fun h => by omega⟩
    · have key := cmpPowRatAbs_floor_eq_iff b⁻¹ q (lt_one_toRat_inv b hb0 hb1 hlt) hq (-e)
      rw [toRat_inv, Rat.cast_inv, inv_zpow, zpow_neg, inv_inv] at key
      rw [← key]
      exact ⟨fun h => h.elim, fun h => absurd (beq_iff_eq.mpr h.1) hc⟩

theorem checkedLogBaseRatAbs_eq_none_iff (b q : AzRat) (hb0 : 0 < (toRat b : ℝ))
    (hb1 : (toRat b : ℝ) ≠ 1) :
    checkedLogBaseRatAbs b q = none ↔ ∀ e : ℤ, |(toRat q : ℝ)| ≠ (toRat b : ℝ) ^ e := by
  constructor
  · intro h e he
    have := (checkedLogBaseRatAbs_eq_some_iff b q hb0 hb1 e).mpr he
    rw [h] at this
    cases this
  · intro h
    rcases hc : checkedLogBaseRatAbs b q with _ | e
    · rfl
    · exact absurd ((checkedLogBaseRatAbs_eq_some_iff b q hb0 hb1 e).mp hc) (h e)


/-! ### Power-of-two bases -/

theorem two_pow_zpow (k : ℕ) (x : ℤ) : ((2 ^ k : ℕ) : ℝ) ^ x = (2 : ℝ) ^ ((k : ℤ) * x) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_mul]

/-- `Int.log` in base `2^k` is the base-2 logarithm floor-divided by `k`. -/
theorem int_log_two_pow (k : ℕ) (hk : 0 < k) (r : ℝ) (hr : 0 < r) :
    Int.log (2 ^ k) r = Int.log 2 r / k := by
  have hb : 1 < 2 ^ k := Nat.one_lt_two_pow hk.ne'
  set e := Int.log 2 r with he
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hdiv : (k : ℤ) * (e / k) + e % k = e := by
    rw [mul_comm]; exact (add_comm _ _).trans (Int.emod_add_ediv_mul e k)
  have hr0 := Int.emod_nonneg e hkZ.ne'
  have hr1 := Int.emod_lt_of_pos e hkZ
  apply le_antisymm
  · have : r < ((2 ^ k : ℕ) : ℝ) ^ (e / k + 1) := by
      rw [two_pow_zpow]
      calc r < (2 : ℝ) ^ (e + 1) := by
            simpa using Int.lt_zpow_succ_log_self (b := 2) (by norm_num) r
        _ ≤ (2 : ℝ) ^ ((k : ℤ) * (e / k + 1)) :=
            zpow_le_zpow_right₀ (by norm_num) (by rw [mul_add, mul_one]; linarith)
    have := (Int.lt_zpow_iff_log_lt hb hr).mp this
    omega
  · apply (Int.zpow_le_iff_le_log hb hr).mp
    rw [two_pow_zpow]
    calc (2 : ℝ) ^ ((k : ℤ) * (e / k)) ≤ (2 : ℝ) ^ e :=
          zpow_le_zpow_right₀ (by norm_num) (by linarith)
      _ ≤ r := by simpa using Int.zpow_log_le_self (b := 2) (by norm_num) hr

/-- `Int.clog` in base `2^k` is the base-2 logarithm ceiling-divided by `k`. -/
theorem int_clog_two_pow (k : ℕ) (hk : 0 < k) (r : ℝ) (hr : 0 < r) :
    Int.clog (2 ^ k) r = -((-Int.clog 2 r) / k) := by
  have hb : 1 < 2 ^ k := Nat.one_lt_two_pow hk.ne'
  set c := Int.clog 2 r with hc
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hdiv : (k : ℤ) * (-c / k) + -c % k = -c := by
    rw [mul_comm]; exact (add_comm _ _).trans (Int.emod_add_ediv_mul (-c) k)
  have hr0 := Int.emod_nonneg (-c) hkZ.ne'
  have hr1 := Int.emod_lt_of_pos (-c) hkZ
  apply le_antisymm
  · apply (Int.le_zpow_iff_clog_le hb hr).mp
    rw [two_pow_zpow]
    calc r ≤ (2 : ℝ) ^ c := by simpa using Int.self_le_zpow_clog (b := 2) (by norm_num) r
      _ ≤ (2 : ℝ) ^ ((k : ℤ) * -(-c / k)) :=
          zpow_le_zpow_right₀ (by norm_num) (by rw [mul_neg]; linarith)
  · have : ((2 ^ k : ℕ) : ℝ) ^ (-(-c / k) - 1) < r := by
      rw [two_pow_zpow]
      calc (2 : ℝ) ^ ((k : ℤ) * (-(-c / k) - 1)) ≤ (2 : ℝ) ^ (c - 1) :=
            zpow_le_zpow_right₀ (by norm_num) (by rw [mul_sub, mul_neg, mul_one]; linarith)
        _ < r := by simpa using Int.zpow_pred_clog_lt_self (b := 2) (by norm_num) hr
    have := (Int.zpow_lt_iff_lt_clog hb hr).mp this
    omega

theorem floorLogBasePowerOf2Abs_eq (q : AzRat) (k : ℕ) (hq : q.num ≠ 0) (hk : 0 < k) :
    floorLogBasePowerOf2Abs q k = some (Int.log (2 ^ k) |(toRat q : ℝ)|) := by
  unfold floorLogBasePowerOf2Abs
  rw [ite_eq_right (not_or.mpr ⟨hq, hk.ne'⟩), floorLogBase2Abs_eq_log q hq,
    int_log_two_pow k hk _ (abs_toRat_pos q hq)]

theorem ceilingLogBase2Abs_eq_clog (q : AzRat) (hq : q.num ≠ 0) :
    ceilingLogBase2Abs q = Int.clog 2 |(toRat q : ℝ)| := by
  rw [ceilingLogBase2Abs_eq q hq, ← Real.ceil_logb_natCast (b := 2) (abs_toRat_pos q hq).le]
  norm_num

theorem ceilingLogBasePowerOf2Abs_eq (q : AzRat) (k : ℕ) (hq : q.num ≠ 0) (hk : 0 < k) :
    ceilingLogBasePowerOf2Abs q k = some (Int.clog (2 ^ k) |(toRat q : ℝ)|) := by
  unfold ceilingLogBasePowerOf2Abs
  rw [ite_eq_right (not_or.mpr ⟨hq, hk.ne'⟩), ceilingLogBase2Abs_eq_clog q hq,
    int_clog_two_pow k hk _ (abs_toRat_pos q hq)]

/-- `|q| = 2^j` exactly when numerator and denominator are powers of two with exponents
differing by `j`. -/
theorem abs_toRat_eq_zpow_iff (q : AzRat) (j : ℤ) :
    |(toRat q : ℝ)| = (2 : ℝ) ^ j ↔
      q.num.toNat.isPowerOfTwo ∧ q.den.toNat.isPowerOfTwo ∧
        (q.num.size : ℤ) - q.den.size = j := by
  have hD : (0 : ℝ) < q.den.toNat := by exact_mod_cast den_toNat_pos q
  have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
  rw [abs_toRat_eq]
  constructor
  · intro h
    rcases le_or_gt 0 j with hj | hj
    · have hnum : q.num.toNat = q.den.toNat * 2 ^ j.toNat := by
        have : (q.num.toNat : ℝ) = q.den.toNat * 2 ^ j.toNat := by
          rw [div_eq_iff hD.ne'] at h
          rw [h, ← zpow_natCast, Int.toNat_of_nonneg hj]
          ring
        exact_mod_cast this
      have hden1 : q.den.toNat = 1 := Nat.eq_one_of_dvd_coprimes hcop ⟨_, hnum⟩ (dvd_refl _)
      rw [hden1, one_mul] at hnum
      refine ⟨⟨j.toNat, hnum⟩, ⟨0, by rw [hden1, pow_zero]⟩, ?_⟩
      rw [← AzNat.size_toNat, ← AzNat.size_toNat, hnum, hden1, Nat.size_pow, Nat.size_one]
      omega
    · have hden' : q.den.toNat = q.num.toNat * 2 ^ (-j).toNat := by
        have : (q.den.toNat : ℝ) = q.num.toNat * 2 ^ (-j).toNat := by
          rw [div_eq_iff hD.ne'] at h
          rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), h, mul_comm ((2 : ℝ) ^ j),
            mul_assoc, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero,
            mul_one]
        exact_mod_cast this
      have hnum1 : q.num.toNat = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop.symm ⟨_, hden'⟩ (dvd_refl _)
      rw [hnum1, one_mul] at hden'
      refine ⟨⟨0, by rw [hnum1, pow_zero]⟩, ⟨(-j).toNat, hden'⟩, ?_⟩
      rw [← AzNat.size_toNat, ← AzNat.size_toNat, hnum1, hden', Nat.size_pow, Nat.size_one]
      omega
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hj⟩
    rw [← AzNat.size_toNat, ← AzNat.size_toNat, ha, hb, Nat.size_pow, Nat.size_pow] at hj
    rw [ha, hb, ← hj]
    push_cast
    rw [show ((a : ℤ) + 1 - ((b : ℤ) + 1)) = (a : ℤ) - b by ring, zpow_sub₀ (by norm_num),
      zpow_natCast, zpow_natCast]

theorem checkedLogBasePowerOf2Abs_eq_some_iff (q : AzRat) (k : ℕ) (hk : 0 < k) (e : ℤ) :
    checkedLogBasePowerOf2Abs q k = some e ↔ |(toRat q : ℝ)| = ((2 ^ k : ℕ) : ℝ) ^ e := by
  unfold checkedLogBasePowerOf2Abs
  rw [two_pow_zpow]
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  by_cases hq : q.num = 0
  · rw [ite_eq_left (Or.inl hq), abs_toRat_eq,
      show (q.num.toNat : ℝ) = 0 by rw [hq, AzNat.toNat_zero, Nat.cast_zero], zero_div]
    constructor
    · intro h; cases h
    · intro h; exact absurd h.symm (zpow_pos (by norm_num) _).ne'
  · rw [abs_toRat_eq_zpow_iff q]
    by_cases hp : (q.num.isPowerOfTwo && q.den.isPowerOfTwo) = true
    · rw [ite_eq_right (by push Not; exact ⟨hq, hk.ne', hp⟩)]
      simp only []
      rw [Bool.and_eq_true, AzNat.isPowerOfTwo_iff, AzNat.isPowerOfTwo_iff] at hp
      constructor
      · intro h
        split_ifs at h with hm
        · simp only [Option.some.injEq] at h
          refine ⟨hp.1, hp.2, ?_⟩
          rw [← h]
          have := Int.emod_add_ediv_mul ((q.num.size : ℤ) - q.den.size) k
          rw [hm, zero_add] at this
          rw [mul_comm]
          exact this.symm
      · rintro ⟨-, -, hj⟩
        rw [hj, Int.mul_emod_right, ite_eq_left rfl, Int.mul_ediv_cancel_left _ hkZ.ne']
    · rw [ite_eq_left (Or.inr (Or.inr hp))]
      rw [Bool.and_eq_true, AzNat.isPowerOfTwo_iff, AzNat.isPowerOfTwo_iff] at hp
      constructor
      · intro h; cases h
      · rintro ⟨h1, h2, -⟩; exact absurd ⟨h1, h2⟩ hp

theorem checkedLogBasePowerOf2Abs_eq_none_iff (q : AzRat) (k : ℕ) (hk : 0 < k) :
    checkedLogBasePowerOf2Abs q k = none ↔
      ∀ e : ℤ, |(toRat q : ℝ)| ≠ ((2 ^ k : ℕ) : ℝ) ^ e := by
  constructor
  · intro h e he
    have := (checkedLogBasePowerOf2Abs_eq_some_iff q k hk e).mpr he
    rw [h] at this
    cases this
  · intro h
    rcases hc : checkedLogBasePowerOf2Abs q k with _ | e
    · rfl
    · exact absurd ((checkedLogBasePowerOf2Abs_eq_some_iff q k hk e).mp hc) (h e)

end Azurite.AzRat
