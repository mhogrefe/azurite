/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.Equiv.ExpBracket
import Azurite.AzFloat.Equiv.AddSubRat
import Azurite.AzInt.Equiv.Sub
import Azurite.AzNat.Equiv.LogBase2

/-!
# Equivalence: the bracket of `exp x`

* `floorScaled_spec`, `truncToAzInt_spec`: the dyadic truncations.
* `expReduce_spec`: `r = x − k ln 2` is enclosed with width at most `2^(−w−10)`, `|r| < 3/4`.
* `expSmallBracket_spec`, `expSignedBracket_spec`: relative errors `40 (K + 1) 2^(−w)` on either
  side, `K = expK w ≤ w + 8`.
* `expApprox_spec`: the `Roundable` pair encloses `exp x` with width at most `expEps x w`, and
  `expApprox_isSome_exists` is the Ziv certificate (`exp x` is irrational for a finite `x ≠ 0`).
* `expRatApprox_spec`, `expRatApprox_isSome_exists`: the same for a rational argument, width
  `expRatEps q w = 2 expEps q w`.
* `expM1Approx_spec`, `expM1Approx_isSome_exists`: the same for `exp x − 1`, width
  `expM1Eps x c w` (`c = max(−e, 0)`).
* `expM1RatApprox_spec`, `expM1RatApprox_isSome_exists`: `exp q − 1` for a rational `q`, width
  `expM1RatEps q c w`.
* `expOfBracket_spec` (strict lower end) and `expOfBracket_spec_width` (width
  `expOfBracketEps v (hi − lo) w`): the exponential of a bracket of width `≤ 1`.
-/

namespace Azurite.AzFloat

/-! ### The dyadic truncations -/

/-- `floorScaled x N = ⌊|x| · 2^N⌋`. -/
theorem floorScaled_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (N : ℕ) :
    ((floorScaled x N).toNat : ℝ) ≤ |xv| * 2 ^ N ∧
      |xv| * 2 ^ N < (floorScaled x N).toNat + 1 := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero =>
    simp only [toVal_zero, Option.some.injEq] at hx
    have : xv = 0 := by exact_mod_cast hx.symm
    subst this
    simp [floorScaled]
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    subst hx
    have habs : |finiteVal s e m| = (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size) := by
      unfold finiteVal
      rw [abs_mul, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _), Nat.abs_cast]
      cases s <;> simp
    simp only [floorScaled]
    set sh : AzInt := e + (AzNat.ofNat N).toAzInt - (AzNat.ofNat m.size).toAzInt with hsh
    have hshv : sh.toInt = e.toInt + N - m.size := by
      rw [hsh, AzInt.toInt_sub, AzInt.toInt_add, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
        AzNat.toNat_ofNat]
    have hval : |finiteVal s e m| * 2 ^ N = (m.toNat : ℝ) * (2 : ℝ) ^ sh.toInt := by
      rw [habs, hshv, mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 2
      ring
    rw [hval]
    have hA := AzInt.abs_toNat_eq sh
    split_ifs with hs
    · have h0 : 0 ≤ sh.toInt := (AzInt.sign_eq_true_iff sh).mp hs
      rw [abs_of_nonneg h0] at hA
      rw [← hA, zpow_natCast, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]
      push_cast
      exact ⟨le_rfl, lt_add_one _⟩
    · have h0 : sh.toInt = -(sh.abs.toNat : ℤ) := by
        unfold AzInt.toInt
        rw [ite_eq_right hs]
      rw [h0, zpow_neg, zpow_natCast, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
      set a := sh.abs.toNat
      have hpos : (0 : ℝ) < 2 ^ a := by positivity
      have hdm := Nat.div_add_mod m.toNat (2 ^ a)
      have hmod := Nat.mod_lt m.toNat (by positivity : 0 < 2 ^ a)
      have hdm' : (m.toNat : ℝ) = 2 ^ a * (m.toNat / 2 ^ a : ℕ) + (m.toNat % 2 ^ a : ℕ) := by
        exact_mod_cast hdm.symm
      have hmod' : ((m.toNat % 2 ^ a : ℕ) : ℝ) < 2 ^ a := by exact_mod_cast hmod
      have hr0 : (0 : ℝ) ≤ ((m.toNat % 2 ^ a : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [← div_eq_mul_inv]
      constructor
      · rw [le_div_iff₀ hpos]; linarith
      · rw [div_lt_iff₀ hpos]; linarith

/-- `truncToAzInt x` is within `1` of `x` and no larger in absolute value. -/
theorem truncToAzInt_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    |((truncToAzInt x).toInt : ℝ) - xv| < 1 ∧ |((truncToAzInt x).toInt : ℝ)| ≤ |xv| := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero =>
    simp only [toVal_zero, Option.some.injEq] at hx
    have : xv = 0 := by exact_mod_cast hx.symm
    subst this
    simp [truncToAzInt, AzInt.toInt_zero]
  | finite s e q m hv =>
    obtain ⟨h1, h2⟩ := floorScaled_spec hx 0
    rw [pow_zero, mul_one] at h1 h2
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    subst hx
    have hpos := finiteVal_true_pos e hv
    have hM0 : (0 : ℝ) ≤ ((floorScaled (finite s e q m hv) 0).toNat : ℝ) := Nat.cast_nonneg _
    cases s with
    | true =>
      simp only [truncToAzInt, ↓reduceIte, toInt_toAzInt, Int.cast_natCast]
      rw [abs_of_pos hpos] at h1 h2 ⊢
      rw [abs_of_nonneg hM0]
      refine ⟨?_, h1⟩
      rw [abs_lt]
      constructor <;> linarith
    | false =>
      simp only [truncToAzInt, Bool.false_eq_true, ↓reduceIte, AzInt.toInt_neg, toInt_toAzInt,
        Int.cast_neg, Int.cast_natCast]
      rw [finiteVal_false, abs_neg, abs_of_pos hpos] at h1 h2
      rw [finiteVal_false]
      refine ⟨?_, ?_⟩
      · rw [abs_lt]
        constructor <;> linarith
      · simp only [abs_neg]
        rw [abs_of_pos hpos, abs_of_nonneg hM0]
        exact h1

/-- `2^(expK w) > w + 8` and `expK w ≤ w + 8`. -/
theorem expK_spec (w : ℕ) : w + 8 < 2 ^ expK w ∧ expK w ≤ w + 8 := by
  unfold expK
  have hne : AzNat.ofNat (w + 8) ≠ 0 := by
    intro h
    have := congrArg AzNat.toNat h
    rw [AzNat.toNat_ofNat, AzNat.toNat_zero] at this
    omega
  obtain ⟨h1, h2⟩ := AzNat.size_bounds _ hne
  rw [AzNat.toNat_ofNat] at h1 h2
  refine ⟨h2, ?_⟩
  have h3 : (AzNat.ofNat (w + 8)).size - 1 < 2 ^ ((AzNat.ofNat (w + 8)).size - 1) :=
    Nat.lt_two_pow_self
  omega

/-! ### Numeric helpers -/

/-- `2^(−w) ≤ 10^(−18)` from `w = 64` on. -/
theorem half_pow_small {w : ℕ} (hw : 64 ≤ w) : (1 / 2 : ℝ) ^ w ≤ 1 / 10 ^ 18 :=
  calc (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 64 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
    _ ≤ 1 / 10 ^ 18 := by norm_num

/-- `40 (w + 9) 2^(−w) ≤ 1` from `w = 64` on. -/
theorem forty_mul_half_pow_le {w : ℕ} (hw : 64 ≤ w) :
    40 * ((w : ℝ) + 9) * (1 / 2 : ℝ) ^ w ≤ 1 := by
  have hN : 40 * (w + 9) ≤ 2 ^ w := by
    have h1 : w - 6 < 2 ^ (w - 6) := Nat.lt_two_pow_self
    have h2 : 2 ^ w = 2 ^ 6 * 2 ^ (w - 6) := by rw [← pow_add]; congr 1; omega
    omega
  have hN' : (40 * ((w : ℝ) + 9)) ≤ 2 ^ w := by exact_mod_cast hN
  rw [one_div_pow, mul_one_div, div_le_one (by positivity)]
  exact hN'

/-- `(1 + 8u)^n ≤ 1 + 16 n u` for `8 n u ≤ 1`. -/
theorem one_add_eight_mul_pow_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) (hnu : 8 * n * u ≤ 1) :
    (1 + 8 * u) ^ n ≤ 1 + 16 * n * u := by
  have h1 : (1 + 8 * u) ^ n ≤ Real.exp (8 * u) ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (8 * u)]) n
  rw [← Real.exp_nat_mul] at h1
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := n * (8 * u))
    (by rw [abs_of_nonneg (by positivity)]; linarith)
  rw [abs_le] at h2
  have h3 : (n * (8 * u)) ^ 2 ≤ n * (8 * u) := by
    have : 0 ≤ n * (8 * u) := by positivity
    nlinarith
  nlinarith

/-- `exp x ≤ 1 + 2x` for `0 ≤ x ≤ 1`. -/
theorem exp_le_one_add_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_le] at h
  nlinarith

/-- `exp b (1 − (b − a)) ≤ exp a` for `a ≤ b`. -/
theorem exp_mul_one_sub_le_exp (a b : ℝ) : Real.exp b * (1 - (b - a)) ≤ Real.exp a := by
  have h := Real.add_one_le_exp (a - b)
  have hb := Real.exp_pos b
  calc Real.exp b * (1 - (b - a)) = Real.exp b * (a - b + 1) := by ring
    _ ≤ Real.exp b * Real.exp (a - b) := mul_le_mul_of_nonneg_left h hb.le
    _ = Real.exp a := by rw [← Real.exp_add]; congr 1; ring

/-- `exp b ≤ exp a (1 + 2 (b − a))` for `a ≤ b ≤ a + 1`. -/
theorem exp_le_exp_mul_one_add {a b : ℝ} (hab : a ≤ b) (h1 : b - a ≤ 1) :
    Real.exp b ≤ Real.exp a * (1 + 2 * (b - a)) := by
  have h := exp_le_one_add_two_mul (by linarith [hab]) h1
  have ha := Real.exp_pos a
  calc Real.exp b = Real.exp a * Real.exp (b - a) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp a * (1 + 2 * (b - a)) := mul_le_mul_of_nonneg_left h ha.le

/-- `A ≤ C (1 + t)` gives `(1/C)(1 − t) ≤ 1/A`. -/
theorem one_div_ge_of_le {A C t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hC : 0 < C) (hA : 0 < A)
    (h : A ≤ C * (1 + t)) : 1 / C * (1 - t) ≤ 1 / A := by
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hC hA]
  have h1 : (1 - t) * A ≤ (1 - t) * (C * (1 + t)) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h2 : 0 ≤ t * t * C := mul_nonneg (mul_nonneg ht ht) hC.le
  nlinarith

/-- `C (1 − t) ≤ A` with `t ≤ 1/2` gives `1/A ≤ (1/C)(1 + 2t)`. -/
theorem one_div_le_of_ge {A C t : ℝ} (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2) (hC : 0 < C) (hA : 0 < A)
    (h : C * (1 - t) ≤ A) : 1 / A ≤ 1 / C * (1 + 2 * t) := by
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hA hC]
  have h1 : (1 + 2 * t) * (C * (1 - t)) ≤ (1 + 2 * t) * A :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h2 : 0 ≤ t * (1 - 2 * t) * C := mul_nonneg (mul_nonneg ht (by linarith)) hC.le
  nlinarith

/-- A float that is not positive has a value `≤ 0`. -/
theorem toVal_sign_of_isPositive {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    (x.isPositive = true → 0 < xv) ∧ (x.isPositive = false → xv ≤ 0) := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero =>
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    simp only [toVal_zero, Option.some.injEq] at hx
    have : xv = 0 := by exact_mod_cast hx.symm
    rw [this]
  | finite s e q m h =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    subst hx
    have hpos : (finite s e q m h).isPositive = s := rfl
    rw [hpos]
    cases s with
    | true => exact ⟨fun _ => finiteVal_true_pos e h, fun h' => absurd h' (by decide)⟩
    | false =>
      refine ⟨fun h' => absurd h' (by decide), fun _ => ?_⟩
      rw [finiteVal_false]
      exact (neg_neg_of_pos (finiteVal_true_pos e h)).le

/-! ### The reduction -/

/-- The bounds on the remainder bracket from the bracket `[plo, phi]` of `P = x − r`. -/
theorem reduce_bounds {xv P plo phi rl rh δ r : ℝ} (hδ : 0 ≤ δ) (hδs : δ ≤ 1 / 10000)
    (hr : r = xv - P) (hP1 : plo ≤ P) (hP2 : P ≤ phi) (hwid : phi - plo ≤ 48 * δ)
    (hr71 : |r| ≤ 71 / 100)
    (hrl1 : rl ≤ xv - phi) (hrl2 : xv - phi ≤ rl + 2 * |xv - phi| * δ)
    (hrh1 : xv - plo ≤ rh) (hrh2 : rh ≤ xv - plo + 2 * |xv - plo| * δ) :
    rl ≤ r ∧ r ≤ rh ∧ rh - rl ≤ 52 * δ ∧ -3 / 4 ≤ rl ∧ rh ≤ 3 / 4 := by
  rw [abs_le] at hr71
  have h1 : |xv - phi| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |xv - plo| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have h3 : 2 * |xv - phi| * δ ≤ 2 * δ := by nlinarith [abs_nonneg (xv - phi)]
  have h4 : 2 * |xv - plo| * δ ≤ 2 * δ := by nlinarith [abs_nonneg (xv - plo)]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 1000000 in
/-- `expReduce` encloses `r = x − k ln 2` with width at most `2^(−w−10)`, inside `[−3/4, 3/4]`,
for a float `x` with `|x| < 2^e`. -/
theorem expReduce_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (e : AzInt)
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (w : ℕ) (hw : 64 ≤ w) :
    ∃ rl rh : ℝ, (expReduce x (expWork e w)).2.1.toVal = some (rl : EReal) ∧
      (expReduce x (expWork e w)).2.2.toVal = some (rh : EReal) ∧
      rl ≤ xv - (expReduce x (expWork e w)).1.toInt * Real.log 2 ∧
      xv - (expReduce x (expWork e w)).1.toInt * Real.log 2 ≤ rh ∧
      rh - rl ≤ (1 / 2 : ℝ) ^ (w + 10) ∧ -3 / 4 ≤ rl ∧ rh ≤ 3 / 4 := by
  -- the exponent scale
  obtain ⟨emax, hemax⟩ : ∃ n : ℕ, n = if e.sign then e.abs.toNat else 0 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = expWork e w := ⟨_, rfl⟩
  rw [← hW]
  have hWv : W = w + 16 + emax := by rw [hW, hemax]; rfl
  have hemaxZ : e.toInt ≤ (emax : ℤ) := by
    rw [hemax]
    split_ifs with hs
    · rw [AzInt.abs_toNat_eq e, abs_of_nonneg ((AzInt.sign_eq_true_iff e).mp hs)]
    · have := (AzInt.sign_eq_true_iff e).not.mp hs
      push Not at this
      push_cast
      exact this.le
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ emax := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact one_le_pow₀ (by norm_num)
  have hxE : |xv| < E := by
    calc |xv| < (2 : ℝ) ^ e.toInt := hxe
      _ ≤ (2 : ℝ) ^ (emax : ℤ) := zpow_le_zpow_right₀ (by norm_num) hemaxZ
      _ = E := by rw [hE, zpow_natCast]
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ (w + 16) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hus : u ≤ 1 / 10 ^ 18 := by
    calc u ≤ (1 / 2 : ℝ) ^ w := by
          rw [hu]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ 1 / 10 ^ 18 := half_pow_small hw
  have : NeZero W := ⟨by omega⟩
  have hδ : (1 / 2 : ℝ) ^ W = u * (1 / 2 : ℝ) ^ emax := by rw [hWv, pow_add, hu]
  have hEu : E * (1 / 2 : ℝ) ^ emax = 1 := by
    rw [hE, one_div_pow, mul_one_div, div_self (by positivity)]
  have hhalf1 : (1 / 2 : ℝ) ^ emax ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hhalf0 : 0 ≤ (1 / 2 : ℝ) ^ emax := by positivity
  have hδu : (1 / 2 : ℝ) ^ W ≤ u := by
    rw [hδ]
    exact mul_le_of_le_one_right hu0.le hhalf1
  have hδ0 : 0 ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hX : |xv| * (1 / 2 : ℝ) ^ W ≤ u := by
    rw [hδ]
    have : |xv| * (1 / 2 : ℝ) ^ emax ≤ E * (1 / 2 : ℝ) ^ emax :=
      mul_le_mul_of_nonneg_right hxE.le hhalf0
    rw [hEu] at this
    calc |xv| * (u * (1 / 2 : ℝ) ^ emax) = u * (|xv| * (1 / 2 : ℝ) ^ emax) := by ring
      _ ≤ u * 1 := mul_le_mul_of_nonneg_left this hu0.le
      _ = u := mul_one u
  -- the bracket of `ln 2`
  obtain ⟨lv, hv', hlv, hhv, hl, hh, hwid, hlv5⟩ := ln2Bracket_spec W
  have hlv5' : 1 / 5 ≤ lv := hlv5 (by omega)
  have hln2lo := Real.log_two_gt_d9
  have hln2hi := Real.log_two_lt_d9
  have hlv0 : 0 < lv := by linarith
  have hhv1 : hv' ≤ 1 := by linarith
  have hlv1 : lv ≤ 1 := by linarith
  -- the quotient and its truncation
  obtain ⟨kq, hkq, hkq1, hkq2⟩ := divFloor_abs hx hlv hlv0.ne' W
  simp only [expReduce]
  generalize hk : truncToAzInt (divPrecRound x (ln2Bracket W).1 W .Floor).1 = k
  obtain ⟨hk1, hk2⟩ := truncToAzInt_spec hkq
  rw [hk] at hk1 hk2
  obtain ⟨kr, hkr⟩ : ∃ kr : ℝ, kr = (k.toInt : ℝ) := ⟨_, rfl⟩
  rw [← hkr] at hk1 hk2
  -- `|kq − x / ln 2| ≤ 1/100`
  have hq1 : |kq - xv / lv| ≤ 10 * u := by
    have habs : |xv / lv| ≤ 5 * |xv| := by
      rw [abs_div, abs_of_pos hlv0, div_le_iff₀ hlv0]
      have := mul_le_mul_of_nonneg_left hlv5' (abs_nonneg xv)
      linarith
    have h3 : 2 * |xv / lv| * (1 / 2 : ℝ) ^ W ≤ 2 * (5 * |xv|) * (1 / 2 : ℝ) ^ W :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0
    rw [abs_le]
    constructor <;> linarith
  have hq2 : |xv / lv - xv / Real.log 2| ≤ 80 * u := by
    have hln0 : 0 < Real.log 2 := by linarith
    rw [div_sub_div _ _ hlv0.ne' hln0.ne', abs_div, abs_of_pos (mul_pos hlv0 hln0),
      div_le_iff₀ (mul_pos hlv0 hln0)]
    have e1 : xv * Real.log 2 - lv * xv = xv * (Real.log 2 - lv) := by ring
    rw [e1, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.log 2 - lv)]
    have h110 : 1 / 10 ≤ lv * Real.log 2 := by nlinarith
    have hwid2 : Real.log 2 - lv ≤ 8 * (1 / 2 : ℝ) ^ W := by linarith
    have hA : |xv| * (Real.log 2 - lv) ≤ |xv| * (8 * (1 / 2 : ℝ) ^ W) :=
      mul_le_mul_of_nonneg_left hwid2 (abs_nonneg _)
    have hB : 80 * u * (1 / 10) ≤ 80 * u * (lv * Real.log 2) :=
      mul_le_mul_of_nonneg_left h110 (by positivity)
    nlinarith
  have hq : |kq - xv / Real.log 2| ≤ 90 * u := by
    calc |kq - xv / Real.log 2| = |(kq - xv / lv) + (xv / lv - xv / Real.log 2)| := by
          rw [sub_add_sub_cancel]
      _ ≤ |kq - xv / lv| + |xv / lv - xv / Real.log 2| := abs_add_le _ _
      _ ≤ 90 * u := by linarith
  have hk101 : |kr - xv / Real.log 2| ≤ 101 / 100 := by
    calc |kr - xv / Real.log 2| = |(kr - kq) + (kq - xv / Real.log 2)| := by
          rw [sub_add_sub_cancel]
      _ ≤ |kr - kq| + |kq - xv / Real.log 2| := abs_add_le _ _
      _ ≤ 101 / 100 := by linarith
  -- `|r| ≤ 71/100` and `|k| ≤ 4 E`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = xv - kr * Real.log 2 := ⟨_, rfl⟩
  have hln0 : 0 < Real.log 2 := by linarith
  have hr71 : |r| ≤ 71 / 100 := by
    have e0 : Real.log 2 * (xv / Real.log 2) = xv := by field_simp
    have e1 : r = Real.log 2 * (xv / Real.log 2 - kr) := by rw [hr, mul_sub, e0]; ring
    rw [e1, abs_mul, abs_of_pos hln0, abs_sub_comm]
    have h2 : Real.log 2 * |kr - xv / Real.log 2| ≤ Real.log 2 * (101 / 100) :=
      mul_le_mul_of_nonneg_left hk101 hln0.le
    linarith
  have hka : |kr| ≤ 4 * E := by
    have h1 : |xv / Real.log 2| ≤ 2 * |xv| := by
      rw [abs_div, abs_of_pos hln0, div_le_iff₀ hln0]
      have := mul_le_mul_of_nonneg_left (by linarith : (1 / 2 : ℝ) ≤ Real.log 2) (abs_nonneg xv)
      linarith
    calc |kr| = |(kr - xv / Real.log 2) + xv / Real.log 2| := by rw [sub_add_cancel]
      _ ≤ |kr - xv / Real.log 2| + |xv / Real.log 2| := abs_add_le _ _
      _ ≤ 4 * E := by linarith
  -- the products `k · ln 2`
  have hkaV : ((k.abs.toNat : ℕ) : ℝ) = |kr| := by
    rw [hkr, ← Int.cast_abs, ← AzInt.abs_toNat_eq, Int.cast_natCast]
  have hka0 : 0 ≤ |kr| := abs_nonneg _
  obtain ⟨plo, hplo, hplo1⟩ := mulFloor_err (toVal_ofAzNat k.abs) hlv W
    (by rw [hkaV]; exact mul_nonneg hka0 hlv0.le)
  obtain ⟨phi, hphi, hphi1⟩ := mulCeiling_err (toVal_ofAzNat k.abs) hhv W
    (by rw [hkaV]; exact mul_nonneg hka0 (by linarith))
  rw [hkaV] at hplo1 hphi1
  have hpwid : phi - plo ≤ 48 * u := by
    have h1 := hplo1.ge
    have h2 := hphi1.le
    have h3 : |kr| * (hv' - lv) ≤ |kr| * (8 * (1 / 2 : ℝ) ^ W) :=
      mul_le_mul_of_nonneg_left hwid hka0
    have h4 : 2 * (|kr| * hv') * (1 / 2 : ℝ) ^ W ≤ 2 * |kr| * (1 / 2 : ℝ) ^ W := by
      have : |kr| * hv' ≤ |kr| * 1 := mul_le_mul_of_nonneg_left hhv1 hka0
      have := mul_le_mul_of_nonneg_right this hδ0
      linarith
    have h5 : 2 * (|kr| * lv) * (1 / 2 : ℝ) ^ W ≤ 2 * |kr| * (1 / 2 : ℝ) ^ W := by
      have : |kr| * lv ≤ |kr| * 1 := mul_le_mul_of_nonneg_left hlv1 hka0
      have := mul_le_mul_of_nonneg_right this hδ0
      linarith
    have h6 : |kr| * (1 / 2 : ℝ) ^ W ≤ 4 * u := by
      calc |kr| * (1 / 2 : ℝ) ^ W ≤ 4 * E * (1 / 2 : ℝ) ^ W :=
            mul_le_mul_of_nonneg_right hka (by positivity)
        _ = 4 * u := by rw [hδ]; linear_combination 4 * u * hEu
    nlinarith
  have hus' : u ≤ 1 / 10000 := by linarith
  -- the two signs of `k`
  have hlog_lv : |kr| * lv ≤ |kr| * Real.log 2 := mul_le_mul_of_nonneg_left hl hka0
  have hlog_hv : |kr| * Real.log 2 ≤ |kr| * hv' := mul_le_mul_of_nonneg_left hh hka0
  split_ifs with hs
  · -- `k ≥ 0`
    have hkr0 : kr = |kr| := by
      rw [hkr, abs_of_nonneg]
      exact_mod_cast (AzInt.sign_eq_true_iff k).mp hs
    obtain ⟨rl, hrl, hrl1, hrl2⟩ := subFloor_abs hx hphi W
    obtain ⟨rh, hrh, hrh1, hrh2⟩ := subCeiling_abs hx hplo W
    refine ⟨rl, rh, hrl, hrh, ?_⟩
    dsimp only
    rw [← hkr, ← hr]
    have hrl2' : xv - phi ≤ rl + 2 * |xv - phi| * u := by
      have : 2 * |xv - phi| * (1 / 2 : ℝ) ^ W ≤ 2 * |xv - phi| * u :=
        mul_le_mul_of_nonneg_left hδu (by positivity)
      linarith
    have hrh2' : rh ≤ xv - plo + 2 * |xv - plo| * u := by
      have : 2 * |xv - plo| * (1 / 2 : ℝ) ^ W ≤ 2 * |xv - plo| * u :=
        mul_le_mul_of_nonneg_left hδu (by positivity)
      linarith
    have hP1 : plo ≤ kr * Real.log 2 := by rw [hkr0]; linarith [hplo1.le]
    have hP2 : kr * Real.log 2 ≤ phi := by rw [hkr0]; linarith [hphi1.ge]
    obtain ⟨c1, c2, c3, c4, c5⟩ := reduce_bounds hu0.le hus' hr hP1 hP2 hpwid hr71 hrl1 hrl2'
      hrh1 hrh2'
    refine ⟨c1, c2, ?_, c4, c5⟩
    calc rh - rl ≤ 52 * u := c3
      _ ≤ 64 * u := by linarith
      _ = (1 / 2 : ℝ) ^ (w + 10) := by rw [hu, pow_add, pow_add]; ring
  · -- `k < 0`
    have hkr0 : kr = -|kr| := by
      have hneg : k.toInt < 0 := by
        have := (AzInt.sign_eq_true_iff k).not.mp hs
        push Not at this
        exact this
      rw [hkr, abs_of_neg (by exact_mod_cast hneg), neg_neg]
    have hkl : kr * Real.log 2 = -(|kr| * Real.log 2) := by rw [neg_mul_eq_neg_mul, ← hkr0]
    obtain ⟨rl, hrl, hrl1, hrl2⟩ := addFloor_abs hx hplo W
    obtain ⟨rh, hrh, hrh1, hrh2⟩ := addCeiling_abs hx hphi W
    refine ⟨rl, rh, hrl, hrh, ?_⟩
    dsimp only
    rw [← hkr, ← hr]
    have hrl2' : xv - -plo ≤ rl + 2 * |xv - -plo| * u := by
      have : 2 * |xv + plo| * (1 / 2 : ℝ) ^ W ≤ 2 * |xv + plo| * u :=
        mul_le_mul_of_nonneg_left hδu (by positivity)
      simp only [sub_neg_eq_add]
      linarith
    have hrh2' : rh ≤ xv - -phi + 2 * |xv - -phi| * u := by
      have : 2 * |xv + phi| * (1 / 2 : ℝ) ^ W ≤ 2 * |xv + phi| * u :=
        mul_le_mul_of_nonneg_left hδu (by positivity)
      simp only [sub_neg_eq_add]
      linarith
    have hP1 : -phi ≤ kr * Real.log 2 := by linarith [hphi1.ge, hkl, hlog_hv]
    have hP2 : kr * Real.log 2 ≤ -plo := by linarith [hplo1.le, hkl, hlog_lv]
    have hwid' : -plo - -phi ≤ 48 * u := by linarith
    obtain ⟨c1, c2, c3, c4, c5⟩ := reduce_bounds hu0.le hus' hr hP1 hP2 hwid' hr71
      (by simpa only [sub_neg_eq_add] using hrl1) hrl2'
      (by simpa only [sub_neg_eq_add] using hrh1) hrh2'
    refine ⟨c1, c2, ?_, c4, c5⟩
    calc rh - rl ≤ 52 * u := c3
      _ ≤ 64 * u := by linarith
      _ = (1 / 2 : ℝ) ^ (w + 10) := by rw [hu, pow_add, pow_add]; ring

/-! ### The small-argument bracket -/

set_option maxHeartbeats 1000000 in
/-- `expSmallBracket` encloses `exp` over `[rl, rh]` for `0 ≤ rl ≤ rh ≤ 3/4` and
`rh − rl ≤ 2^(−w−10)`: relative errors `9 (K + 1) u` below and `18 (K + 1) u` above, with
`u = 2^(−w)` and `K = expK w`. -/
theorem expSmallBracket_spec {rl rh : AzFloat} {rlv rhv : ℝ}
    (hrl : rl.toVal = some (rlv : EReal)) (hrh : rh.toVal = some (rhv : EReal)) (h0 : 0 ≤ rlv)
    (hle : rlv ≤ rhv) (h34 : rhv ≤ 3 / 4) {w : ℕ} (hw : 64 ≤ w)
    (hwid : rhv - rlv ≤ (1 / 2 : ℝ) ^ (w + 10)) :
    ∃ lo hi : ℝ, (expSmallBracket rl rh w).1.toVal = some (lo : EReal) ∧
      (expSmallBracket rl rh w).2.toVal = some (hi : EReal) ∧ 0 < lo ∧
      Real.exp rlv * (1 - 9 * (expK w + 1) * (1 / 2 : ℝ) ^ w) ≤ lo ∧ lo ≤ Real.exp rlv ∧
      Real.exp rhv ≤ hi ∧ hi ≤ Real.exp rhv * (1 + 18 * (expK w + 1) * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨hK1, hK2⟩ := expK_spec w
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = expK w := ⟨_, rfl⟩
  rw [← hK] at hK1 hK2 ⊢
  have : NeZero (w + 8) := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 < u := by rw [hu]; positivity
  have hus : u ≤ 1 / 10 ^ 18 := hu ▸ half_pow_small hw
  have hu1 : u ≤ 1 := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hnu : 40 * ((K : ℝ) + 1) * u ≤ 1 := by
    have h := forty_mul_half_pow_le hw
    rw [← hu] at h
    have hK' : (K : ℝ) + 1 ≤ w + 9 := by exact_mod_cast (by omega : K + 1 ≤ w + 9)
    have := mul_le_mul_of_nonneg_right hK' hu0.le
    linarith
  have hKu0 : 0 ≤ (K : ℝ) * u := mul_nonneg hK0 hu0.le
  have hKuu0 : 0 ≤ (K : ℝ) * u * u := mul_nonneg hKu0 hu0.le
  have huu0 : 0 ≤ u * u := mul_nonneg hu0.le hu0.le
  have hKuu1 : (K : ℝ) * u * u ≤ K * u := mul_le_of_le_one_right hKu0 hu1
  have huu1 : u * u ≤ u := mul_le_of_le_one_right hu0.le hu1
  have h256 : ((1 : ℝ) / 2) ^ 8 = 1 / 256 := by norm_num
  have hu8 : (1 / 2 : ℝ) ^ (w + 8) = u / 256 := by rw [hu, pow_add, h256]; ring
  have hu10 : (1 / 2 : ℝ) ^ (w + 10) = u / 1024 := by
    rw [hu, pow_add, show ((1 : ℝ) / 2) ^ 10 = 1 / 1024 by norm_num]; ring
  rw [hu10] at hwid
  -- the truncation `t = M / 2^(2^K)`
  obtain ⟨M1, M2⟩ := floorScaled_spec hrl (2 ^ K)
  rw [abs_of_nonneg h0] at M1 M2
  simp only [expSmallBracket]
  rw [← hK]
  generalize hM : floorScaled rl (2 ^ K) = M at M1 M2 ⊢
  have hN0 : (0 : ℝ) < 2 ^ (2 ^ K) := by positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (M.toNat : ℝ) / 2 ^ (2 ^ K) := ⟨_, rfl⟩
  have ht1 : t ≤ rlv := by rw [ht, div_le_iff₀ hN0]; exact M1
  have ht2 : rlv < t + (1 / 2 : ℝ) ^ (2 ^ K) := by
    have h : rlv < ((M.toNat : ℝ) + 1) / 2 ^ (2 ^ K) := by rw [lt_div_iff₀ hN0]; exact M2
    rw [add_div] at h
    rw [ht, one_div_pow]
    exact h
  have hsmall : (1 / 2 : ℝ) ^ (2 ^ K) ≤ (1 / 2 : ℝ) ^ (w + 9) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hu9 : (1 / 2 : ℝ) ^ (w + 9) = u / 512 := by
    rw [hu, pow_add, show ((1 : ℝ) / 2) ^ 9 = 1 / 512 by norm_num]; ring
  rw [hu9] at hsmall
  have hMlt : M.toNat < 2 ^ (2 ^ K) := by
    have h : (M.toNat : ℝ) < 2 ^ (2 ^ K) := by
      calc (M.toNat : ℝ) ≤ rlv * 2 ^ (2 ^ K) := M1
        _ ≤ (3 / 4) * 2 ^ (2 ^ K) := mul_le_mul_of_nonneg_right (by linarith) hN0.le
        _ < 2 ^ (2 ^ K) := by linarith
    exact_mod_cast h
  obtain ⟨lo, Eh, hlo, hEh, hlo0, hlo1, hlo2, hEh1, hEh2⟩ :=
    expDyadicBracket_spec M K w (by omega) hMlt
  rw [← ht] at hlo1 hlo2 hEh1 hEh2
  rw [← hu] at hlo1 hEh2
  -- the float `t`
  have htF : (ofAzNat M >>> (2 ^ K : ℕ)).toVal = some (t : EReal) := by
    show (shiftRight (ofAzNat M) (AzNat.ofNat (2 ^ K)).toAzInt).toVal = _
    rw [toVal_shiftRight, toVal_ofAzNat, Option.map_some, toInt_toAzInt, AzNat.toNat_ofNat,
      ← EReal.coe_mul, zpow_neg, zpow_natCast, ht, div_eq_mul_inv]
  -- the distance `d` to the upper end
  have hd0 : 0 ≤ rhv - t := by linarith
  obtain ⟨dv, hd, hd1, hd2⟩ := subCeiling_abs hrh htF (w + 8)
  rw [abs_of_nonneg hd0, hu8] at hd2
  have hdt : rhv - t ≤ u / 256 := by linarith
  have hdv2 : dv ≤ u / 128 := by
    have h1 : 2 * (rhv - t) * (u / 256) ≤ 2 * (rhv - t) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hdv0 : 0 ≤ dv := by linarith
  have h2d : ((subPrecRound rh (ofAzNat M >>> (2 ^ K : ℕ)) (w + 8) .Ceiling).1 <<< (1 : ℕ)).toVal
      = some ((2 * dv : ℝ) : EReal) := by
    show (shiftLeft _ (AzNat.ofNat 1).toAzInt).toVal = _
    rw [toVal_shiftLeft, hd, Option.map_some, toInt_toAzInt, AzNat.toNat_ofNat, ← EReal.coe_mul,
      Nat.cast_one, zpow_one, mul_comm]
  -- the factor `f ≥ 1 + 2d`
  obtain ⟨fv, hf, hf1⟩ := addCeiling_err toVal_one' h2d (w + 8) (by linarith)
  have hEh0 : 0 < Eh := lt_of_lt_of_le (Real.exp_pos t) hEh1
  have hf0 : 0 ≤ fv := by linarith [hf1.ge]
  obtain ⟨hi, hhi, hhi1⟩ := mulCeiling_err hEh hf (w + 8) (mul_nonneg hEh0.le hf0)
  refine ⟨lo, hi, hlo, hhi, hlo0, ?_, hlo2.trans (Real.exp_le_exp.mpr ht1), ?_, ?_⟩
  · -- the lower end
    have hpow : 1 - 8 * ((K : ℝ) + 1) * u ≤ (1 - 8 * u) ^ (K + 1) := by
      have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(8 * u)) (K + 1)
      have e1 : (1 : ℝ) + -(8 * u) = 1 - 8 * u := by ring
      rw [e1] at h
      push_cast at h
      linarith
    have hexp : Real.exp rlv * (1 - u / 512) ≤ Real.exp t := by
      have h := exp_mul_one_sub_le_exp t rlv
      have h' : Real.exp rlv * (1 - u / 512) ≤ Real.exp rlv * (1 - (rlv - t)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      linarith
    calc Real.exp rlv * (1 - 9 * ((K : ℝ) + 1) * u)
        ≤ Real.exp rlv * ((1 - u / 512) * (1 - 8 * ((K : ℝ) + 1) * u)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          nlinarith
      _ = (Real.exp rlv * (1 - u / 512)) * (1 - 8 * ((K : ℝ) + 1) * u) := by ring
      _ ≤ Real.exp t * (1 - 8 * u) ^ (K + 1) :=
          mul_le_mul hexp hpow (by linarith) (Real.exp_pos _).le
      _ ≤ lo := hlo1
  · -- `exp rh ≤ hi`
    have h1 : Real.exp rhv ≤ Real.exp t * (1 + 2 * (rhv - t)) :=
      exp_le_exp_mul_one_add (by linarith) (by linarith)
    have h2 : Real.exp t * (1 + 2 * (rhv - t)) ≤ Eh * fv :=
      mul_le_mul hEh1 (by linarith [hf1.ge]) (by linarith) hEh0.le
    linarith [hhi1.ge]
  · -- the upper end
    have hpow := one_add_eight_mul_pow_le (K + 1) hu0.le (by push_cast; linarith)
    push_cast at hpow
    have hfv : fv ≤ 1 + u / 32 := by
      have h := hf1.le
      rw [hu8] at h
      have h4 : dv * u ≤ u / 128 * 1 := mul_le_mul hdv2 hu1 hu0.le (by linarith)
      nlinarith
    have hhi' : hi ≤ Eh * fv * (1 + u / 128) := by
      have := hhi1.le
      rw [hu8] at this
      linarith
    have hEh' : Eh ≤ Real.exp rhv * (1 + 16 * ((K : ℝ) + 1) * u) := by
      calc Eh ≤ Real.exp t * (1 + 8 * u) ^ (K + 1) := hEh2
        _ ≤ Real.exp rhv * (1 + 16 * ((K : ℝ) + 1) * u) :=
          mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hpow (by positivity) (Real.exp_pos _).le
    have hfac : (1 + 16 * ((K : ℝ) + 1) * u) * (1 + u / 32) * (1 + u / 128)
        ≤ 1 + 18 * ((K : ℝ) + 1) * u := by
      have h1 : (1 + u / 32) * (1 + u / 128) ≤ 1 + u / 16 := by nlinarith
      have h2 : (1 + 16 * ((K : ℝ) + 1) * u) * (1 + u / 16) ≤ 1 + 18 * ((K : ℝ) + 1) * u := by
        nlinarith
      calc (1 + 16 * ((K : ℝ) + 1) * u) * (1 + u / 32) * (1 + u / 128)
          = (1 + 16 * ((K : ℝ) + 1) * u) * ((1 + u / 32) * (1 + u / 128)) := by ring
        _ ≤ (1 + 16 * ((K : ℝ) + 1) * u) * (1 + u / 16) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 + 18 * ((K : ℝ) + 1) * u := h2
    calc hi ≤ Eh * fv * (1 + u / 128) := hhi'
      _ ≤ (Real.exp rhv * (1 + 16 * ((K : ℝ) + 1) * u)) * (1 + u / 32) * (1 + u / 128) := by
          gcongr
      _ = Real.exp rhv * ((1 + 16 * ((K : ℝ) + 1) * u) * (1 + u / 32) * (1 + u / 128)) := by
          ring
      _ ≤ Real.exp rhv * (1 + 18 * ((K : ℝ) + 1) * u) :=
          mul_le_mul_of_nonneg_left hfac (Real.exp_pos _).le

/-! ### The sign dispatch -/

set_option maxHeartbeats 1000000 in
/-- `expSignedBracket` encloses `exp r` for `r ∈ [rl, rh] ⊆ [−3/4, 3/4]` with
`rh − rl ≤ 2^(−w−10)`: relative errors `40 (K + 1) 2^(−w)` on either side. -/
theorem expSignedBracket_spec {rl rh : AzFloat} {rlv rhv r : ℝ}
    (hrl : rl.toVal = some (rlv : EReal)) (hrh : rh.toVal = some (rhv : EReal)) (h1 : rlv ≤ r)
    (h2 : r ≤ rhv) (h3 : -3 / 4 ≤ rlv) (h4 : rhv ≤ 3 / 4) {w : ℕ} (hw : 64 ≤ w)
    (hwid : rhv - rlv ≤ (1 / 2 : ℝ) ^ (w + 10)) :
    ∃ lo hi : ℝ, (expSignedBracket rl rh w).1.toVal = some (lo : EReal) ∧
      (expSignedBracket rl rh w).2.toVal = some (hi : EReal) ∧ 0 < lo ∧
      Real.exp r * (1 - 40 * (expK w + 1) * (1 / 2 : ℝ) ^ w) ≤ lo ∧ lo ≤ Real.exp r ∧
      Real.exp r ≤ hi ∧ hi ≤ Real.exp r * (1 + 40 * (expK w + 1) * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨hK1, hK2⟩ := expK_spec w
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = expK w := ⟨_, rfl⟩
  rw [← hK] at hK1 hK2 ⊢
  have : NeZero (w + 8) := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 < u := by rw [hu]; positivity
  have hus : u ≤ 1 / 10 ^ 18 := hu ▸ half_pow_small hw
  have hu1 : u ≤ 1 := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hnu : 40 * ((K : ℝ) + 1) * u ≤ 1 := by
    have h := forty_mul_half_pow_le hw
    rw [← hu] at h
    have hK' : (K : ℝ) + 1 ≤ w + 9 := by exact_mod_cast (by omega : K + 1 ≤ w + 9)
    have := mul_le_mul_of_nonneg_right hK' hu0.le
    linarith
  have hKu0 : 0 ≤ (K : ℝ) * u := mul_nonneg hK0 hu0.le
  have hKuu0 : 0 ≤ (K : ℝ) * u * u := mul_nonneg hKu0 hu0.le
  have huu0 : 0 ≤ u * u := mul_nonneg hu0.le hu0.le
  have hKuu1 : (K : ℝ) * u * u ≤ K * u := mul_le_of_le_one_right hKu0 hu1
  have huu1 : u * u ≤ u := mul_le_of_le_one_right hu0.le hu1
  have h256 : ((1 : ℝ) / 2) ^ 8 = 1 / 256 := by norm_num
  have hu8 : (1 / 2 : ℝ) ^ (w + 8) = u / 256 := by rw [hu, pow_add, h256]; ring
  have hu10 : (1 / 2 : ℝ) ^ (w + 10) = u / 1024 := by
    rw [hu, pow_add, show ((1 : ℝ) / 2) ^ 10 = 1 / 1024 by norm_num]; ring
  have hwidu : rhv - rlv ≤ u / 1024 := by rw [hu10] at hwid; exact hwid
  have hEr := Real.exp_pos r
  unfold expSignedBracket
  split_ifs with hneg hpos
  · -- `rl < 0 < rh`
    have hrlv0 : rlv < 0 := (toVal_sign_of_isNegative hrl).1 hneg
    have hrhv0 : 0 < rhv := (toVal_sign_of_isPositive hrh).1 hpos
    obtain ⟨lo, hlo, hlo1⟩ := addFloor_err toVal_one' hrl (w + 8) (by linarith)
    have h2rh : (rh <<< (1 : ℕ)).toVal = some ((2 * rhv : ℝ) : EReal) := by
      show (shiftLeft rh (AzNat.ofNat 1).toAzInt).toVal = _
      rw [toVal_shiftLeft, hrh, Option.map_some, toInt_toAzInt, AzNat.toNat_ofNat,
        ← EReal.coe_mul, Nat.cast_one, zpow_one, mul_comm]
    obtain ⟨hi, hhi, hhi1⟩ := addCeiling_err toVal_one' h2rh (w + 8) (by linarith)
    have hrh' : rhv ≤ u / 1024 := by linarith
    have hrl' : -(u / 1024) ≤ rlv := by linarith
    have hlo2 := hlo1.le
    have hlo3 : (1 + rlv) * (1 - u / 128) ≤ lo := by
      have := hlo1.ge
      rw [hu8] at this
      linarith
    have hhi2 := hhi1.ge
    have hhi3 : hi ≤ (1 + 2 * rhv) * (1 + u / 128) := by
      have := hhi1.le
      rw [hu8] at this
      linarith
    have e1 : rlv + 1 ≤ Real.exp rlv := Real.add_one_le_exp rlv
    have e2 : Real.exp rlv ≤ Real.exp r := Real.exp_le_exp.mpr h1
    have e3 : Real.exp r ≤ Real.exp rhv := Real.exp_le_exp.mpr h2
    have e4 : Real.exp rhv ≤ 1 + 2 * rhv := exp_le_one_add_two_mul hrhv0.le (by linarith)
    have hA : 1 - u / 64 ≤ (1 + rlv) * (1 - u / 128) := by
      have := mul_le_mul_of_nonneg_right hrl' (by linarith : (0 : ℝ) ≤ 1 - u / 128)
      nlinarith
    have hB : (1 + 2 * rhv) * (1 + u / 128) ≤ 1 + u / 64 := by
      have := mul_le_mul_of_nonneg_right hrh' (by linarith : (0 : ℝ) ≤ 1 + u / 128)
      nlinarith
    refine ⟨lo, hi, hlo, hhi, by linarith, ?_, by linarith, by linarith, ?_⟩
    · have hC : Real.exp r * (1 - 40 * ((K : ℝ) + 1) * u) ≤ Real.exp r * (1 - 40 * u) :=
        mul_le_mul_of_nonneg_left (by linarith) hEr.le
      have hD : Real.exp r * (1 - 40 * u) ≤ (1 + u / 512) * (1 - 40 * u) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      nlinarith
    · have hG : 1 - u / 1024 ≤ Real.exp r := by linarith
      have hH : (1 - u / 1024) * (1 + 40 * u) ≤ Real.exp r * (1 + 40 * u) :=
        mul_le_mul_of_nonneg_right hG (by linarith)
      have hI : Real.exp r * (1 + 40 * u) ≤ Real.exp r * (1 + 40 * ((K : ℝ) + 1) * u) :=
        mul_le_mul_of_nonneg_left (by linarith) hEr.le
      nlinarith
  · -- `rl < 0`, `rh ≤ 0`: through `exp (−r)` and a reciprocal
    have hrlv0 : rlv < 0 := (toVal_sign_of_isNegative hrl).1 hneg
    have hrhv0 : rhv ≤ 0 := (toVal_sign_of_isPositive hrh).2 (by simpa using hpos)
    have hnrh : (-rh).toVal = some ((-rhv : ℝ) : EReal) := by
      rw [toVal_neg, hrh, Option.map_some, EReal.coe_neg]
    have hnrl : (-rl).toVal = some ((-rlv : ℝ) : EReal) := by
      rw [toVal_neg, hrl, Option.map_some, EReal.coe_neg]
    obtain ⟨A, B, hA, hB, hA0, hA1, hA2, hB1, hB2⟩ :=
      expSmallBracket_spec hnrh hnrl (by linarith) (by linarith) (by linarith) hw (by linarith)
    rw [← hK, ← hu] at hA1 hB2
    have hB0 : 0 < B := lt_of_lt_of_le (Real.exp_pos _) hB1
    obtain ⟨lo, hlo, hlo1⟩ := divFloor_err toVal_one' hB hB0 zero_le_one (w + 8)
    obtain ⟨hi, hhi, hhi1⟩ := divCeiling_err toVal_one' hA hA0 zero_le_one (w + 8)
    have hEn : Real.exp (-r) = 1 / Real.exp r := by rw [Real.exp_neg, one_div]
    have hEn0 : 0 < Real.exp (-r) := Real.exp_pos _
    have hL : Real.exp (-r) * (1 - u / 1024) ≤ Real.exp (-rhv) := by
      have h := exp_mul_one_sub_le_exp (-rhv) (-r)
      have h' : Real.exp (-r) * (1 - u / 1024) ≤ Real.exp (-r) * (1 - (-r - -rhv)) :=
        mul_le_mul_of_nonneg_left (by linarith) hEn0.le
      linarith
    have hU : Real.exp (-rlv) ≤ Real.exp (-r) * (1 + u / 512) := by
      have h := exp_le_exp_mul_one_add (a := -r) (b := -rlv) (by linarith) (by linarith)
      have h' : Real.exp (-r) * (1 + 2 * (-rlv - -r)) ≤ Real.exp (-r) * (1 + u / 512) :=
        mul_le_mul_of_nonneg_left (by linarith) hEn0.le
      linarith
    have hA3 : Real.exp (-r) * (1 - 10 * ((K : ℝ) + 1) * u) ≤ A := by
      calc Real.exp (-r) * (1 - 10 * ((K : ℝ) + 1) * u)
          ≤ Real.exp (-r) * ((1 - u / 1024) * (1 - 9 * ((K : ℝ) + 1) * u)) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hEn0.le
        _ = (Real.exp (-r) * (1 - u / 1024)) * (1 - 9 * ((K : ℝ) + 1) * u) := by ring
        _ ≤ Real.exp (-rhv) * (1 - 9 * ((K : ℝ) + 1) * u) :=
            mul_le_mul_of_nonneg_right hL (by linarith)
        _ ≤ A := hA1
    have hB3 : B ≤ Real.exp (-r) * (1 + 19 * ((K : ℝ) + 1) * u) := by
      calc B ≤ Real.exp (-rlv) * (1 + 18 * ((K : ℝ) + 1) * u) := hB2
        _ ≤ (Real.exp (-r) * (1 + u / 512)) * (1 + 18 * ((K : ℝ) + 1) * u) :=
            mul_le_mul_of_nonneg_right hU (by positivity)
        _ = Real.exp (-r) * ((1 + u / 512) * (1 + 18 * ((K : ℝ) + 1) * u)) := by ring
        _ ≤ Real.exp (-r) * (1 + 19 * ((K : ℝ) + 1) * u) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hEn0.le
    have hinvB : 1 / Real.exp (-r) * (1 - 19 * ((K : ℝ) + 1) * u) ≤ 1 / B :=
      one_div_ge_of_le (by positivity) (by linarith) hEn0 hB0 hB3
    have hinvA : 1 / A ≤ 1 / Real.exp (-r) * (1 + 2 * (10 * ((K : ℝ) + 1) * u)) :=
      one_div_le_of_ge (by positivity) (by linarith) hEn0 hA0 hA3
    rw [hEn, one_div_one_div] at hinvB hinvA
    have hlo2 : lo ≤ 1 / B := hlo1.le
    have hlo3 : 1 / B * (1 - u / 128) ≤ lo := by
      have := hlo1.ge
      rw [hu8] at this
      linarith
    have hhi2 : 1 / A ≤ hi := hhi1.ge
    have hhi3 : hi ≤ 1 / A * (1 + u / 128) := by
      have := hhi1.le
      rw [hu8] at this
      linarith
    have hBge : Real.exp (-r) ≤ B := le_trans (Real.exp_le_exp.mpr (by linarith)) hB1
    have hAle : A ≤ Real.exp (-r) := hA2.trans (Real.exp_le_exp.mpr (by linarith))
    have h1B : 1 / B ≤ Real.exp r := by
      have := one_div_le_one_div_of_le hEn0 hBge
      rwa [hEn, one_div_one_div] at this
    have h1A : Real.exp r ≤ 1 / A := by
      have := one_div_le_one_div_of_le hA0 hAle
      rwa [hEn, one_div_one_div] at this
    have hpos0 : 0 < Real.exp r * (1 - 19 * ((K : ℝ) + 1) * u) * (1 - u / 128) :=
      mul_pos (mul_pos hEr (by linarith)) (by linarith)
    refine ⟨lo, hi, hlo, hhi, ?_, ?_, hlo2.trans h1B, h1A.trans hhi2, ?_⟩
    · calc 0 < Real.exp r * (1 - 19 * ((K : ℝ) + 1) * u) * (1 - u / 128) := hpos0
        _ ≤ 1 / B * (1 - u / 128) := mul_le_mul_of_nonneg_right hinvB (by linarith)
        _ ≤ lo := hlo3
    · calc Real.exp r * (1 - 40 * ((K : ℝ) + 1) * u)
          ≤ Real.exp r * ((1 - 19 * ((K : ℝ) + 1) * u) * (1 - u / 128)) := by
            apply mul_le_mul_of_nonneg_left _ hEr.le
            nlinarith
        _ = Real.exp r * (1 - 19 * ((K : ℝ) + 1) * u) * (1 - u / 128) := by ring
        _ ≤ lo := (mul_le_mul_of_nonneg_right hinvB (by linarith)).trans hlo3
    · calc hi ≤ 1 / A * (1 + u / 128) := hhi3
        _ ≤ Real.exp r * (1 + 2 * (10 * ((K : ℝ) + 1) * u)) * (1 + u / 128) :=
            mul_le_mul_of_nonneg_right hinvA (by linarith)
        _ = Real.exp r * ((1 + 20 * ((K : ℝ) + 1) * u) * (1 + u / 128)) := by ring
        _ ≤ Real.exp r * (1 + 40 * ((K : ℝ) + 1) * u) := by
            apply mul_le_mul_of_nonneg_left _ hEr.le
            nlinarith
  · -- `rl ≥ 0`
    have hrlv0 : 0 ≤ rlv := (toVal_sign_of_isNegative hrl).2 (by simpa using hneg)
    obtain ⟨lo, hi, hlo, hhi, hlo0, hlo1, hlo2, hhi1, hhi2⟩ :=
      expSmallBracket_spec hrl hrh hrlv0 (by linarith) h4 hw hwid
    rw [← hK, ← hu] at hlo1 hhi2
    refine ⟨lo, hi, hlo, hhi, hlo0, ?_, hlo2.trans (Real.exp_le_exp.mpr h1),
      (Real.exp_le_exp.mpr h2).trans hhi1, ?_⟩
    · have hL : Real.exp r * (1 - u / 1024) ≤ Real.exp rlv := by
        have h := exp_mul_one_sub_le_exp rlv r
        have h' : Real.exp r * (1 - u / 1024) ≤ Real.exp r * (1 - (r - rlv)) :=
          mul_le_mul_of_nonneg_left (by linarith) hEr.le
        linarith
      calc Real.exp r * (1 - 40 * ((K : ℝ) + 1) * u)
          ≤ Real.exp r * ((1 - u / 1024) * (1 - 9 * ((K : ℝ) + 1) * u)) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hEr.le
        _ = (Real.exp r * (1 - u / 1024)) * (1 - 9 * ((K : ℝ) + 1) * u) := by ring
        _ ≤ Real.exp rlv * (1 - 9 * ((K : ℝ) + 1) * u) :=
            mul_le_mul_of_nonneg_right hL (by linarith)
        _ ≤ lo := hlo1
    · have hU : Real.exp rhv ≤ Real.exp r * (1 + u / 512) := by
        have h := exp_le_exp_mul_one_add h2 (by linarith)
        have h' : Real.exp r * (1 + 2 * (rhv - r)) ≤ Real.exp r * (1 + u / 512) :=
          mul_le_mul_of_nonneg_left (by linarith) hEr.le
        linarith
      calc hi ≤ Real.exp rhv * (1 + 18 * ((K : ℝ) + 1) * u) := hhi2
        _ ≤ (Real.exp r * (1 + u / 512)) * (1 + 18 * ((K : ℝ) + 1) * u) :=
            mul_le_mul_of_nonneg_right hU (by positivity)
        _ = Real.exp r * ((1 + u / 512) * (1 + 18 * ((K : ℝ) + 1) * u)) := by ring
        _ ≤ Real.exp r * (1 + 40 * ((K : ℝ) + 1) * u) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hEr.le

/-! ### The full bracket and the Ziv certificate -/

/-- The width bound of `expBracket`. -/
noncomputable def expEps (xv : ℝ) (w : ℕ) : ℝ :=
  Real.exp xv * (80 * ((w : ℝ) + 9)) * (1 / 2 : ℝ) ^ w

theorem tendsto_expEps (xv : ℝ) : Filter.Tendsto (expEps xv) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1
    (by norm_num : |(1 / 2 : ℝ)| < 1)).const_mul (Real.exp xv * 800)
  rw [mul_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · exact Filter.Eventually.of_forall fun w => by unfold expEps; positivity
  · refine Filter.eventually_atTop.mpr ⟨1, fun w hw => ?_⟩
    unfold expEps
    have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    have hE := (Real.exp_pos xv).le
    have h1 : 80 * ((w : ℝ) + 9) ≤ 800 * w := by linarith
    calc Real.exp xv * (80 * ((w : ℝ) + 9)) * (1 / 2 : ℝ) ^ w
        ≤ Real.exp xv * (800 * w) * (1 / 2 : ℝ) ^ w := by gcongr
      _ = Real.exp xv * 800 * ((w : ℝ) ^ 1 * (1 / 2 : ℝ) ^ w) := by rw [pow_one]; ring

/-- `expBracket x e w` encloses `exp x` for a float `x` with `|x| < 2^e`, with width at most
`expEps x w`. -/
theorem expBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (e : AzInt)
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (expBracket x e w).1.toVal = some (lo : EReal) ∧
      (expBracket x e w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.exp xv ∧ Real.exp xv ≤ hi ∧ hi - lo ≤ expEps xv w := by
  obtain ⟨rl, rh, hrl, hrh, h1, h2, hwid, h3, h4⟩ := expReduce_spec hx e hxe w hw
  obtain ⟨lo, hi, hlo, hhi, hlo0, hlo1, hlo2, hhi1, hhi2⟩ :=
    expSignedBracket_spec hrl hrh h1 h2 h3 h4 hw hwid
  simp only [expBracket]
  generalize hk : (expReduce x (expWork e w)).1 = k at h1 h2 hlo1 hlo2 hhi1 hhi2 ⊢
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = xv - k.toInt * Real.log 2 := ⟨_, rfl⟩
  rw [← hr] at hlo1 hlo2 hhi1 hhi2
  have hpow : (2 : ℝ) ^ k.toInt = Real.exp (k.toInt * Real.log 2) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  have hsplit : Real.exp xv = Real.exp r * 2 ^ k.toInt := by
    rw [hpow, ← Real.exp_add, hr]
    congr 1
    ring
  have h2k : 0 < (2 : ℝ) ^ k.toInt := zpow_pos (by norm_num) _
  refine ⟨lo * 2 ^ k.toInt, hi * 2 ^ k.toInt, toVal_shiftLeft_of_toVal hlo k,
    toVal_shiftLeft_of_toVal hhi k, ?_, ?_, ?_⟩
  · rw [hsplit]
    exact mul_le_mul_of_nonneg_right hlo2 h2k.le
  · rw [hsplit]
    exact mul_le_mul_of_nonneg_right hhi1 h2k.le
  · have hK' : ((expK w : ℕ) : ℝ) + 1 ≤ (w : ℝ) + 9 := by
      exact_mod_cast (by have := (expK_spec w).2; omega : expK w + 1 ≤ w + 9)
    have hEr := Real.exp_pos r
    have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
    have h5 : hi - lo ≤ Real.exp r * (80 * (expK w + 1) * (1 / 2 : ℝ) ^ w) := by linarith
    have h6 : Real.exp r * (80 * (expK w + 1) * (1 / 2 : ℝ) ^ w)
        ≤ Real.exp r * (80 * ((w : ℝ) + 9) * (1 / 2 : ℝ) ^ w) := by
      apply mul_le_mul_of_nonneg_left _ hEr.le
      have := mul_le_mul_of_nonneg_right hK' hu0.le
      linarith
    unfold expEps
    rw [hsplit]
    calc hi * 2 ^ k.toInt - lo * 2 ^ k.toInt = (hi - lo) * 2 ^ k.toInt := by ring
      _ ≤ Real.exp r * (80 * ((w : ℝ) + 9) * (1 / 2 : ℝ) ^ w) * 2 ^ k.toInt :=
          mul_le_mul_of_nonneg_right (h5.trans h6) h2k.le
      _ = Real.exp r * 2 ^ k.toInt * (80 * ((w : ℝ) + 9)) * (1 / 2 : ℝ) ^ w := by ring

/-- `exp x` is irrational for every finite float `x` (which is a nonzero rational). -/
theorem irrational_exp_finiteVal (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) : Irrational (Real.exp (finiteVal s e m)) := by
  obtain ⟨r, hr⟩ := exists_rat_of_toVal (toVal_finite s e q m hv)
  have h0 := finiteVal_ne_zero s e hv
  rw [hr] at h0 ⊢
  exact irrational_exp_rat (by exact_mod_cast h0)

/-- `expApprox` is a strict enclosure of `exp x` with width at most `expEps x w`. -/
theorem expApprox_spec {w : ℕ} (hw : 64 ≤ w) (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) :
    ∃ lv hv' : ℝ, Rounds (expApprox (finite s e q m hv) e w).1 lv ∧
      Rounds (expApprox (finite s e q m hv) e w).2 hv' ∧
      lv < Real.exp (finiteVal s e m) ∧ Real.exp (finiteVal s e m) < hv' ∧
      hv' - lv ≤ expEps (finiteVal s e m) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ :=
    expBracket_spec (toVal_finite s e q m hv) e (abs_finiteVal_bounds s e hv).2 hw
  have hirr := irrational_exp_finiteVal s e hv
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, h3⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlo
    exact lt_of_le_of_ne h1 (by rw [hr]; exact (hirr.ne_rat r).symm)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhi
    exact lt_of_le_of_ne h2 (by rw [hr]; exact hirr.ne_rat r)

/-- The Ziv certificate: at some working precision `w₀ · 2^f`, rounding is possible. -/
theorem expApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (s : Bool) (e : AzInt)
    {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (expApprox (finite s e q m hv) e (w₀ * 2 ^ f)).1
      (expApprox (finite s e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (expApprox (finite s e q m hv) e)
    (irrational_exp_finiteVal s e hv) (expEps (finiteVal s e m)) (tendsto_expEps _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := expApprox_spec hw s e hv
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-! ### A rational argument -/

/-- `expBracketAt` encloses `exp x` for a finite float or zero `x`. -/
theorem expBracketAt_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {w : ℕ}
    (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (expBracketAt x w).1.toVal = some (lo : EReal) ∧
      (expBracketAt x w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.exp xv ∧ Real.exp xv ≤ hi ∧ hi - lo ≤ expEps xv w := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero =>
    simp only [toVal_zero, Option.some.injEq] at hx
    have h0 : xv = 0 := by exact_mod_cast hx.symm
    subst h0
    refine ⟨1, 1, toVal_one', toVal_one', by rw [Real.exp_zero], by rw [Real.exp_zero], ?_⟩
    unfold expEps
    have : (0 : ℝ) ≤ Real.exp 0 * (80 * ((w : ℝ) + 9)) * (1 / 2 : ℝ) ^ w := by positivity
    linarith
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    subst hx
    exact expBracket_spec (toVal_finite s e q m hv) e (abs_finiteVal_bounds s e hv).2 hw

/-- The width bound of `expRatBracket`. -/
noncomputable def expRatEps (qv : ℝ) (w : ℕ) : ℝ := 2 * expEps qv w

theorem tendsto_expRatEps (qv : ℝ) :
    Filter.Tendsto (expRatEps qv) Filter.atTop (nhds 0) := by
  have h := (tendsto_expEps qv).const_mul 2
  rw [mul_zero] at h
  exact h

/-- `expRatBracket q w` encloses `exp q` with width at most `expRatEps q w`. -/
theorem expRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) :
    ∃ lo hi : ℝ, (expRatBracket q w).1.toVal = some (lo : EReal) ∧
      (expRatBracket q w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.exp (AzRat.toRat q : ℝ) ∧ Real.exp (AzRat.toRat q : ℝ) ≤ hi ∧
      hi - lo ≤ expRatEps (AzRat.toRat q : ℝ) w := by
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = w + 16 + q.num.size := ⟨_, rfl⟩
  have : NeZero W := ⟨by omega⟩
  have : NeZero (w + 8) := ⟨by omega⟩
  simp only [expRatBracket]
  rw [← hW]
  obtain ⟨qv, hqv⟩ : ∃ qv : ℝ, qv = (AzRat.toRat q : ℝ) := ⟨_, rfl⟩
  rw [← hqv]
  obtain ⟨y, hy, hy1, hy2⟩ := ofAzRatRound_floor_abs q W
  rw [← hqv] at hy1 hy2
  generalize (ofAzRatRound q W .Floor).1 = Y at hy
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expBracketAt_spec hy hw
  -- `q − y ≤ 2^(−w−15)`
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hus : u ≤ 1 / 10 ^ 18 := hu ▸ half_pow_small hw
  have hu1 : u ≤ 1 := by linarith
  have hqs : |qv| < (2 : ℝ) ^ q.num.size := by
    have h := abs_toRat_lt q
    rw [zpow_natCast, ← hqv] at h
    exact h
  have hs0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ q.num.size := by positivity
  have hs1 : (2 : ℝ) ^ q.num.size * (1 / 2 : ℝ) ^ q.num.size = 1 := by
    rw [one_div_pow, mul_one_div, div_self (by positivity)]
  have hqs1 : |qv| * (1 / 2 : ℝ) ^ q.num.size ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hqs.le hs0
    rw [hs1] at this
    exact this
  have hWu : (1 / 2 : ℝ) ^ W = u * (1 / 65536) * (1 / 2 : ℝ) ^ q.num.size := by
    rw [hW, pow_add, pow_add, hu, show ((1 : ℝ) / 2) ^ 16 = 1 / 65536 by norm_num]
  have hd : qv - y ≤ u / 32768 := by
    have e1 : 2 * |qv| * (1 / 2 : ℝ) ^ W = u / 32768 * (|qv| * (1 / 2 : ℝ) ^ q.num.size) := by
      rw [hWu]; ring
    have e2 : u / 32768 * (|qv| * (1 / 2 : ℝ) ^ q.num.size) ≤ u / 32768 * 1 :=
      mul_le_mul_of_nonneg_left hqs1 (by positivity)
    linarith
  have hd0 : 0 ≤ qv - y := by linarith
  -- the widened upper end
  have hEy := Real.exp_pos y
  have hhi0 : 0 < hi := lt_of_lt_of_le hEy h2
  have hshift : ((expBracketAt Y w).2 >>> (w + 14 : ℕ)).toVal
      = some ((hi * (1 / 2 : ℝ) ^ (w + 14) : ℝ) : EReal) := by
    show (shiftRight _ (AzNat.ofNat (w + 14)).toAzInt).toVal = _
    rw [toVal_shiftRight, hhi, Option.map_some, toInt_toAzInt, AzNat.toNat_ofNat,
      ← EReal.coe_mul, zpow_neg, zpow_natCast, one_div_pow, one_div]
  have h14 : (1 / 2 : ℝ) ^ (w + 14) = u / 16384 := by
    rw [pow_add, hu, show ((1 : ℝ) / 2) ^ 14 = 1 / 16384 by norm_num]; ring
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = u / 256 := by
    rw [pow_add, hu, show ((1 : ℝ) / 2) ^ 8 = 1 / 256 by norm_num]; ring
  rw [h14] at hshift
  obtain ⟨hi', hhi', hc⟩ := addCeiling_err hhi hshift (w + 8) (by positivity)
  refine ⟨lo, hi', hlo, hhi', h1.trans (Real.exp_le_exp.mpr hy1), ?_, ?_⟩
  · have e1 : Real.exp qv ≤ Real.exp y * (1 + 2 * (qv - y)) :=
      exp_le_exp_mul_one_add hy1 (by linarith)
    have e2 : Real.exp y * (1 + 2 * (qv - y)) ≤ hi * (1 + u / 16384) :=
      mul_le_mul h2 (by linarith) (by linarith) hhi0.le
    have e3 := hc.ge
    linarith
  · have e1 := hc.le
    rw [h8] at e1
    -- `hi ≤ 3 exp y` from the width bound at `y`
    have hf := forty_mul_half_pow_le hw
    rw [← hu] at hf
    have hhi3 : hi ≤ 3 * Real.exp y := by
      unfold expEps at h3
      rw [← hu] at h3
      have : Real.exp y * (80 * ((w : ℝ) + 9)) * u ≤ Real.exp y * 2 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) hEy.le
      linarith
    have hw0 : (0 : ℝ) ≤ (w : ℝ) + 9 := by positivity
    have hEq : Real.exp y ≤ Real.exp qv := Real.exp_le_exp.mpr hy1
    unfold expRatEps expEps
    rw [← hu]
    unfold expEps at h3
    rw [← hu] at h3
    have hmono : Real.exp y * (80 * ((w : ℝ) + 9)) * u ≤ Real.exp qv * (80 * ((w : ℝ) + 9)) * u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEq (by positivity)) hu0.le
    have hsmall : 3 * Real.exp y * (u / 64) ≤ Real.exp qv * (80 * ((w : ℝ) + 9)) * u := by
      have : Real.exp y * (3 / 64) ≤ Real.exp qv * (80 * ((w : ℝ) + 9)) :=
        mul_le_mul hEq (by linarith) (by norm_num) (Real.exp_pos _).le
      nlinarith
    have hhuu : hi * u * u ≤ hi * u * 1 := mul_le_mul_of_nonneg_left hu1 (by positivity)
    have hhi4 : hi' ≤ hi + hi * (u / 64) := by nlinarith
    have hhi5 : hi * (u / 64) ≤ 3 * Real.exp y * (u / 64) :=
      mul_le_mul_of_nonneg_right hhi3 (by positivity)
    linarith

/-- `exp q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_exp_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.exp (AzRat.toRat q : ℝ)) :=
  irrational_exp_rat (q := AzRat.toRat q)
    (fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp (by rw [h, Rat.cast_zero])))

/-- `expRatApprox` is a strict enclosure of `exp q` with width at most `expRatEps q w`. -/
theorem expRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    ∃ lv hv : ℝ, Rounds (expRatApprox q w).1 lv ∧ Rounds (expRatApprox q w).2 hv ∧
      lv < Real.exp (AzRat.toRat q : ℝ) ∧ Real.exp (AzRat.toRat q : ℝ) < hv ∧
      hv - lv ≤ expRatEps (AzRat.toRat q : ℝ) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expRatBracket_spec hw q
  have hirr := irrational_exp_toRat q h0
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, h3⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlo
    exact lt_of_le_of_ne h1 (by rw [hr]; exact (hirr.ne_rat r).symm)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhi
    exact lt_of_le_of_ne h2 (by rw [hr]; exact hirr.ne_rat r)

/-- The Ziv certificate for `exp q`: at some working precision `w₀ · 2^f`, rounding is
possible. -/
theorem expRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (expRatApprox q (w₀ * 2 ^ f)).1 (expRatApprox q (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (expRatApprox q) (irrational_exp_toRat q h0)
    (expRatEps (AzRat.toRat q : ℝ)) (tendsto_expRatEps _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := expRatApprox_spec hw q h0
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-! ### `exp x − 1` -/

/-- The width bound of `expM1Bracket` at compensation `c`. -/
noncomputable def expM1Eps (xv : ℝ) (c w : ℕ) : ℝ :=
  (2 * Real.exp xv * (80 * ((w : ℝ) + c + 9)) + |Real.exp xv - 1| + 2 * |xv|) * (1 / 2 : ℝ) ^ w

theorem tendsto_expM1Eps (xv : ℝ) (c : ℕ) :
    Filter.Tendsto (expM1Eps xv c) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1
    (by norm_num : |(1 / 2 : ℝ)| < 1)).const_mul
    (2 * Real.exp xv * 160 + |Real.exp xv - 1| + 2 * |xv|)
  rw [mul_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · exact Filter.Eventually.of_forall fun w => by unfold expM1Eps; positivity
  · refine Filter.eventually_atTop.mpr ⟨c + 9, fun w hw => ?_⟩
    unfold expM1Eps
    have hw1 : (c : ℝ) + 9 ≤ w := by exact_mod_cast hw
    have hw0 : (1 : ℝ) ≤ w := by linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
    have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    have hE := (Real.exp_pos xv).le
    have h1 : 2 * Real.exp xv * (80 * ((w : ℝ) + c + 9)) ≤ 2 * Real.exp xv * 160 * w := by
      have : 80 * ((w : ℝ) + c + 9) ≤ 160 * w := by linarith
      nlinarith
    have h2 : |Real.exp xv - 1| ≤ |Real.exp xv - 1| * w :=
      le_mul_of_one_le_right (abs_nonneg _) hw0
    have h3 : 2 * |xv| ≤ 2 * |xv| * w := le_mul_of_one_le_right (by positivity) hw0
    rw [pow_one]
    nlinarith

/-- `expM1Bracket x e w` encloses `exp x − 1` for a float `x` with `|x| < 2^e`, with width at
most `expM1Eps x (expM1Comp e) w`. -/
theorem expM1Bracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (e : AzInt)
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (expM1Bracket x e w).1.toVal = some (lo : EReal) ∧
      (expM1Bracket x e w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.exp xv - 1 ∧ Real.exp xv - 1 ≤ hi ∧ hi - lo ≤ expM1Eps xv (expM1Comp e) w := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = expM1Comp e := ⟨_, rfl⟩
  simp only [expM1Bracket]
  rw [← hc]
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hus : u ≤ 1 / 10 ^ 18 := hu ▸ half_pow_small hw
  have hu1 : u ≤ 1 := by linarith
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = u / 256 := by
    rw [pow_add, hu, show ((1 : ℝ) / 2) ^ 8 = 1 / 256 by norm_num]; ring
  have hEx := Real.exp_pos xv
  unfold expM1Eps
  rw [← hu]
  split_ifs with hwc
  · -- tiny: `e ≤ −w`
    have : NeZero (w + 8) := ⟨by omega⟩
    have hneg : e.toInt ≤ -(w : ℤ) := by
      rw [hc] at hwc
      unfold expM1Comp at hwc
      split_ifs at hwc with hs
      · omega
      · have h1 := (AzInt.sign_eq_true_iff e).not.mp hs
        push Not at h1
        have h2 := AzInt.abs_toNat_eq e
        rw [abs_of_neg h1] at h2
        omega
    have h2e : (2 : ℝ) ^ e.toInt ≤ u := by
      rw [hu, one_div_pow, one_div, ← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) hneg
    have h2e0 : (0 : ℝ) < (2 : ℝ) ^ e.toInt := zpow_pos (by norm_num) _
    have hxu : |xv| < u := hxe.trans_le h2e
    have hx1 : |xv| ≤ 1 := by linarith
    have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
      congr 1
    have hsh := toVal_shiftLeft_of_toVal habs e
    obtain ⟨hi, hhi, hhi1, hhi2⟩ := addCeiling_abs hx hsh (w + 8)
    rw [h8] at hhi2
    refine ⟨xv, hi, hx, hhi, by linarith [Real.add_one_le_exp xv], ?_, ?_⟩
    · have h1 := Real.abs_exp_sub_one_sub_id_le hx1
      rw [abs_le] at h1
      have h2 : xv ^ 2 ≤ |xv| * (2 : ℝ) ^ e.toInt := by
        rw [sq, ← abs_mul_abs_self xv]
        exact mul_le_mul_of_nonneg_left hxe.le (abs_nonneg _)
      linarith
    · have hv : |xv| * (2 : ℝ) ^ e.toInt ≤ |xv| * u :=
        mul_le_mul_of_nonneg_left h2e (abs_nonneg _)
      have hv0 : 0 ≤ |xv| * (2 : ℝ) ^ e.toInt := by positivity
      have hab : |xv + |xv| * (2 : ℝ) ^ e.toInt| ≤ 2 * |xv| := by
        calc |xv + |xv| * (2 : ℝ) ^ e.toInt|
            ≤ |xv| + |(|xv| * (2 : ℝ) ^ e.toInt)| := abs_add_le _ _
          _ ≤ 2 * |xv| := by rw [abs_of_nonneg hv0]; nlinarith [abs_nonneg xv]
      have h3 : 2 * |xv + |xv| * (2 : ℝ) ^ e.toInt| * (u / 256) ≤ 2 * (2 * |xv|) * (u / 256) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h4 : |xv| * u ≤ |xv| * 1 := mul_le_mul_of_nonneg_left hu1 (abs_nonneg _)
      have h5 : 0 ≤ Real.exp xv * (80 * ((w : ℝ) + c + 9)) := by positivity
      have h6 : 0 ≤ |Real.exp xv - 1| := abs_nonneg _
      nlinarith
  · -- general: the compensated `expBracket`
    have : NeZero (w + c + 8) := ⟨by omega⟩
    obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expBracket_spec hx e hxe (w := w + c) (by omega)
    unfold expEps at h3
    have hwc' : (1 / 2 : ℝ) ^ (w + c) ≤ u := by
      rw [hu]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hcast : ((w + c : ℕ) : ℝ) = (w : ℝ) + c := by push_cast; ring
    rw [hcast] at h3
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Real.exp xv * (80 * ((w : ℝ) + c + 9)) * u := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hwid : hi - lo ≤ D := by
      rw [hD]
      calc hi - lo ≤ Real.exp xv * (80 * ((w : ℝ) + c + 9)) * (1 / 2 : ℝ) ^ (w + c) := h3
        _ ≤ Real.exp xv * (80 * ((w : ℝ) + c + 9)) * u :=
          mul_le_mul_of_nonneg_left hwc' (by positivity)
    obtain ⟨lo', hlo', hlo1, hlo2⟩ := subFloor_abs hlo toVal_one' (w + c + 8)
    obtain ⟨hi', hhi', hhi1, hhi2⟩ := subCeiling_abs hhi toVal_one' (w + c + 8)
    have hq : (1 / 2 : ℝ) ^ (w + c + 8) ≤ u / 256 := by
      rw [← h8]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    refine ⟨lo', hi', hlo', hhi', by linarith, by linarith, ?_⟩
    have hA : |lo - 1| ≤ |Real.exp xv - 1| + D := by
      calc |lo - 1| = |(Real.exp xv - 1) - (Real.exp xv - lo)| := by ring_nf
        _ ≤ |Real.exp xv - 1| + |Real.exp xv - lo| := abs_sub _ _
        _ ≤ |Real.exp xv - 1| + D := by
          rw [abs_of_nonneg (by linarith : 0 ≤ Real.exp xv - lo)]; linarith
    have hB : |hi - 1| ≤ |Real.exp xv - 1| + D := by
      calc |hi - 1| = |(Real.exp xv - 1) + (hi - Real.exp xv)| := by ring_nf
        _ ≤ |Real.exp xv - 1| + |hi - Real.exp xv| := abs_add_le _ _
        _ ≤ |Real.exp xv - 1| + D := by
          rw [abs_of_nonneg (by linarith : 0 ≤ hi - Real.exp xv)]; linarith
    have hA' : 2 * |lo - 1| * (1 / 2 : ℝ) ^ (w + c + 8)
        ≤ 2 * (|Real.exp xv - 1| + D) * (u / 256) :=
      mul_le_mul (by linarith) hq (by positivity) (by positivity)
    have hB' : 2 * |hi - 1| * (1 / 2 : ℝ) ^ (w + c + 8)
        ≤ 2 * (|Real.exp xv - 1| + D) * (u / 256) :=
      mul_le_mul (by linarith) hq (by positivity) (by positivity)
    have hDu : D * u ≤ D * 1 := mul_le_mul_of_nonneg_left hu1 hD0
    have hEu : |Real.exp xv - 1| * u ≤ |Real.exp xv - 1| * 1 :=
      mul_le_mul_of_nonneg_left hu1 (abs_nonneg _)
    have h5 : 0 ≤ |xv| * u := by positivity
    nlinarith

/-- `exp x − 1` is irrational for every finite float `x`. -/
theorem irrational_exp_sub_one_finiteVal (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) : Irrational (Real.exp (finiteVal s e m) - 1) := by
  have h := (irrational_exp_finiteVal s e hv).sub_intCast 1
  rwa [Int.cast_one] at h

/-- `expM1Approx` is a strict enclosure of `exp x − 1` with width at most
`expM1Eps x (expM1Comp e) w`. -/
theorem expM1Approx_spec {w : ℕ} (hw : 64 ≤ w) (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) :
    ∃ lv hv' : ℝ, Rounds (expM1Approx (finite s e q m hv) e w).1 lv ∧
      Rounds (expM1Approx (finite s e q m hv) e w).2 hv' ∧
      lv < Real.exp (finiteVal s e m) - 1 ∧ Real.exp (finiteVal s e m) - 1 < hv' ∧
      hv' - lv ≤ expM1Eps (finiteVal s e m) (expM1Comp e) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ :=
    expM1Bracket_spec (toVal_finite s e q m hv) e (abs_finiteVal_bounds s e hv).2 hw
  have hirr := irrational_exp_sub_one_finiteVal s e hv
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, h3⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlo
    exact lt_of_le_of_ne h1 (by rw [hr]; exact (hirr.ne_rat r).symm)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhi
    exact lt_of_le_of_ne h2 (by rw [hr]; exact hirr.ne_rat r)

/-- The Ziv certificate for `exp x − 1`. -/
theorem expM1Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (s : Bool)
    (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (expM1Approx (finite s e q m hv) e (w₀ * 2 ^ f)).1
      (expM1Approx (finite s e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (expM1Approx (finite s e q m hv) e)
    (irrational_exp_sub_one_finiteVal s e hv) (expM1Eps (finiteVal s e m) (expM1Comp e))
    (tendsto_expM1Eps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := expM1Approx_spec hw s e hv
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-! ### `exp q − 1` for a rational -/

/-- The real arithmetic of the width of `expM1RatBracket`. -/
theorem expM1Rat_width {yv lo hi E corr hi' u Dy pw : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hlo : lo ≤ Real.exp yv - 1) (hhi : Real.exp yv - 1 ≤ hi) (hwid : hi - lo ≤ Dy)
    (hE1 : hi + 1 ≤ E) (hE2 : E ≤ hi + 1 + 2 * |hi + 1| * (u / 256))
    (hcorr : corr = E * pw) (hpw0 : 0 ≤ pw) (hpw : pw ≤ u / 8192)
    (hh2 : hi' ≤ hi + corr + 2 * |hi + corr| * (u / 256)) :
    hi' - lo ≤ 2 * Dy + (Real.exp yv + |Real.exp yv - 1|) * u := by
  have hEy := Real.exp_pos yv
  have hDy0 : 0 ≤ Dy := by linarith
  have hhi1 : 0 < hi + 1 := by linarith
  rw [abs_of_pos hhi1] at hE2
  have hE3 : E ≤ 2 * (hi + 1) := by nlinarith
  have hhi2 : hi + 1 ≤ Real.exp yv + Dy := by linarith
  have hcorr2 : corr ≤ 2 * (Real.exp yv + Dy) * (u / 8192) := by
    rw [hcorr]
    calc E * pw ≤ 2 * (hi + 1) * (u / 8192) := mul_le_mul hE3 hpw hpw0 (by linarith)
      _ ≤ 2 * (Real.exp yv + Dy) * (u / 8192) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
  have hcorr0 : 0 ≤ corr := by rw [hcorr]; exact mul_nonneg (by linarith) hpw0
  have hhiabs : |hi| ≤ |Real.exp yv - 1| + Dy :=
    abs_le.mpr ⟨by linarith [neg_abs_le (Real.exp yv - 1)],
      by linarith [le_abs_self (Real.exp yv - 1)]⟩
  have habs : |hi + corr| ≤ |Real.exp yv - 1| + Dy + corr := by
    calc |hi + corr| ≤ |hi| + |corr| := abs_add_le _ _
      _ ≤ |Real.exp yv - 1| + Dy + corr := by rw [abs_of_nonneg hcorr0]; linarith
  have h3 : 2 * |hi + corr| * (u / 256) ≤ 2 * (|Real.exp yv - 1| + Dy + corr) * (u / 256) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h4 : Dy * u ≤ Dy := mul_le_of_le_one_right hDy0 hu1
  have h5 : corr * u ≤ corr := mul_le_of_le_one_right hcorr0 hu1
  have h6 : 0 ≤ |Real.exp yv - 1| * u := by positivity
  nlinarith

/-- `expM1Eps` at `y ≤ q` with `|y| ≤ 2|q|` is bounded in terms of `q`. -/
theorem expM1Eps_le {yv qv : ℝ} (hle : yv ≤ qv) (hy : |yv| ≤ 2 * |qv|)
    (c w : ℕ) :
    expM1Eps yv c w ≤ (2 * Real.exp qv * (80 * ((w : ℝ) + c + 9)) + |Real.exp qv - 1|
      + Real.exp qv + 4 * |qv|) * (1 / 2 : ℝ) ^ w := by
  unfold expM1Eps
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h1 : Real.exp yv ≤ Real.exp qv := Real.exp_le_exp.mpr hle
  have h2 : |Real.exp yv - 1| ≤ |Real.exp qv - 1| + Real.exp qv := by
    calc |Real.exp yv - 1| = |(Real.exp qv - 1) - (Real.exp qv - Real.exp yv)| := by ring_nf
      _ ≤ |Real.exp qv - 1| + |Real.exp qv - Real.exp yv| := abs_sub _ _
      _ ≤ |Real.exp qv - 1| + Real.exp qv := by
        rw [abs_of_nonneg (by linarith : 0 ≤ Real.exp qv - Real.exp yv)]; linarith [Real.exp_pos yv]
  have h3 : 2 * Real.exp yv * (80 * ((w : ℝ) + c + 9))
      ≤ 2 * Real.exp qv * (80 * ((w : ℝ) + c + 9)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- The width bound of `expM1RatBracket`. -/
noncomputable def expM1RatEps (qv : ℝ) (c w : ℕ) : ℝ :=
  3 * ((2 * Real.exp qv * (80 * ((w : ℝ) + c + 9)) + |Real.exp qv - 1| + Real.exp qv + 4 * |qv|)
    * (1 / 2 : ℝ) ^ w)

theorem tendsto_expM1RatEps (qv : ℝ) (c : ℕ) :
    Filter.Tendsto (expM1RatEps qv c) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1
    (by norm_num : |(1 / 2 : ℝ)| < 1)).const_mul
    (3 * (2 * Real.exp qv * 160 + |Real.exp qv - 1| + Real.exp qv + 4 * |qv|))
  rw [mul_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · exact Filter.Eventually.of_forall fun w => by unfold expM1RatEps; positivity
  · refine Filter.eventually_atTop.mpr ⟨c + 9, fun w hw => ?_⟩
    unfold expM1RatEps
    have hw1 : (c : ℝ) + 9 ≤ w := by exact_mod_cast hw
    have hw0 : (1 : ℝ) ≤ w := by linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
    have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    have hE := (Real.exp_pos qv).le
    have h1 : 2 * Real.exp qv * (80 * ((w : ℝ) + c + 9)) ≤ 2 * Real.exp qv * 160 * w := by
      have : 80 * ((w : ℝ) + c + 9) ≤ 160 * w := by linarith
      nlinarith
    have h2 : |Real.exp qv - 1| ≤ |Real.exp qv - 1| * w :=
      le_mul_of_one_le_right (abs_nonneg _) hw0
    have h3 : Real.exp qv ≤ Real.exp qv * w := le_mul_of_one_le_right hE hw0
    have h4 : 4 * |qv| ≤ 4 * |qv| * w := le_mul_of_one_le_right (by positivity) hw0
    rw [pow_one]
    have h5 : (2 * Real.exp qv * (80 * ((w : ℝ) + c + 9)) + |Real.exp qv - 1| + Real.exp qv
        + 4 * |qv|)
        ≤ (2 * Real.exp qv * 160 + |Real.exp qv - 1| + Real.exp qv + 4 * |qv|) * w := by
      linarith
    have := mul_le_mul_of_nonneg_right h5 hu
    linarith

/-- `expM1RatBracket q w` encloses `exp q − 1` for `q ≠ 0`, with width at most
`expM1RatEps q (expM1Comp (ofInt (⌊log₂ |q|⌋ + 2))) w`. -/
theorem expM1RatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    ∃ lo hi : ℝ, (expM1RatBracket q w).1.toVal = some (lo : EReal) ∧
      (expM1RatBracket q w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.exp (AzRat.toRat q : ℝ) - 1 ∧ Real.exp (AzRat.toRat q : ℝ) - 1 ≤ hi ∧
      hi - lo ≤ expM1RatEps (AzRat.toRat q : ℝ)
        (expM1Comp (AzInt.ofInt (AzRat.floorLogBaseAbs 2 q + 2))) w := by
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = w + 16 + q.num.size := ⟨_, rfl⟩
  have : NeZero W := ⟨by omega⟩
  have : NeZero (w + 8) := ⟨by omega⟩
  obtain ⟨e, he⟩ : ∃ e : AzInt, e = AzInt.ofInt (AzRat.floorLogBaseAbs 2 q + 2) := ⟨_, rfl⟩
  simp only [expM1RatBracket]
  rw [← hW, ← he]
  obtain ⟨qv, hqv⟩ : ∃ qv : ℝ, qv = (AzRat.toRat q : ℝ) := ⟨_, rfl⟩
  rw [← hqv]
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = Int.log 2 |qv| := ⟨_, rfl⟩
  have heL : e.toInt = L + 2 := by
    rw [he, AzInt.toInt_ofInt, AzRat.floorLogBaseAbs_eq 2 (by decide) q h0, hL, hqv]; rfl
  have hq0 : qv ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp (by rw [← hqv]; exact h))
  have hqpos : 0 < |qv| := abs_pos.mpr hq0
  have h2L : (2 : ℝ) ^ L ≤ |qv| := by
    rw [hL]; exact_mod_cast Int.zpow_log_le_self (by norm_num : 1 < 2) hqpos
  have hqL : |qv| < (2 : ℝ) ^ (L + 1) := by
    rw [hL]; exact_mod_cast Int.lt_zpow_succ_log_self (by norm_num : 1 < 2) |qv|
  have hqs : |qv| < (2 : ℝ) ^ (q.num.size : ℤ) := by
    have h := abs_toRat_lt q
    rw [← hqv] at h
    exact h
  have hLs : L ≤ (q.num.size : ℤ) - 1 := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ^ (q.num.size : ℤ) ≤ (2 : ℝ) ^ L := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  -- the float `y`
  obtain ⟨y, hy, hy1, hy2⟩ := ofAzRatRound_floor_abs q W
  rw [← hqv] at hy1 hy2
  generalize (ofAzRatRound q W .Floor).1 = Y at hy
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hus : u ≤ 1 / 10 ^ 18 := hu ▸ half_pow_small hw
  have hu1 : u ≤ 1 := by linarith
  have hs0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ q.num.size := by positivity
  have hs1 : (2 : ℝ) ^ q.num.size * (1 / 2 : ℝ) ^ q.num.size = 1 := by
    rw [one_div_pow, mul_one_div, div_self (by positivity)]
  have hqs1 : |qv| * (1 / 2 : ℝ) ^ q.num.size ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (zpow_natCast (2 : ℝ) q.num.size ▸ hqs).le hs0
    rw [hs1] at h
    exact h
  have hWu : (1 / 2 : ℝ) ^ W = u * (1 / 65536) * (1 / 2 : ℝ) ^ q.num.size := by
    rw [hW, pow_add, pow_add, hu, show ((1 : ℝ) / 2) ^ 16 = 1 / 65536 by norm_num]
  have hd : qv - y ≤ u / 32768 := by
    have e1 : 2 * |qv| * (1 / 2 : ℝ) ^ W = u / 32768 * (|qv| * (1 / 2 : ℝ) ^ q.num.size) := by
      rw [hWu]; ring
    have e2 : u / 32768 * (|qv| * (1 / 2 : ℝ) ^ q.num.size) ≤ u / 32768 * 1 :=
      mul_le_mul_of_nonneg_left hqs1 (by positivity)
    linarith
  have hd0 : 0 ≤ qv - y := by linarith
  have hdq : qv - y ≤ |qv| := by
    have hW12 : (1 / 2 : ℝ) ^ W ≤ 1 / 2 := by
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (by omega : 1 ≤ W)
      rwa [pow_one] at this
    have := mul_le_mul_of_nonneg_left hW12 (by positivity : (0 : ℝ) ≤ 2 * |qv|)
    linarith
  have hy2q : |y| ≤ 2 * |qv| := by
    calc |y| = |qv - (qv - y)| := by ring_nf
      _ ≤ |qv| + |qv - y| := abs_sub _ _
      _ ≤ 2 * |qv| := by rw [abs_of_nonneg hd0]; linarith
  have hye : |y| < (2 : ℝ) ^ e.toInt := by
    rw [heL]
    calc |y| ≤ 2 * |qv| := hy2q
      _ < 2 * (2 : ℝ) ^ (L + 1) := by linarith
      _ = (2 : ℝ) ^ (L + 2) := by
        rw [zpow_add₀ (by norm_num) L 2, zpow_add₀ (by norm_num) L 1]; ring
  -- the bracket at `y`
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expM1Bracket_spec hy e hye hw
  have hDy := expM1Eps_le hy1 hy2q (expM1Comp e) w
  rw [← hu] at hDy
  -- the correction
  obtain ⟨E, hE, hE1, hE2⟩ := addCeiling_abs hhi toVal_one' (w + 8)
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = u / 256 := by
    rw [pow_add, hu, show ((1 : ℝ) / 2) ^ 8 = 1 / 256 by norm_num]; ring
  rw [h8] at hE2
  have hsh := toVal_shiftLeft_of_toVal hE (e - (AzNat.ofNat (W - 2)).toAzInt)
  obtain ⟨pw, hpw⟩ : ∃ pw : ℝ, pw = (2 : ℝ) ^ (e - (AzNat.ofNat (W - 2)).toAzInt).toInt :=
    ⟨_, rfl⟩
  rw [← hpw] at hsh
  have hexp : (e - (AzNat.ofNat (W - 2)).toAzInt).toInt = L + 4 - W := by
    rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat, heL, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hpw0 : 0 ≤ pw := by rw [hpw]; positivity
  have hpwu : pw ≤ u / 8192 := by
    have e1 : (2 : ℝ) ^ (-((w + 13 : ℕ) : ℤ)) = u / 8192 := by
      rw [zpow_neg, zpow_natCast, ← one_div, ← one_div_pow, pow_add, hu,
        show ((1 : ℝ) / 2) ^ 13 = 1 / 8192 by norm_num]
      ring
    rw [hpw, hexp, ← e1]
    exact zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
  have hpw1 : 2 * (qv - y) * Real.exp y ≤ pw * Real.exp y := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos y).le
    have e1 : 4 * (2 : ℝ) ^ (L + 1) * (1 / 2 : ℝ) ^ W ≤ pw := by
      rw [hpw, hexp, one_div_pow, one_div, ← zpow_natCast, ← zpow_neg,
        show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num, ← zpow_add₀ (by norm_num),
        ← zpow_add₀ (by norm_num)]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have e2 : 2 * (qv - y) ≤ 4 * |qv| * (1 / 2 : ℝ) ^ W := by linarith
    have e3 : 4 * |qv| * (1 / 2 : ℝ) ^ W ≤ 4 * (2 : ℝ) ^ (L + 1) * (1 / 2 : ℝ) ^ W :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  obtain ⟨hi', hhi', hh1, hh2⟩ := addCeiling_abs hhi hsh (w + 8)
  rw [h8] at hh2
  refine ⟨lo, hi', hlo, hhi', h1.trans (by linarith [Real.exp_le_exp.mpr hy1]), ?_, ?_⟩
  · -- `exp q − 1 ≤ hi'`
    have e1 : Real.exp qv ≤ Real.exp y * (1 + 2 * (qv - y)) :=
      exp_le_exp_mul_one_add hy1 (by linarith)
    have e2 : pw * Real.exp y ≤ E * pw := by
      have : Real.exp y ≤ E := by linarith [Real.exp_pos y]
      nlinarith
    linarith
  · have hw' := expM1Rat_width hu0 hu1 h1 h2 h3 (by linarith) hE2 rfl hpw0 hpwu hh2
    unfold expM1RatEps
    rw [← hu]
    have hEq : Real.exp y ≤ Real.exp qv := Real.exp_le_exp.mpr hy1
    have hab : |Real.exp y - 1| ≤ |Real.exp qv - 1| + Real.exp qv := by
      calc |Real.exp y - 1| = |(Real.exp qv - 1) - (Real.exp qv - Real.exp y)| := by ring_nf
        _ ≤ |Real.exp qv - 1| + |Real.exp qv - Real.exp y| := abs_sub _ _
        _ ≤ |Real.exp qv - 1| + Real.exp qv := by
          rw [abs_of_nonneg (by linarith : 0 ≤ Real.exp qv - Real.exp y)]; linarith [Real.exp_pos y]
    have h5 : (Real.exp y + |Real.exp y - 1|) * u ≤ (|Real.exp qv - 1| + 2 * Real.exp qv) * u :=
      mul_le_mul_of_nonneg_right (by linarith) hu0.le
    have h6 : 0 ≤ (2 * Real.exp qv * (80 * ((w : ℝ) + expM1Comp e + 9)) + 4 * |qv|) * u := by
      positivity
    nlinarith

/-- `exp q − 1` is irrational for a rational `q ≠ 0`. -/
theorem irrational_exp_sub_one_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.exp (AzRat.toRat q : ℝ) - 1) := by
  have h := (irrational_exp_toRat q h0).sub_intCast 1
  rwa [Int.cast_one] at h

/-- `expM1RatApprox` is a strict enclosure of `exp q − 1` with width at most `expM1RatEps`. -/
theorem expM1RatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    ∃ lv hv : ℝ, Rounds (expM1RatApprox q w).1 lv ∧ Rounds (expM1RatApprox q w).2 hv ∧
      lv < Real.exp (AzRat.toRat q : ℝ) - 1 ∧ Real.exp (AzRat.toRat q : ℝ) - 1 < hv ∧
      hv - lv ≤ expM1RatEps (AzRat.toRat q : ℝ)
        (expM1Comp (AzInt.ofInt (AzRat.floorLogBaseAbs 2 q + 2))) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expM1RatBracket_spec hw q h0
  have hirr := irrational_exp_sub_one_toRat q h0
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, h3⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlo
    exact lt_of_le_of_ne h1 (by rw [hr]; exact (hirr.ne_rat r).symm)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhi
    exact lt_of_le_of_ne h2 (by rw [hr]; exact hirr.ne_rat r)

/-- The Ziv certificate for `exp q − 1`. -/
theorem expM1RatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (expM1RatApprox q (w₀ * 2 ^ f)).1
      (expM1RatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (expM1RatApprox q)
    (irrational_exp_sub_one_toRat q h0)
    (expM1RatEps (AzRat.toRat q : ℝ) (expM1Comp (AzInt.ofInt (AzRat.floorLogBaseAbs 2 q + 2))))
    (tendsto_expM1RatEps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := expM1RatApprox_spec hw q h0
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-- `expOfBracket X w` encloses `exp v` for a bracket `X = [lo, hi]` of `v` with `hi − lo ≤ 1`,
strictly from below when `lo < v`. -/
theorem expOfBracket_spec {X : AzFloat × AzFloat} {lo hi v : ℝ}
    (hlo : X.1.toVal = some (lo : EReal)) (hhi : X.2.toVal = some (hi : EReal)) (h1 : lo < v)
    (h2 : v ≤ hi) (hw1 : hi - lo ≤ 1) {w : ℕ} (hw : 64 ≤ w) :
    ∃ a b : ℝ, (expOfBracket X w).1.toVal = some (a : EReal) ∧
      (expOfBracket X w).2.toVal = some (b : EReal) ∧ a < Real.exp v ∧ Real.exp v ≤ b := by
  have : NeZero (w + 8) := ⟨by omega⟩
  obtain ⟨a, b, ha, hb, ha1, hb1, -⟩ := expBracketAt_spec hlo hw
  simp only [expOfBracket]
  obtain ⟨dv, hd, hd1, -⟩ := subCeiling_abs hhi hlo (w + 8)
  have hd0 : 0 ≤ dv := by linarith
  have h2d : ((subPrecRound X.2 X.1 (w + 8) .Ceiling).1 <<< AzInt.ofInt 1).toVal
      = some ((2 * dv : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hd (AzInt.ofInt 1)
    rw [AzInt.toInt_ofInt, zpow_one, mul_comm] at h
    exact h
  have hb0 : 0 < b := lt_of_lt_of_le (Real.exp_pos lo) hb1
  obtain ⟨corr, hcorr, hc⟩ := mulCeiling_err hb h2d (w + 8) (by positivity)
  have hbd : 0 ≤ b * (2 * dv) := by positivity
  obtain ⟨hi', hhi', hh⟩ := addCeiling_err hb hcorr (w + 8) (by linarith [hc.ge])
  refine ⟨a, hi', ha, hhi', lt_of_le_of_lt ha1 (Real.exp_lt_exp.mpr h1), ?_⟩
  have e1 : Real.exp v ≤ Real.exp lo * (1 + 2 * (v - lo)) :=
    exp_le_exp_mul_one_add h1.le (by linarith)
  have e2 : Real.exp lo * (1 + 2 * (v - lo)) ≤ b * (1 + 2 * dv) :=
    mul_le_mul hb1 (by linarith) (by linarith) hb0.le
  have e3 := hc.ge
  have e4 := hh.ge
  nlinarith


/-- The width bound of `expOfBracket` at a bracket of width `δ`. -/
noncomputable def expOfBracketEps (v δ : ℝ) (w : ℕ) : ℝ :=
  expEps v w + Real.exp v * (24 * δ + (1 / 2 : ℝ) ^ w / 4)

/-- `expOfBracket X w` encloses `exp v` for a bracket `X = [lo, hi]` of `v` with `hi − lo ≤ 1`,
with width at most `expOfBracketEps v (hi − lo) w`. -/
theorem expOfBracket_spec_width {X : AzFloat × AzFloat} {lo hi v : ℝ}
    (hlo : X.1.toVal = some (lo : EReal)) (hhi : X.2.toVal = some (hi : EReal)) (h1 : lo ≤ v)
    (h2 : v ≤ hi) (hw1 : hi - lo ≤ 1) {w : ℕ} (hw : 64 ≤ w) :
    ∃ a b : ℝ, (expOfBracket X w).1.toVal = some (a : EReal) ∧
      (expOfBracket X w).2.toVal = some (b : EReal) ∧ a ≤ Real.exp v ∧ Real.exp v ≤ b ∧
      b - a ≤ expOfBracketEps v (hi - lo) w := by
  have : NeZero (w + 8) := ⟨by omega⟩
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expBracketAt_spec hlo hw
  simp only [expOfBracket]
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hus : u ≤ 1 / 10 ^ 18 := hu ▸ half_pow_small hw
  have hu1 : u ≤ 1 := by linarith
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = u / 256 := by
    rw [pow_add, hu, show ((1 : ℝ) / 2) ^ 8 = 1 / 256 by norm_num]; ring
  obtain ⟨dv, hd, hd1, hd2⟩ := subCeiling_abs hhi hlo (w + 8)
  have hd0 : 0 ≤ dv := by linarith
  rw [abs_of_nonneg (by linarith : 0 ≤ hi - lo), h8] at hd2
  have hdv : dv ≤ 2 * (hi - lo) := by nlinarith
  have h2d : ((subPrecRound X.2 X.1 (w + 8) .Ceiling).1 <<< AzInt.ofInt 1).toVal
      = some ((2 * dv : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hd (AzInt.ofInt 1)
    rw [AzInt.toInt_ofInt, zpow_one, mul_comm] at h
    exact h
  have hElo := Real.exp_pos lo
  have hb0 : 0 < b := lt_of_lt_of_le hElo hb1
  obtain ⟨corr, hcorr, hc⟩ := mulCeiling_err hb h2d (w + 8) (by positivity)
  have hbd : 0 ≤ b * (2 * dv) := by positivity
  have hc1 := hc.ge
  have hc2 := hc.le
  rw [h8] at hc2
  obtain ⟨hi', hhi', hh⟩ := addCeiling_err hb hcorr (w + 8) (by linarith)
  have hh1 := hh.ge
  have hh2 := hh.le
  rw [h8] at hh2
  refine ⟨a, hi', ha, hhi', ha1.trans (Real.exp_le_exp.mpr h1), ?_, ?_⟩
  · have e1 : Real.exp v ≤ Real.exp lo * (1 + 2 * (v - lo)) :=
      exp_le_exp_mul_one_add h1 (by linarith)
    have e2 : Real.exp lo * (1 + 2 * (v - lo)) ≤ b * (1 + 2 * dv) :=
      mul_le_mul hb1 (by linarith) (by linarith) hb0.le
    nlinarith
  · -- `b ≤ 3 exp lo`, `corr ≤ 8 (hi − lo) b`, `hi' ≤ b + corr + (b + corr) u/128`
    have hf := forty_mul_half_pow_le hw
    rw [← hu] at hf
    unfold expEps at hab
    rw [← hu] at hab
    have hb3 : b ≤ 3 * Real.exp lo := by
      have : Real.exp lo * (80 * ((w : ℝ) + 9)) * u ≤ Real.exp lo * 2 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) hElo.le
      linarith
    have hcorr2 : corr ≤ 8 * (hi - lo) * b := by
      have h3 : b * (2 * dv) ≤ b * (4 * (hi - lo)) := mul_le_mul_of_nonneg_left (by linarith) hb0.le
      have h4 : 2 * (b * (2 * dv)) * (u / 256) ≤ 2 * (b * (4 * (hi - lo))) * (u / 256) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith
    have hcorr0 : 0 ≤ corr := by linarith
    have hhi3 : hi' ≤ b + corr + (b + corr) * (u / 128) := by linarith
    have hEv : Real.exp lo ≤ Real.exp v := Real.exp_le_exp.mpr h1
    unfold expOfBracketEps expEps
    rw [← hu]
    have hmono : Real.exp lo * (80 * ((w : ℝ) + 9)) * u ≤ Real.exp v * (80 * ((w : ℝ) + 9)) * u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEv (by positivity)) hu0.le
    have hδ0 : 0 ≤ hi - lo := by linarith
    have hcu : corr * u ≤ corr := mul_le_of_le_one_right hcorr0 hu1
    have hbu : b * u ≤ 3 * Real.exp lo * u := mul_le_mul_of_nonneg_right hb3 hu0.le
    have hcl : corr ≤ 24 * (hi - lo) * Real.exp lo := by
      have := mul_le_mul_of_nonneg_left hb3 (by positivity : (0 : ℝ) ≤ 8 * (hi - lo))
      linarith
    have hEvδ : (hi - lo) * Real.exp lo ≤ (hi - lo) * Real.exp v :=
      mul_le_mul_of_nonneg_left hEv hδ0
    have hEvu : Real.exp lo * u ≤ Real.exp v * u := mul_le_mul_of_nonneg_right hEv hu0.le
    nlinarith

end Azurite.AzFloat
