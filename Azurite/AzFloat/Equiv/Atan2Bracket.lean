/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.Equiv.AtanRatBracket
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Equivalence: the bracket of `atan2 (y, x)`

* Real analysis: `arg_of_re_pos` (`arg z = arctan (im/re)` for `re > 0`), `atan2Abs`
  (`atan2 (a, ±b)` for `a, b > 0`), `arg_eq_atan2Abs` (`arg (x + iy) = ± atan2Abs |y| |x|`),
  `irrational_arg_of_rat` (the angle of a rational point off the axes is irrational).
* `enclApprox_spec`, `piShiftEncl_spec`, `atanQuot_spec`, `atanQuotRel_spec`,
  `atan2Bracket_spec` (width at most `2^(−w)`), `atan2Approx_spec`,
  `atan2Approx_isSome_exists` (the Ziv certificate), `piThreeQuartersApprox_spec`,
  `piThreeQuartersApprox_isSome_exists`.
-/

open Real

namespace Azurite.AzFloat

/-! ### Real analysis -/

/-- `arg z = arctan (im z / re z)` in the right half-plane. -/
theorem arg_of_re_pos {z : ℂ} (h : 0 < z.re) : Complex.arg z = arctan (z.im / z.re) := by
  have habs := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h))
  rw [← Complex.tan_arg, arctan_tan habs.1 habs.2]

/-- `atan2 (a, b)` (`xpos`) or `atan2 (a, −b)` for `a, b > 0`. -/
noncomputable def atan2Abs (a b : ℝ) (xpos : Bool) : ℝ :=
  if xpos then arctan (a / b) else π - arctan (a / b)

/-- The angle of `(x, y)` off the axes: `± atan2Abs |y| |x|` with the sign of `y`. -/
theorem arg_eq_atan2Abs {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) {neg xpos : Bool}
    (hneg : neg = true ↔ y < 0) (hxpos : xpos = true ↔ 0 < x) :
    Complex.arg ⟨x, y⟩ = (if neg then -1 else 1) * atan2Abs |y| |x| xpos := by
  unfold atan2Abs
  rcases lt_or_gt_of_ne hx with hx' | hx'
  · have hxp : xpos = false := by
      cases xpos
      · rfl
      · exact absurd (hxpos.mp rfl) (not_lt.mpr hx'.le)
    rw [hxp, abs_of_neg hx']
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases lt_or_gt_of_ne hy with hy' | hy'
    · rw [hneg.mpr hy', abs_of_neg hy']
      simp only [↓reduceIte]
      have h1 := Complex.arg_neg_eq_arg_add_pi_of_im_neg (x := (⟨x, y⟩ : ℂ)) hy'
      have h2 := arg_of_re_pos (z := -(⟨x, y⟩ : ℂ)) (by simpa using hx')
      rw [Complex.neg_re, Complex.neg_im] at h2
      linarith
    · have hn : neg = false := by
        cases neg
        · rfl
        · exact absurd (hneg.mp rfl) (not_lt.mpr hy'.le)
      rw [hn, abs_of_pos hy']
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      have h1 := Complex.arg_neg_eq_arg_sub_pi_of_im_pos (x := (⟨x, y⟩ : ℂ)) hy'
      have h2 := arg_of_re_pos (z := -(⟨x, y⟩ : ℂ)) (by simpa using hx')
      rw [Complex.neg_re, Complex.neg_im, neg_div_neg_eq] at h2
      have h3 : arctan (y / -x) = -arctan (y / x) := by rw [div_neg, arctan_neg]
      linarith
  · rw [hxpos.mpr hx', abs_of_pos hx']
    simp only [↓reduceIte]
    have h2 := arg_of_re_pos (z := (⟨x, y⟩ : ℂ)) hx'
    rcases lt_or_gt_of_ne hy with hy' | hy'
    · rw [hneg.mpr hy', abs_of_neg hy']
      simp only [↓reduceIte]
      rw [h2, neg_div, arctan_neg]
      ring
    · have hn : neg = false := by
        cases neg
        · rfl
        · exact absurd (hneg.mp rfl) (not_lt.mpr hy'.le)
      rw [hn, abs_of_pos hy']
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      exact h2

/-- The angle of a rational point off the axes is irrational. -/
theorem irrational_arg_of_rat {x y : ℚ} (hy : y ≠ 0) :
    Irrational (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero] at hr
    have h0 : ((y : ℚ) : ℝ) = 0 := (Complex.arg_eq_zero_iff.mp hr.symm).2
    exact hy (by exact_mod_cast h0)
  apply irrational_tan_rat hr0
  rw [hr, Complex.tan_arg]
  exact ⟨y / x, by push_cast; rfl⟩

/-! ### The enclosures -/

/-- The ends of an enclosure, negated and swapped on demand, as `Roundable`s around `± v`. -/
theorem enclApprox_spec (neg : Bool) {b : Encl} {lo hi v : ℝ} (hlo : b.1.toVal = some (lo : EReal))
    (hhi : b.2.toVal = some (hi : EReal)) (h1 : lo ≤ v) (h2 : v ≤ hi) :
    ∃ lv hv : ℝ, Rounds (enclApprox neg b).1 lv ∧ Rounds (enclApprox neg b).2 hv ∧
      lv ≤ (if neg then -1 else 1) * v ∧ (if neg then -1 else 1) * v ≤ hv ∧
      hv - lv = hi - lo := by
  simp only [enclApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    exact ⟨lo, hi, hR1, hR2, h1, h2, rfl⟩
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    have hnlo : (-b.2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-b.1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by ring⟩

/-- **`π ± A` and `π/2 ± A`**: for an enclosure `A` of `α` with ends in `[0, 4]` and width `δ`,
an enclosure of width at most `δ + 44·2^(−V)`. -/
theorem piShiftEncl_spec (half plus : Bool) {A : Encl} {al ah α δ : ℝ}
    (hal : A.1.toVal = some (al : EReal)) (hah : A.2.toVal = some (ah : EReal)) (hal0 : 0 ≤ al)
    (h1 : al ≤ α) (h2 : α ≤ ah) (hah4 : ah ≤ 4) (hw : ah - al ≤ δ) {V : ℕ} (hV : 64 ≤ V) :
    ∃ lo hi : ℝ, (piShiftEncl half plus A V).1.toVal = some (lo : EReal) ∧
      (piShiftEncl half plus A V).2.toVal = some (hi : EReal) ∧
      lo ≤ (if half then π / 2 else π) + (if plus then α else -α) ∧
      (if half then π / 2 else π) + (if plus then α else -α) ≤ hi ∧
      hi - lo ≤ δ + 44 * (1 / 2 : ℝ) ^ V := by
  have : NeZero V := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ V with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 16 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (by omega : 4 ≤ V)
    rw [← hu] at this
    norm_num at this
    linarith
  have hπ := pi_lt_four
  have hπ3 := pi_gt_three
  obtain ⟨pl, ph, hpl, hph, hpl0, hpl1, hph1, hpw⟩ := piBracket_spec_width hV
  rw [← hu] at hpw
  have key : ∃ ql qh : ℝ,
      (if half = true then (piBracket V).1 <<< AzInt.ofInt (-1) else (piBracket V).1).toVal
        = some (ql : EReal) ∧
      (if half = true then (piBracket V).2 <<< AzInt.ofInt (-1) else (piBracket V).2).toVal
        = some (qh : EReal) ∧ 0 ≤ ql ∧ ql ≤ (if half then π / 2 else π) ∧
      (if half then π / 2 else π) ≤ qh ∧ qh - ql ≤ 8 * u ∧ qh ≤ 5 := by
    cases half with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨pl, ph, hpl, hph, hpl0, hpl1.le, hph1, hpw, by linarith⟩
    | true =>
      simp only [↓reduceIte]
      have hpl' : ((piBracket V).1 <<< AzInt.ofInt (-1)).toVal
          = some ((pl / 2 : ℝ) : EReal) := by
        have h := toVal_shiftLeft_of_toVal hpl (AzInt.ofInt (-1))
        rw [h, AzInt.toInt_ofInt, zpow_neg_one, div_eq_mul_inv]
      have hph' : ((piBracket V).2 <<< AzInt.ofInt (-1)).toVal
          = some ((ph / 2 : ℝ) : EReal) := by
        have h := toVal_shiftLeft_of_toVal hph (AzInt.ofInt (-1))
        rw [h, AzInt.toInt_ofInt, zpow_neg_one, div_eq_mul_inv]
      exact ⟨pl / 2, ph / 2, hpl', hph', by linarith, by linarith, by linarith, by linarith,
        by linarith⟩
  obtain ⟨ql, qh, hql, hqh, hq0, hq1, hq2, hqw, hq5⟩ := key
  unfold piShiftEncl
  dsimp only
  cases plus with
  | true =>
    simp only [↓reduceIte]
    obtain ⟨lo, hlo, hlo1, hlo2⟩ := addFloor_abs hql hal V
    obtain ⟨hi, hhi, hhi1, hhi2⟩ := addCeiling_abs hqh hah V
    rw [← hu] at hlo2 hhi2
    have ha1 : |ql + al| ≤ 9 := by
      rw [abs_le]
      constructor <;> linarith
    have ha2 : |qh + ah| ≤ 9 := by
      rw [abs_le]
      constructor <;> linarith
    have m1 := mul_le_mul_of_nonneg_right ha1 hu0
    have m2 := mul_le_mul_of_nonneg_right ha2 hu0
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hql hah V
    obtain ⟨hi, hhi, hhi1, hhi2⟩ := subCeiling_abs hqh hal V
    rw [← hu] at hlo2 hhi2
    have ha1 : |ql - ah| ≤ 9 := by
      rw [abs_le]
      constructor <;> linarith
    have ha2 : |qh - al| ≤ 9 := by
      rw [abs_le]
      constructor <;> linarith
    have m1 := mul_le_mul_of_nonneg_right ha1 hu0
    have m2 := mul_le_mul_of_nonneg_right ha2 hu0
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩

/-- The two rounded quotients of floats `0 < n ≤ d` at `V` bits. -/
theorem divPrecRound_unit {n d : AzFloat} {nv dv : ℝ} (hn : n.toVal = some (nv : EReal))
    (hd : d.toVal = some (dv : EReal)) (hn0 : 0 < nv) (hnd : nv ≤ dv) (V : ℕ) [NeZero V] :
    ∃ lv hv : ℝ, (divPrecRound n d V .Floor).1.toVal = some (lv : EReal) ∧
      (divPrecRound n d V .Ceiling).1.toVal = some (hv : EReal) ∧ 0 ≤ lv ∧ lv ≤ nv / dv ∧
      nv / dv ≤ hv ∧ hv - lv ≤ 4 * (1 / 2 : ℝ) ^ V := by
  have hd0 : 0 < dv := lt_of_lt_of_le hn0 hnd
  obtain ⟨lv, hlv, hl0, hl1, hl2⟩ := divFloor_err hn hd hd0 hn0.le V
  obtain ⟨hv, hhv, hh1, hh2⟩ := divCeiling_err hn hd hd0 hn0.le V
  have hr1 : nv / dv ≤ 1 := (div_le_one hd0).mpr hnd
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
  have hru : nv / dv * (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ V := mul_le_of_le_one_left hu0 hr1
  exact ⟨lv, hv, hlv, hhv, hl0, hl1, hh1, by linarith⟩

/-- **`arctan (n/d)`** for floats `0 < n ≤ d`: nonnegative lower end, upper end at most `4`,
width at most `(3/4) 2^(−K) + 14·2^(−K−64)`. -/
theorem atanQuot_spec {n d : AzFloat} {nv dv : ℝ} (hn : n.toVal = some (nv : EReal))
    (hd : d.toVal = some (dv : EReal)) (hn0 : 0 < nv) (hnd : nv ≤ dv) (K : ℕ) :
    ∃ lo hi : ℝ, (atanQuot n d K).1.toVal = some (lo : EReal) ∧
      (atanQuot n d K).2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ arctan (nv / dv) ∧
      arctan (nv / dv) ≤ hi ∧ hi ≤ 4 ∧
      hi - lo ≤ 3 / 4 * (1 / 2 : ℝ) ^ K + 14 * (1 / 2 : ℝ) ^ (K + 64) := by
  have : NeZero (K + 64) := ⟨by omega⟩
  have hd0 : 0 < dv := lt_of_lt_of_le hn0 hnd
  obtain ⟨lv, hv, hlv, hhv, hl0, hl1, hh1, hdw⟩ := divPrecRound_unit hn hd hn0 hnd (K + 64)
  exact atanWiden_spec hlv hhv hl0 hl1 hh1 ((div_le_one hd0).mpr hnd) K hdw

/-- **`arctan (n/d)` with relative accuracy** for floats `0 < n ≤ d`, `n/d < 2^e`: width at
most `2^(−w)`, nonnegative lower end. -/
theorem atanQuotRel_spec {n d : AzFloat} {nv dv : ℝ} (hn : n.toVal = some (nv : EReal))
    (hd : d.toVal = some (dv : EReal)) (hn0 : 0 < nv) (hnd : nv ≤ dv) {e : AzInt}
    (hlt : nv / dv < (2 : ℝ) ^ e.toInt) (w : ℕ) :
    ∃ lo hi : ℝ, (atanQuotRel n d e w).1.toVal = some (lo : EReal) ∧
      (atanQuotRel n d e w).2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ arctan (nv / dv) ∧
      arctan (nv / dv) ≤ hi ∧ hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  have hd0 : 0 < dv := lt_of_lt_of_le hn0 hnd
  set a := nv / dv with ha
  have ha0 : 0 < a := div_pos hn0 hd0
  have ha1 : a ≤ 1 := (div_le_one hd0).mpr hnd
  have hat0 : 0 ≤ arctan a := arctan_nonneg.mpr ha0.le
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  unfold atanQuotRel
  split_ifs with hc
  · obtain ⟨hs, hn'⟩ := hc
    dsimp only
    have : NeZero (w + 64) := ⟨by omega⟩
    set m := e.abs.toNat with hmdef
    set t := (2 : ℝ) ^ e.toInt with ht
    have ht0 : 0 < t := by positivity
    have htn : t = (1 / 2 : ℝ) ^ m := by
      rw [ht, htoInt, hs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    have ht1 : t ≤ 1 := by
      rw [htn]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    set tt := t * t with htt
    have htt0 : 0 ≤ tt := by positivity
    have htt1 : tt ≤ 1 := by
      rw [htt]
      nlinarith
    have httw : tt ≤ (1 / 2 : ℝ) ^ (w + 8) := by
      rw [htt, htn, ← pow_add]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    obtain ⟨lv, hv, hlv, hhv, hl0, hl1, hh1, hdw⟩ := divPrecRound_unit hn hd hn0 hnd (w + 64)
    rw [← ha] at hl1 hh1
    have hsh : (((divPrecRound n d (w + 64) .Floor).1 <<< e) <<< e).toVal
        = some ((lv * tt : ℝ) : EReal) := by
      have h := toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal hlv e) e
      rw [h, htt, mul_assoc]
    obtain ⟨r, hr, hr1, hr2⟩ := subFloor_abs hlv hsh (w + 64)
    obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hr
    have haa : a * a ≤ tt := mul_le_mul hlt.le hlt.le ha0.le ht0.le
    have hcube : a ^ 3 ≤ a * tt := by
      have := mul_le_mul_of_nonneg_left haa ha0.le
      nlinarith
    have m1 : lv * tt ≤ a * tt := mul_le_mul_of_nonneg_right hl1 htt0
    have m3 : lv * tt ≤ lv := by
      have := mul_le_mul_of_nonneg_left htt1 hl0
      linarith
    have m3' : lv * tt ≤ tt := by
      have := mul_le_mul_of_nonneg_right (hl1.trans ha1) htt0
      linarith
    have m4 : 0 ≤ lv * tt := mul_nonneg hl0 htt0
    have m5 : (a - lv) * tt ≤ a - lv := by
      have := mul_le_mul_of_nonneg_left htt1 (by linarith : 0 ≤ a - lv)
      linarith
    have hlow := sub_cube_div_three_le_arctan ha0.le
    have ha3 : 0 ≤ a ^ 3 := by positivity
    have hup := arctan_le_self ha0.le
    have hrc : r ≤ cv := by
      rcases le_or_gt 0 r with h | h
      · rw [hcveq h]
      · linarith
    have hsub : |lv - lv * tt| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 64) := by positivity
    have m6 := mul_le_mul_of_nonneg_right hsub hu0
    have h64 : (1 / 2 : ℝ) ^ (w + 64) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
      have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
        rw [pow_add]
        norm_num
        ring
      rw [← h10]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    refine ⟨cv, hv, hcv, hhv, hcv0, hcvle.trans (max_le ?_ hat0), by linarith, by linarith⟩
    linarith
  · obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2, -, h3⟩ :=
      atanQuot_spec hn hd hn0 hnd (atanWork e w)
    refine ⟨lo, hi, hlo, hhi, hlo0, h1, h2, h3.trans ?_⟩
    have hKw : w + 8 ≤ atanWork e w := by
      unfold atanWork
      omega
    have hKle : (1 / 2 : ℝ) ^ atanWork e w ≤ (1 / 2 : ℝ) ^ (w + 8) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hKw
    have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ atanWork e w := by positivity
    have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 ^ 64 := by norm_num
    rw [h8] at hKle
    rw [pow_add]
    nlinarith

/-- `|y|/|x| < 2^(ey − ex + 1)` from the exponents of the floats. -/
theorem div_lt_two_zpow_exp {a b : ℝ} (hb0 : 0 < b) {ey ex : AzInt}
    (hey : a < (2 : ℝ) ^ ey.toInt) (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ b) :
    a / b < (2 : ℝ) ^ (ey - ex + AzInt.ofInt 1).toInt := by
  have hE : (ey - ex + AzInt.ofInt 1).toInt = ey.toInt - ex.toInt + 1 := by
    rw [AzInt.toInt_add, AzInt.toInt_sub, AzInt.toInt_ofInt]
  rw [hE, div_lt_iff₀ hb0]
  have h2 : (2 : ℝ) ^ (ey.toInt - ex.toInt + 1) * (2 : ℝ) ^ (ex.toInt - 1)
      = (2 : ℝ) ^ ey.toInt := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  have h3 : (2 : ℝ) ^ (ey.toInt - ex.toInt + 1) * (2 : ℝ) ^ (ex.toInt - 1)
      ≤ (2 : ℝ) ^ (ey.toInt - ex.toInt + 1) * b :=
    mul_le_mul_of_nonneg_left hex1 (by positivity)
  linarith

/-- **The bracket of `atan2 (|y|, x)`**: width at most `2^(−w)`. -/
theorem atan2Bracket_spec {y x : AzFloat} {yv xv : ℝ} (hy : y.toVal = some (yv : EReal))
    (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0) (hx0 : xv ≠ 0) {ey ex : AzInt}
    (hey : |yv| < (2 : ℝ) ^ ey.toInt) (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|) (xpos : Bool)
    (w : ℕ) :
    ∃ lo hi : ℝ, (atan2Bracket y x ey ex xpos w).1.toVal = some (lo : EReal) ∧
      (atan2Bracket y x ey ex xpos w).2.toVal = some (hi : EReal) ∧
      lo ≤ atan2Abs |yv| |xv| xpos ∧ atan2Abs |yv| |xv| xpos ≤ hi ∧
      hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  set a := |yv| with ha
  set b := |xv| with hb
  have ha0 : 0 < a := abs_pos.mpr hy0
  have hb0 : 0 < b := abs_pos.mpr hx0
  have hya : y.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hy, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hxa : x.abs.toVal = some ((b : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hwid : ∀ δ : ℝ, δ ≤ 3 / 4 * (1 / 2 : ℝ) ^ (w + 8) + 14 * (1 / 2 : ℝ) ^ (w + 8 + 64) →
      δ + 44 * (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w := fun δ hδ => by
    have e1 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
      rw [pow_add]
      norm_num
      ring
    have e2 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
      have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
        rw [pow_add]
        norm_num
        ring
      rw [← h10]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [show w + 8 + 64 = w + 72 by ring, e1] at hδ
    linarith
  unfold atan2Bracket
  dsimp only
  by_cases hc : y.abs.le x.abs = true
  · simp only [hc, ↓reduceIte]
    have hab : a ≤ b := (le_eq_true_iff hya hxa).mp hc
    cases xpos with
    | true =>
      simp only [↓reduceIte, atan2Abs]
      have hlt := div_lt_two_zpow_exp hb0 hey hex1
      obtain ⟨lo, hi, hlo, hhi, -, h1, h2, h3⟩ := atanQuotRel_spec hya hxa ha0 hab hlt w
      exact ⟨lo, hi, hlo, hhi, h1, h2, h3⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, atan2Abs]
      obtain ⟨al, ah, hal, hah, hal0, h1, h2, hah4, hδ⟩ :=
        atanQuot_spec hya hxa ha0 hab (w + 8)
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        piShiftEncl_spec false false hal hah hal0 h1 h2 hah4 hδ (V := w + 72) (by omega)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, hwd.trans (hwid _ le_rfl)⟩
  · simp only [hc]
    have hab : b < a := not_le.mp fun h => hc ((le_eq_true_iff hya hxa).mpr h)
    obtain ⟨al, ah, hal, hah, hal0, h1, h2, hah4, hδ⟩ :=
      atanQuot_spec hxa hya hb0 hab.le (w + 8)
    have hinv : arctan (a / b) = π / 2 - arctan (b / a) := by
      rw [← arctan_inv_of_pos (div_pos hb0 ha0), inv_div]
    cases xpos with
    | true =>
      simp only [Bool.not_true, ↓reduceIte, atan2Abs]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        piShiftEncl_spec true false hal hah hal0 h1 h2 hah4 hδ (V := w + 72) (by omega)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, hwd.trans (hwid _ le_rfl)⟩
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, atan2Abs]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        piShiftEncl_spec true true hal hah hal0 h1 h2 hah4 hδ (V := w + 72) (by omega)
      simp only [↓reduceIte] at hl hh
      exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, hwd.trans (hwid _ le_rfl)⟩

/-- `atan2Approx neg` as a pair of `Roundable`s bracketing `± atan2 (|y|, x)`. -/
theorem atan2Approx_spec (neg : Bool) {y x : AzFloat} {yv xv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0)
    (hx0 : xv ≠ 0) {ey ex : AzInt} (hey : |yv| < (2 : ℝ) ^ ey.toInt)
    (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|) (xpos : Bool) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (atan2Approx neg y x ey ex xpos w).1 lv ∧
      Rounds (atan2Approx neg y x ey ex xpos w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * atan2Abs |yv| |xv| xpos ∧
      (if neg then -1 else 1) * atan2Abs |yv| |xv| xpos ≤ hv ∧ hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := atan2Bracket_spec hy hx hy0 hx0 hey hex1 xpos w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- The angle of a point with finite nonzero float coordinates is irrational. -/
theorem irrational_arg_of_toVal {y x : AzFloat} {yv xv : ℝ} (hy : y.toVal = some (yv : EReal))
    (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0) :
    Irrational (Complex.arg ⟨xv, yv⟩) := by
  obtain ⟨qy, hqy⟩ := exists_rat_of_toVal hy
  obtain ⟨qx, hqx⟩ := exists_rat_of_toVal hx
  rw [hqy, hqx]
  refine irrational_arg_of_rat ?_
  rintro rfl
  exact hy0 (by rw [hqy, Rat.cast_zero])

/-- `atan2 (|y|, x)` is irrational for finite nonzero floats `y`, `x`. -/
theorem irrational_atan2Abs_of_toVal {y x : AzFloat} {yv xv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0)
    (hx0 : xv ≠ 0) {xpos : Bool} (hxpos : xpos = true ↔ 0 < xv) :
    Irrational (atan2Abs |yv| |xv| xpos) := by
  obtain ⟨qy, hqy⟩ := exists_rat_of_toVal hy
  obtain ⟨qx, hqx⟩ := exists_rat_of_toVal hx
  have hpos : 0 < |yv| := abs_pos.mpr hy0
  have h := arg_eq_atan2Abs (x := xv) (y := |yv|) hx0 hpos.ne' (neg := false)
    (by simp [abs_nonneg]) hxpos
  rw [abs_abs] at h
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  rw [← h, hqy, hqx, ← Rat.cast_abs]
  refine irrational_arg_of_rat ?_
  intro h0
  exact hy0 (by rw [hqy, abs_eq_zero.mp h0, Rat.cast_zero])

/-- The Ziv certificate for `± atan2 (|y|, x)`, `y`, `x` finite and nonzero. -/
theorem atan2Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {y x : AzFloat} {yv xv : ℝ} (hy : y.toVal = some (yv : EReal))
    (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0) (hx0 : xv ≠ 0)
    {xpos : Bool} (hxpos : xpos = true ↔ 0 < xv) {ey ex : AzInt}
    (hey : |yv| < (2 : ℝ) ^ ey.toInt) (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (atan2Approx neg y x ey ex xpos (w₀ * 2 ^ f)).1
      (atan2Approx neg y x ey ex xpos (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  refine exists_isSome_of_irrational_threshold p mode (atan2Approx neg y x ey ex xpos)
    (v := (if neg then -1 else 1) * atan2Abs |yv| |xv| xpos) ?_ (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => atan2Approx_spec neg hy hx hy0 hx0 hey hex1 xpos w) w₀ hw₀
  have hirr := irrational_atan2Abs_of_toVal hy hx hy0 hx0 hxpos
  cases neg with
  | false => simpa using hirr
  | true => simpa using hirr.neg

/-! ### `3π/4` -/

/-- `3π/4` is irrational. -/
theorem irrational_three_pi_div_four : Irrational (3 * π / 4) := by
  have h := irrational_pi.mul_ratCast (q := 3 / 4) (by norm_num)
  convert h using 1
  push_cast
  ring

/-- `piThreeQuartersApprox` brackets `3π/4` with width at most `2^(−w)`. -/
theorem piThreeQuartersApprox_spec (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (piThreeQuartersApprox w).1 lv ∧ Rounds (piThreeQuartersApprox w).2 hv ∧
      lv ≤ 3 * π / 4 ∧ 3 * π / 4 ≤ hv ∧ hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  have hV : 64 ≤ w + 64 := by omega
  set u := (1 / 2 : ℝ) ^ (w + 64) with hu
  have hu0 : 0 ≤ u := by positivity
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have huw : u ≤ (1 / 2 : ℝ) ^ w / 1024 := by
    have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
      rw [pow_add]
      norm_num
      ring
    rw [hu, ← h10]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hπ := pi_lt_four
  obtain ⟨pl, ph, hpl, hph, hpl0, hpl1, hph1, hpw⟩ := piBracket_spec_width hV
  rw [← hu] at hpw
  have hal : ((piBracket (w + 64)).1 <<< AzInt.ofInt (-2)).toVal
      = some ((pl / 4 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hpl (AzInt.ofInt (-2))
    rw [h, AzInt.toInt_ofInt, show ((2 : ℝ) ^ (-2 : ℤ)) = 1 / 4 by norm_num, mul_one_div]
  have hah : ((piBracket (w + 64)).2 <<< AzInt.ofInt (-2)).toVal
      = some ((ph / 4 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hph (AzInt.ofInt (-2))
    rw [h, AzInt.toInt_ofInt, show ((2 : ℝ) ^ (-2 : ℤ)) = 1 / 4 by norm_num, mul_one_div]
  obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ := piShiftEncl_spec true true
    (A := ((piBracket (w + 64)).1 <<< AzInt.ofInt (-2),
      (piBracket (w + 64)).2 <<< AzInt.ofInt (-2)))
    (α := π / 4) (δ := 2 * u) hal hah (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hV
  simp only [↓reduceIte] at hl hh
  rw [← hu] at hwd
  obtain ⟨lv, hv, hR1, hR2, hl', hh', he⟩ := enclApprox_spec false hlo hhi
    (v := 3 * π / 4) (by linarith) (by linarith)
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl' hh'
  exact ⟨lv, hv, hR1, hR2, hl', hh', by rw [he]; linarith⟩

/-- The Ziv certificate for `3π/4`. -/
theorem piThreeQuartersApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (piThreeQuartersApprox (w₀ * 2 ^ f)).1
      (piThreeQuartersApprox (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode piThreeQuartersApprox
    irrational_three_pi_div_four (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => piThreeQuartersApprox_spec w) w₀ hw₀

end Azurite.AzFloat
