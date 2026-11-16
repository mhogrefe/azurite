/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanhBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.Equiv.SinRatBracket
import Azurite.AzFloat.Equiv.SinhBracket
import Azurite.AzRat.Equiv.Add
import Azurite.Transcendental.Sinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Equivalence: the brackets of `tanh x` and `tanh q`

`tanh_eq_expm1` (`tanh a = v/(2 + v)`, `v = e^(2a) − 1`), `tanhStep_bounds` (the real
arithmetic of the outward rounding), `tanhOfExpM1_spec`, `tanhOfExpM1_width` (width at most
`tanhWidth`), `tanhBracket_spec`, `tanhApprox_spec`, `irrational_tanh_of_toVal`,
`tanhApprox_isSome_exists`, the rational versions `tanhRatBracket_spec`, `tanhRatApprox_spec`,
`irrational_tanh_toRat`, `tanhRatApprox_isSome_exists`, the tiny-argument bounds
`tanh_lt_self`, `sub_cube_le_tanh`, and the large-argument path `log_tanh_bound`,
`tanhNearOne?_eq`, `tanhFloatN_le`, `tanhRatN_le`.
-/

open Real

namespace Azurite.AzFloat

/-- `tanh a = v/(2 + v)` with `v = e^(2a) − 1`. -/
theorem tanh_eq_expm1 (a : ℝ) :
    Real.tanh a = (Real.exp (2 * a) - 1) / (2 + (Real.exp (2 * a) - 1)) := by
  have h := exp_pos a
  have hi := inv_pos.mpr h
  have hh : 0 < Real.exp a * Real.exp a := mul_pos h h
  rw [tanh_eq, exp_neg, two_mul, exp_add, div_eq_div_iff (by positivity) (by linarith)]
  field_simp
  ring

/-- `u/(2 + u)` is increasing on `u ≥ 0`. -/
theorem div_two_add_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : u / (2 + u) ≤ v / (2 + v) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The difference of the two exact quotients `vh/d2` and `vl/d1`. -/
theorem tanhQuot_diff {vl vh d1 d2 A1 A2 η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8)
    (hvl0 : 0 ≤ vl) (hlh : vl ≤ vh) (hd1a : 2 + vl ≤ d1)
    (hd1b : d1 ≤ 2 + vl + 2 * (2 + vl) * η) (hd2b : 2 + vh ≤ d2 + 2 * (2 + vh) * η)
    (hA1 : A1 * d1 = vl) (hA2 : A2 * d2 = vh) : A2 - A1 ≤ (vh - vl) + 6 * η := by
  have hvh0 : 0 ≤ vh := hvl0.trans hlh
  set P := (2 + vl) * (2 + vh) with hP
  have hP4 : 4 ≤ P := by nlinarith
  have hd2 : 3 / 4 * (2 + vh) ≤ d2 := by nlinarith
  have hprod : 3 / 4 * P ≤ d1 * d2 := by
    have := mul_le_mul hd1a hd2 (by positivity) (by linarith)
    nlinarith
  have h1 : vh * d1 ≤ vh * (2 + vl + 2 * (2 + vl) * η) := mul_le_mul_of_nonneg_left hd1b hvh0
  have h2 : vl * (2 + vh - 2 * (2 + vh) * η) ≤ vl * d2 :=
    mul_le_mul_of_nonneg_left (by linarith) hvl0
  have hvv : 0 ≤ vh * vl := mul_nonneg hvh0 hvl0
  have hsm : 2 * vh + 2 * vl + 2 * (vh * vl) ≤ 2 * P := by nlinarith
  have hsmη := mul_le_mul_of_nonneg_left hsm hη0
  have hN : vh * d1 - vl * d2 ≤ 2 * (vh - vl) + 4 * η * P := by nlinarith
  have hkey : (A2 - A1) * (d1 * d2) = vh * d1 - vl * d2 := by
    rw [← hA1, ← hA2]
    ring
  set D := vh - vl with hD
  have hD0 : 0 ≤ D := by linarith
  by_contra hcon
  push Not at hcon
  have hB : 2 / 3 * D + 16 / 3 * η < A2 - A1 := by linarith
  have h4 : (2 / 3 * D + 16 / 3 * η) * (3 / 4 * P) ≤ (A2 - A1) * (d1 * d2) :=
    mul_le_mul hB.le hprod (by positivity) (by linarith)
  have h5 : (2 / 3 * D + 16 / 3 * η) * (3 / 4 * P) = D * P / 2 + 4 * η * P := by ring
  have h6 : 2 * D ≤ D * P / 2 := by nlinarith
  have h7 : (A2 - A1) * (3 / 4 * P) ≤ (A2 - A1) * (d1 * d2) :=
    mul_le_mul_of_nonneg_left hprod (by linarith)
  have h8 : (2 / 3 * D + 16 / 3 * η) * (3 / 4 * P) < (A2 - A1) * (3 / 4 * P) :=
    mul_lt_mul_of_pos_right hB (by linarith)
  linarith

/-- The real arithmetic of `tanhOfExpM1`: the enclosure and its width. -/
theorem tanhStep_bounds {V vl vh d1 q1 d2 q2 η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8)
    (hvl0 : 0 ≤ vl) (hvlV : vl ≤ V) (hVvh : V ≤ vh)
    (hd1a : 2 + vl ≤ d1) (hd1b : d1 ≤ 2 + vl + 2 * |2 + vl| * η)
    (hq1a : q1 ≤ vl / d1) (hq1b : vl / d1 ≤ q1 + 2 * |vl / d1| * η)
    (hd2a : d2 ≤ 2 + vh) (hd2b : 2 + vh ≤ d2 + 2 * |2 + vh| * η)
    (hq2a : vh / d2 ≤ q2) (hq2b : q2 ≤ vh / d2 + 2 * |vh / d2| * η) :
    q1 ≤ V / (2 + V) ∧ V / (2 + V) ≤ q2 ∧ q2 - q1 ≤ (vh - vl) + 12 * η := by
  have hV0 : 0 ≤ V := hvl0.trans hvlV
  have hvh0 : 0 ≤ vh := hV0.trans hVvh
  rw [abs_of_nonneg (by linarith)] at hd1b hd2b
  have hd1 : 2 ≤ d1 := by linarith
  have hd2 : 3 / 4 * (2 + vh) ≤ d2 := by nlinarith
  have hd2pos : 0 < d2 := by linarith
  have hA1 : 0 ≤ vl / d1 := div_nonneg hvl0 (by linarith)
  have hA2 : 0 ≤ vh / d2 := div_nonneg hvh0 hd2pos.le
  rw [abs_of_nonneg hA1] at hq1b
  rw [abs_of_nonneg hA2] at hq2b
  have hA1m : vl / d1 ≤ vl / (2 + vl) := div_le_div_of_nonneg_left hvl0 (by linarith) hd1a
  have hA2m : vh / (2 + vh) ≤ vh / d2 := div_le_div_of_nonneg_left hvh0 hd2pos hd2a
  have hA1u : vl / d1 ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hA2u : vh / d2 ≤ 4 / 3 := by
    rw [div_le_iff₀ hd2pos]
    linarith
  have hm1 := div_two_add_mono hvl0 hvlV
  have hm2 := div_two_add_mono hV0 hVvh
  refine ⟨by linarith, by linarith, ?_⟩
  have hdiff := tanhQuot_diff hη0 hη hvl0 (hvlV.trans hVvh) hd1a hd1b hd2b
    (div_mul_cancel₀ vl (by linarith : d1 ≠ 0)) (div_mul_cancel₀ vh hd2pos.ne')
  have e1 : vh / d2 * η ≤ 4 / 3 * η := mul_le_mul_of_nonneg_right hA2u hη0
  have e2 : vl / d1 * η ≤ 1 * η := mul_le_mul_of_nonneg_right hA1u hη0
  linarith

/-- The value of the float `2`. -/
theorem toVal_two_float : (one <<< AzInt.ofInt 1).toVal = some ((2 : ℝ) : EReal) := by
  have h := toVal_shiftLeft_of_toVal toVal_one' (AzInt.ofInt 1)
  rw [AzInt.toInt_ofInt, zpow_one, one_mul] at h
  exact h

/-- **`tanhOfExpM1` encloses `V/(2 + V)`** for an enclosure `[vl, vh]` of `V ≥ 0`. -/
theorem tanhOfExpM1_spec {v : Encl} {V vl vh : ℝ} (hlo : v.1.toVal = some (vl : EReal))
    (hhi : v.2.toVal = some (vh : EReal)) (hV0 : 0 ≤ V) (h1 : vl ≤ V) (h2 : V ≤ vh) {W : ℕ}
    (hW : 3 ≤ W) :
    IsEnclW (tanhOfExpM1 v W) (V / (2 + V)) ((vh - vl) + 12 * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hlo
  have hcU : cv ≤ V := hcvle.trans (max_le h1 hV0)
  have hrc : vl ≤ cv := by
    rcases le_or_gt 0 vl with h | h
    · rw [hcveq h]
    · linarith
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hη : (1 / 2 : ℝ) ^ W ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hW
      _ = 1 / 8 := by norm_num
  have hvh0 : 0 ≤ vh := hV0.trans h2
  obtain ⟨d1, hd1, hd1a, hd1b⟩ := addCeiling_abs toVal_two_float hcv W
  have hd1pos : (0 : ℝ) < d1 := by linarith
  obtain ⟨q1, hq1, hq1a, hq1b⟩ := divFloor_abs hcv hd1 hd1pos.ne' W
  obtain ⟨d2, hd2, hd2a, hd2b⟩ := addFloor_abs toVal_two_float hhi W
  have hd2pos : (0 : ℝ) < d2 := by
    rw [abs_of_nonneg (by linarith)] at hd2b
    nlinarith
  obtain ⟨q2, hq2, hq2a, hq2b⟩ := divCeiling_abs hhi hd2 hd2pos.ne' W
  obtain ⟨b1, b2, b3⟩ := tanhStep_bounds hη0 hη hcv0 hcU h2 hd1a hd1b hq1a hq1b
    hd2a hd2b hq2a hq2b
  exact ⟨q1, q2, hq1, hq2, b1, b2, by linarith⟩

/-- The width of `tanhOfExpM1` at precision `w + 16` on an enclosure of width `E`. -/
noncomputable def tanhWidth (E : ℝ) (w : ℕ) : ℝ := E + 12 * (1 / 2 : ℝ) ^ w

theorem tendsto_tanhWidth {E : ℕ → ℝ} (hE : Filter.Tendsto E Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun w => tanhWidth (E w) w) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := hE.add (hp.const_mul 12)
  have h0 : (0 + 12 * 0 : ℝ) = 0 := by ring
  rw [h0] at h
  exact h

/-- **`tanhOfExpM1` at precision `w + 16` encloses `tanh a`**, `a ≥ 0`, from an enclosure of
`e^(2a) − 1` of width at most `E`, with width at most `tanhWidth E w`. -/
theorem tanhOfExpM1_width {v : Encl} {av lo hi E : ℝ} (hlo : v.1.toVal = some (lo : EReal))
    (hhi : v.2.toVal = some (hi : EReal)) (ha0 : 0 ≤ av) (h1 : lo ≤ Real.exp (2 * av) - 1)
    (h2 : Real.exp (2 * av) - 1 ≤ hi) (h3 : hi - lo ≤ E) (w : ℕ) :
    IsEnclW (tanhOfExpM1 v (w + 16)) (Real.tanh av) (tanhWidth E w) := by
  have hV0 : 0 ≤ Real.exp (2 * av) - 1 := by
    have := add_one_le_exp (2 * av)
    linarith
  have hs := tanhOfExpM1_spec hlo hhi hV0 h1 h2 (W := w + 16) (by omega)
  rw [← tanh_eq_expm1] at hs
  refine hs.mono ?_
  unfold tanhWidth
  have hpw : (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

/-- `tanh x` from `tanh |x|`. -/
theorem tanh_abs_eq {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    (if neg then -1 else 1) * Real.tanh |xv| = Real.tanh xv := by
  cases neg with
  | true =>
    have hlt : xv < 0 := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg hlt, tanh_neg]
    ring
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg hpos]

/-! ### The float bracket -/

/-- **`tanhBracket a e w` encloses `tanh a`** for a float `0 < a < 2^e`. -/
theorem tanhBracket_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) (e : AzInt) (hae : av < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (tanhBracket a e w) (Real.tanh av)
      (tanhWidth (expM1Eps (2 * av) (expM1Comp (e + AzInt.ofInt 1)) w) w) := by
  have h2a : (a <<< AzInt.ofInt 1).toVal = some ((2 * av : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal ha (AzInt.ofInt 1)
    rw [AzInt.toInt_ofInt, zpow_one, mul_comm] at h
    exact h
  have hlt : |2 * av| < (2 : ℝ) ^ (e + AzInt.ofInt 1).toInt := by
    rw [AzInt.toInt_add, AzInt.toInt_ofInt, zpow_add₀ (by norm_num), zpow_one,
      abs_of_pos (by linarith)]
    linarith
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expM1Bracket_spec h2a (e + AzInt.ofInt 1) hlt hw
  exact tanhOfExpM1_width hlo hhi ha0.le h1 h2 h3 w

/-- `tanhApprox neg` as a pair of `Roundable`s bracketing `tanh x`. -/
theorem tanhApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {e : AzInt} (hxe : |xv| < (2 : ℝ) ^ e.toInt) {neg : Bool}
    (hneg : neg = true ↔ xv < 0) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (tanhApprox neg x e w).1 lv ∧ Rounds (tanhApprox neg x e w).2 hv ∧
      lv ≤ Real.tanh xv ∧ Real.tanh xv ≤ hv ∧
      hv - lv ≤ tanhWidth (expM1Eps (2 * |xv|) (expM1Comp (e + AzInt.ofInt 1)) w) w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    tanhBracket_spec habs (abs_pos.mpr hx0) e hxe hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  rw [tanh_abs_eq hneg] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `tanh x` is irrational for a finite float `x ≠ 0`. -/
theorem irrational_tanh_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.tanh xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  rw [hq] at hx0 ⊢
  exact irrational_tanh_rat (by exact_mod_cast hx0)

/-- The Ziv certificate for `tanh x`, `x` a finite nonzero float. -/
theorem tanhApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {e : AzInt}
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (tanhApprox neg x e (w₀ * 2 ^ f)).1
      (tanhApprox neg x e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (tanhApprox neg x e)
    (irrational_tanh_of_toVal hx hx0)
    (fun w => tanhWidth (expM1Eps (2 * |xv|) (expM1Comp (e + AzInt.ofInt 1)) w) w)
    (tendsto_tanhWidth (tendsto_expM1Eps _ _)) 64
    (fun _ hw => tanhApprox_spec hx hx0 hxe hneg hw) w₀ hw₀

/-! ### The rational bracket -/

/-- The width bound of `tanhRatBracket`. -/
noncomputable def tanhRatEps (q : AzRat) (w : ℕ) : ℝ :=
  tanhWidth (expM1RatEps (AzRat.toRat (q.abs + q.abs) : ℝ)
    (expM1Comp (AzInt.ofInt (AzRat.floorLogBaseAbs 2 (q.abs + q.abs) + 2))) w) w

theorem tendsto_tanhRatEps (q : AzRat) :
    Filter.Tendsto (tanhRatEps q) Filter.atTop (nhds 0) :=
  tendsto_tanhWidth (tendsto_expM1RatEps _ _)

/-- **`tanhRatBracket q w` encloses `tanh |q|`** for a rational `q ≠ 0`. -/
theorem tanhRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    IsEnclW (tanhRatBracket q w) (Real.tanh |((AzRat.toRat q : ℚ) : ℝ)|) (tanhRatEps q w) := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have h2 : ((AzRat.toRat (q.abs + q.abs) : ℚ) : ℝ) = 2 * |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_add, AzRat.toRat_abs]
    push_cast
    ring
  have hne : (q.abs + q.abs).num ≠ 0 := fun h => by
    have := coe_toRat_eq_zero_of_num_eq_zero _ h
    rw [h2] at this
    have := abs_pos.mpr hq0
    linarith
  obtain ⟨lo, hi, hlo, hhi, h1, h2', h3⟩ := expM1RatBracket_spec hw (q.abs + q.abs) hne
  rw [h2] at h1 h2'
  exact tanhOfExpM1_width hlo hhi (abs_nonneg _) h1 h2' h3 w

/-- `!q.sign` is the sign bit of a negative rational. -/
theorem toRat_neg_iff (q : AzRat) (h0 : q.num ≠ 0) :
    (!q.sign) = true ↔ (AzRat.toRat q : ℝ) < 0 := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have hs := toRat_sign_iff q h0
  constructor
  · intro h
    rcases lt_or_gt_of_ne hq0 with h' | h'
    · exact h'
    · rw [hs.mpr h'] at h
      cases h
  · intro h
    cases hsg : q.sign
    · rfl
    · exact absurd (hs.mp hsg) (not_lt.mpr h.le)

/-- `tanhRatApprox` as a pair of `Roundable`s bracketing `tanh q`. -/
theorem tanhRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    ∃ lv hv : ℝ, Rounds (tanhRatApprox q w).1 lv ∧ Rounds (tanhRatApprox q w).2 hv ∧
      lv ≤ Real.tanh (AzRat.toRat q : ℝ) ∧ Real.tanh (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ tanhRatEps q w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := tanhRatBracket_spec hw q h0
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec (!q.sign) hlo hhi h1 h2
  rw [tanh_abs_eq (toRat_neg_iff q h0)] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `tanh q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_tanh_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.tanh (AzRat.toRat q : ℝ)) :=
  irrational_tanh_rat (q := AzRat.toRat q)
    (fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp (by rw [h, Rat.cast_zero])))

/-- The Ziv certificate for `tanh q`. -/
theorem tanhRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (tanhRatApprox q (w₀ * 2 ^ f)).1
      (tanhRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (tanhRatApprox q) (irrational_tanh_toRat q h0)
    (tanhRatEps q) (tendsto_tanhRatEps q) 64 (fun _ hw => tanhRatApprox_spec hw q h0) w₀ hw₀

/-! ### Tiny arguments -/

/-- `tanh a < a` for `a > 0`. -/
theorem tanh_lt_self {a : ℝ} (h0 : 0 < a) : Real.tanh a < a := by
  rcases le_or_gt 1 a with h1 | h1
  · exact lt_of_lt_of_le (tanh_lt_one a) h1
  have hb1 := exp_bound (x := a) (by rw [abs_of_pos h0]; exact h1.le) (n := 4) (by norm_num)
  have hb2 := exp_bound (x := -a) (by rw [abs_neg, abs_of_pos h0]; exact h1.le) (n := 4)
    (by norm_num)
  rw [abs_neg] at hb2
  rw [abs_of_pos h0] at hb1 hb2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb1 hb2
  have ha3 : 0 < a ^ 3 := by positivity
  have h4 : a ^ 4 ≤ a ^ 3 := by
    have : a ^ 4 = a ^ 3 * a := by ring
    rw [this]
    exact mul_le_of_le_one_right ha3.le h1.le
  have h5 : a ^ 5 ≤ a ^ 3 := by
    have : a ^ 5 = a ^ 4 * a := by ring
    rw [this]
    exact (mul_le_of_le_one_right (by positivity) h1.le).trans h4
  obtain ⟨l1, u1⟩ := abs_le.mp hb1
  obtain ⟨l2, u2⟩ := abs_le.mp hb2
  norm_num at l1 u1 l2 u2
  have hc : 0 < Real.cosh a := cosh_pos a
  rw [tanh_eq_sinh_div_cosh, div_lt_iff₀ hc, sinh_eq, cosh_eq]
  have e5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith

/-- `a − a³ ≤ tanh a` for `a > 0`. -/
theorem sub_cube_le_tanh {a : ℝ} (h0 : 0 < a) : a - a ^ 3 ≤ Real.tanh a := by
  have hc : 0 < Real.cosh a := cosh_pos a
  have hs : a < Real.sinh a := self_lt_sinh_iff.mpr h0
  have hce := cosh_le_exp_half_sq a
  have hinv : 1 - a ^ 2 / 2 ≤ Real.exp (-(a ^ 2 / 2)) := by
    have := add_one_le_exp (-(a ^ 2 / 2))
    linarith
  rw [tanh_eq_sinh_div_cosh, le_div_iff₀ hc]
  rcases le_or_gt 1 a with h1 | h1
  · have : a - a ^ 3 ≤ 0 := by nlinarith
    nlinarith
  have hpos : 0 ≤ a - a ^ 3 := by nlinarith
  have hee : Real.exp (-(a ^ 2 / 2)) * Real.exp (a ^ 2 / 2) = 1 := by
    rw [← exp_add]
    simp
  have h3 : (1 - a ^ 2 / 2) * Real.cosh a ≤ 1 := by
    have hnn : 0 ≤ 1 - a ^ 2 / 2 := by nlinarith
    calc (1 - a ^ 2 / 2) * Real.cosh a ≤ Real.exp (-(a ^ 2 / 2)) * Real.exp (a ^ 2 / 2) :=
          mul_le_mul hinv hce hc.le (exp_pos _).le
      _ = 1 := hee
  have h4 : a - a ^ 3 ≤ a * (1 - a ^ 2 / 2) := by nlinarith
  have h5 : (a - a ^ 3) * Real.cosh a ≤ a * (1 - a ^ 2 / 2) * Real.cosh a :=
    mul_le_mul_of_nonneg_right h4 hc.le
  nlinarith

/-! ### Large arguments -/

/-- For `1 ≤ M ≤ 2a`: `tanh a = exp v` with `v = ln tanh a < 0` and `|v| < 2^(2 − M)`. -/
theorem log_tanh_bound {a : ℝ} {M : ℕ} (hM : 1 ≤ M) (h : (M : ℝ) ≤ 2 * a) :
    0 < Real.tanh a ∧ Real.log (Real.tanh a) < 0 ∧
      |Real.log (Real.tanh a)| < (2 : ℝ) ^ ((2 : ℤ) - M) := by
  set X := Real.exp (2 * a) with hX
  have hXM : (2 : ℝ) ^ M < X := by
    have h1 : Real.exp (M : ℝ) ≤ X := exp_le_exp.mpr h
    have h2 : (2 : ℝ) ^ M < Real.exp 1 ^ M :=
      pow_lt_pow_left₀ (by linarith [exp_one_gt_d9]) (by norm_num) (by omega)
    rw [← exp_nat_mul, mul_one] at h2
    linarith
  have h2M : (2 : ℝ) ≤ (2 : ℝ) ^ M := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
  have hT : Real.tanh a = (X - 1) / (2 + (X - 1)) := tanh_eq_expm1 a
  have hT0 : 0 < Real.tanh a := by
    rw [hT]
    exact div_pos (by linarith) (by linarith)
  have hT1 := tanh_lt_one a
  have hlog : Real.log (Real.tanh a) < 0 := Real.log_neg hT0 hT1
  refine ⟨hT0, hlog, ?_⟩
  rw [abs_of_neg hlog, ← Real.log_inv]
  have h3 := Real.log_le_sub_one_of_pos (inv_pos.mpr hT0)
  have h4 : (Real.tanh a)⁻¹ - 1 = 2 / (X - 1) := by
    have hX1 : 0 < X - 1 := by linarith
    rw [hT, inv_div, div_sub_one hX1.ne']
    congr 1
    ring
  have h5 : 2 / (X - 1) < (2 : ℝ) ^ ((2 : ℤ) - M) := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, div_lt_div_iff₀ (by linarith) (by positivity)]
    norm_num
    nlinarith
  linarith

/-- **The large-argument path answers with the rounding of `± tanh a`**, for `a > 0` and a
natural `N ≤ 2a`. -/
theorem tanhNearOne?_eq {pos : Bool} {N p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {a : ℝ} (hN : (N : ℝ) ≤ 2 * a)
    (h : tanhNearOne? pos N p mode = some r) :
    r = roundVal p mode (some (((if pos then 1 else -1) * Real.tanh a : ℝ) : EReal)) := by
  unfold tanhNearOne? at h
  dsimp only at h
  set M := min N 4611686018427387904 with hMdef
  have hE : (AzInt.ofInt (2 - (M : Int))).toInt = (2 : ℤ) - M := AzInt.toInt_ofInt _
  have key : ∀ {m' : RoundingMode} {r' : AzFloat × Ordering},
      expNearOne? false (AzInt.ofInt (2 - (M : Int))) p m' = some r' →
      r' = roundVal p m' (some ((Real.tanh a : ℝ) : EReal)) := by
    intro m' r' h'
    have hc := expNearOne?_cond h'
    rw [hE] at hc
    have hM1 : 1 ≤ M := by
      by_contra hcon
      have hM0 : M = 0 := by omega
      rw [hM0] at hc
      norm_num at hc
    have hMa : (M : ℝ) ≤ 2 * a :=
      le_trans (by exact_mod_cast min_le_left N 4611686018427387904) hN
    obtain ⟨hT0, hlog, hb⟩ := log_tanh_bound hM1 hMa
    rw [← hE] at hb
    have := expNearOne?_eq hb hlog.ne (by simp [hlog.le]) h'
    rwa [Real.exp_log hT0] at this
  cases pos with
  | true =>
    simp only [↓reduceIte, one_mul] at h ⊢
    exact key h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul] at h ⊢
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [key hr', roundVal_neg]

/-- `tanhFloatN e ≤ 2|x|` for `|x| ≥ 2^(e−1)`. -/
theorem tanhFloatN_le {e : AzInt} {xv : ℝ} (hx : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|) :
    (tanhFloatN e : ℝ) ≤ 2 * |xv| := by
  unfold tanhFloatN
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  cases hs : e.sign with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
    positivity
  | true =>
    simp only [↓reduceIte]
    rw [hs] at htoInt
    simp only [↓reduceIte] at htoInt
    have h1 : (2 : ℝ) ^ e.toInt ≤ 2 * |xv| := by
      have : (2 : ℝ) ^ e.toInt = 2 * (2 : ℝ) ^ (e.toInt - 1) := by
        rw [zpow_sub₀ (by norm_num), zpow_one]
        ring
      rw [this]
      linarith
    have h2 : ((2 ^ (min e.abs.toNat 62) : ℕ) : ℝ) ≤ (2 : ℝ) ^ e.toInt := by
      rw [htoInt, zpow_natCast]
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (min_le_left _ _)
    exact h2.trans h1

/-- `tanhRatN q ≤ 2|q|`. -/
theorem tanhRatN_le (q : AzRat) : (tanhRatN q : ℝ) ≤ 2 * |(AzRat.toRat q : ℝ)| := by
  unfold tanhRatN
  rw [AzNat.toNat_div, AzNat.toNat_add, abs_coe_toRat]
  have h := Nat.cast_div_le (α := ℝ) (m := q.num.toNat + q.num.toNat) (n := q.den.toNat)
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end Azurite.AzFloat
