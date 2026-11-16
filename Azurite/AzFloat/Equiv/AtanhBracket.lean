/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanhBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.Equiv.LnBracket
import Azurite.AzFloat.Equiv.AsecRat
import Azurite.AzFloat.Equiv.TanhBracket
import Azurite.AzFloat.Equiv.TanRatBracket
import Azurite.AzRat.Equiv.Add
import Azurite.AzRat.Equiv.Sub
import Azurite.Transcendental.Sinh

/-!
# Equivalence: the brackets of `atanh x` and `atanh q`

`atanhArg_bounds` (the real arithmetic of the rounded-down quotient `(1 + a)/(1 − a)`),
`atanhOfArg_spec` (half the logarithm bracket), `atanhBracket_spec`, `atanhApprox_spec`,
`irrational_atanh_of_toVal`, `atanhApprox_isSome_exists`, the
rational versions `atanhRatBracket_spec`, `atanhRatApprox_spec`, `irrational_atanh_toRat`,
`atanhRatApprox_isSome_exists`, `abs_toRat_lt_one_of`, and the tiny-argument path
`artanh_neg'`, `artanh_tiny_bounds`, `atanhTiny?_eq`, `atanhTinyRat?_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- The real arithmetic of `atanhArg`: the quotient of a sum rounded down and a difference
rounded up, rounded down, is within a relative `8η` below `(1 + A)/(1 − A)`. -/
theorem atanhArg_bounds {A su df y η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 64) (hA0 : 0 ≤ A)
    (hA1 : A < 1) (hsu1 : su ≤ 1 + A) (hsu2 : 1 + A ≤ su + 2 * (1 + A) * η)
    (hdf1 : 1 - A ≤ df) (hdf2 : df ≤ 1 - A + 2 * (1 - A) * η)
    (hy1 : y ≤ su / df) (hy2 : su / df ≤ y + 2 * (su / df) * η) :
    y ≤ (1 + A) / (1 - A) ∧
      (1 + A) / (1 - A) ≤ y + 8 * ((1 + A) / (1 - A)) * η := by
  have hd0 : 0 < 1 - A := by linarith
  have hdf0 : 0 < df := lt_of_lt_of_le hd0 hdf1
  set V := (1 + A) / (1 - A) with hV
  have hV0 : 0 ≤ V := div_nonneg (by linarith) hd0.le
  have hVd : V * (1 - A) = 1 + A := div_mul_cancel₀ _ hd0.ne'
  have hc0 : 0 < 1 - 2 * η := by linarith
  have hup : su / df ≤ V := div_le_div₀ (by linarith) hsu1 hd0 hdf1
  have hVdf : V * df ≤ (1 + A) * (1 + 2 * η) := by
    have := mul_le_mul_of_nonneg_left hdf2 hV0
    have e : V * (1 - A + 2 * (1 - A) * η) = V * (1 - A) * (1 + 2 * η) := by ring
    rw [e, hVd] at this
    exact this
  have hlow : (1 - 2 * η) * (1 - 2 * η) * V ≤ su / df := by
    rw [le_div_iff₀ hdf0]
    have h1 : (1 - 2 * η) * (1 - 2 * η) * V * df
        ≤ (1 - 2 * η) * (1 - 2 * η) * ((1 + A) * (1 + 2 * η)) := by
      have := mul_le_mul_of_nonneg_left hVdf (mul_nonneg hc0.le hc0.le)
      linarith
    have h2 : (1 - 2 * η) * (1 + 2 * η) ≤ 1 := by nlinarith
    have h3 : (1 - 2 * η) * (1 - 2 * η) * ((1 + A) * (1 + 2 * η))
        ≤ (1 - 2 * η) * (1 + A) := by
      have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hc0.le (by linarith : (0 : ℝ) ≤ 1 + A))
      linarith
    linarith
  have hy : (1 - 2 * η) * (su / df) ≤ y := by linarith
  have hy' : (1 - 2 * η) * ((1 - 2 * η) * (1 - 2 * η) * V) ≤ y :=
    (mul_le_mul_of_nonneg_left hlow hc0.le).trans hy
  have hbern : 1 - 6 * η ≤ (1 - 2 * η) * ((1 - 2 * η) * (1 - 2 * η)) := by
    have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(2 * η)) 3
    have e : (1 + -(2 * η)) ^ 3 = (1 - 2 * η) * ((1 - 2 * η) * (1 - 2 * η)) := by ring
    rw [e] at h
    push_cast at h
    linarith
  have hfin : (1 - 6 * η) * V ≤ y := by
    have := mul_le_mul_of_nonneg_right hbern hV0
    linarith
  have hVη : 0 ≤ V * η := mul_nonneg hV0 hη0
  constructor
  · linarith
  · linarith

/-- The width bound of the brackets of `atanh a`. -/
noncomputable def atanhEps (A : ℝ) (w : ℕ) : ℝ :=
  lnRatEps (⌊2 * |Real.log ((1 + A) / (1 - A))|⌋₊ + 2) |Real.log ((1 + A) / (1 - A))| w

theorem tendsto_atanhEps (A : ℝ) : Filter.Tendsto (atanhEps A) Filter.atTop (nhds 0) :=
  tendsto_lnRatEps _ _

/-- **`atanhOfArg (atanhArg su df)` encloses `atanh A`**, `0 ≤ A < 1`, for floats `su` just
below `1 + A` and `df` just above `1 − A`. -/
theorem atanhOfArg_spec {su df : AzFloat} {suv dfv A : ℝ} {w : ℕ} (hw : 64 ≤ w)
    (hA0 : 0 ≤ A) (hA1 : A < 1) (hsu : su.toVal = some (suv : EReal)) (hsu0 : 0 ≤ suv)
    (hsu1 : suv ≤ 1 + A) (hsu2 : 1 + A ≤ suv + 2 * (1 + A) * (1 / 2 : ℝ) ^ (w + 8))
    (hdf : df.toVal = some (dfv : EReal)) (hdf1 : 1 - A ≤ dfv)
    (hdf2 : dfv ≤ 1 - A + 2 * (1 - A) * (1 / 2 : ℝ) ^ (w + 8)) :
    IsEnclW (atanhOfArg (atanhArg su df (w + 8)) w) (Real.artanh A) (atanhEps A w) := by
  have : NeZero (w + 8) := ⟨by omega⟩
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 8) := by positivity
  have hη : (1 / 2 : ℝ) ^ (w + 8) ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ (w + 8) ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  have hdf0 : 0 < dfv := by linarith
  obtain ⟨y, hy, -, hy1, hy2⟩ := divFloor_err hsu hdf hdf0 hsu0 (w + 8)
  obtain ⟨b1, b2⟩ := atanhArg_bounds hη0 hη hA0 hA1 hsu1 hsu2 hdf1 hdf2 hy1 hy2
  have hV : 0 < (1 + A) / (1 - A) := div_pos (by linarith) (by linarith)
  have hpw : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  have hy2' : (1 + A) / (1 - A) ≤ y + 2 * ((1 + A) / (1 - A)) * (1 / 2 : ℝ) ^ w := by
    rw [hpw] at b2
    have : 0 ≤ (1 + A) / (1 - A) * (1 / 2 : ℝ) ^ w := by positivity
    linarith
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := lnFloorBracket_spec hw hy hV b1 hy2'
  have hsh1 := toVal_shiftLeft_of_toVal hlv (AzInt.ofInt (-1))
  have hsh2 := toVal_shiftLeft_of_toVal hhv (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at hsh1 hsh2
  have hart : Real.artanh A = 1 / 2 * Real.log ((1 + A) / (1 - A)) :=
    artanh_eq_half_log ⟨by linarith, hA1.le⟩
  have hw0 : 0 ≤ hv - lv := by linarith
  unfold atanhEps
  exact ⟨lv / 2, hv / 2, hsh1, hsh2, by rw [hart]; linarith, by rw [hart]; linarith,
    by linarith⟩

/-- `artanh` is odd. -/
theorem artanh_neg' (x : ℝ) : Real.artanh (-x) = -Real.artanh x := by
  unfold Real.artanh
  have e : (1 + -x) / (1 - -x) = ((1 + x) / (1 - x))⁻¹ := by
    rw [inv_div]
    ring_nf
  rw [e, sqrt_inv, Real.log_inv]

/-- `atanh x` from `atanh |x|`. -/
theorem atanh_abs_eq {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    (if neg then -1 else 1) * Real.artanh |xv| = Real.artanh xv := by
  cases neg with
  | true =>
    have hlt : xv < 0 := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg hlt, artanh_neg']
    ring
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg hpos]

/-! ### Floats -/

/-- **`atanhBracket a w` encloses `atanh a`** for a float `0 ≤ a < 1`. -/
theorem atanhBracket_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 ≤ av) (ha1 : av < 1) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (atanhBracket a w) (Real.artanh av) (atanhEps av w) := by
  have : NeZero (w + 8) := ⟨by omega⟩
  obtain ⟨s, hs, hs0, hs1, hs2⟩ := addFloor_err toVal_one' ha (w + 8) (by linarith)
  obtain ⟨d, hd, hd1, hd2⟩ := subCeiling_err toVal_one' ha (w + 8) (by linarith)
  exact atanhOfArg_spec hw ha0 ha1 hs hs0 hs1 hs2 hd hd1 hd2

/-- `atanhApprox neg` as a pair of `Roundable`s bracketing `atanh x`. -/
theorem atanhApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : |xv| < 1) {neg : Bool} (hneg : neg = true ↔ xv < 0) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (atanhApprox neg x w).1 lv ∧ Rounds (atanhApprox neg x w).2 hv ∧
      lv ≤ Real.artanh xv ∧ Real.artanh xv ≤ hv ∧ hv - lv ≤ atanhEps |xv| w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := atanhBracket_spec habs (abs_nonneg xv) hx1 hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  rw [atanh_abs_eq hneg] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `atanh x` is irrational for a finite float `0 < |x| < 1`. -/
theorem irrational_atanh_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) : Irrational (Real.artanh xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  rw [hq] at hx0 hx1 ⊢
  exact irrational_artanh_rat (by exact_mod_cast hx0) hx1

/-- The Ziv certificate for `atanh x`, `x` a finite float with `0 < |x| < 1`. -/
theorem atanhApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) (hx1 : |xv| < 1)
    (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (atanhApprox neg x (w₀ * 2 ^ f)).1
      (atanhApprox neg x (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (atanhApprox neg x)
    (irrational_atanh_of_toVal hx hx0 hx1) (atanhEps |xv|) (tendsto_atanhEps _) 64
    (fun _ hw => atanhApprox_spec hx hx1 hneg hw) w₀ hw₀

/-! ### Rationals -/

/-- A rational with `¬ den ≤ num` is below `1` in absolute value. -/
theorem abs_toRat_lt_one_of (q : AzRat) (h1 : ¬ q.den ≤ q.num) :
    |((AzRat.toRat q : ℚ) : ℝ)| < 1 :=
  not_le.mp fun h => h1 ((one_le_abs_toRat_iff q).mpr h)

/-- **`atanhRatBracket q w` encloses `atanh |q|`** for a rational `|q| < 1`. -/
theorem atanhRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat)
    (hq1 : |((AzRat.toRat q : ℚ) : ℝ)| < 1) :
    IsEnclW (atanhRatBracket q w) (Real.artanh |((AzRat.toRat q : ℚ) : ℝ)|)
      (atanhEps |((AzRat.toRat q : ℚ) : ℝ)| w) := by
  have : NeZero (w + 8) := ⟨by omega⟩
  set A := |((AzRat.toRat q : ℚ) : ℝ)| with hAdef
  have hA0 : 0 ≤ A := abs_nonneg _
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = A := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  have hp : ((AzRat.toRat (1 + q.abs) : ℚ) : ℝ) = 1 + A := by
    rw [AzRat.toRat_add, AzRat.toRat_one]
    push_cast
    rw [habs]
  have hm : ((AzRat.toRat (1 - q.abs) : ℚ) : ℝ) = 1 - A := by
    rw [AzRat.toRat_sub, AzRat.toRat_one]
    push_cast
    rw [habs]
  have hη : (1 / 2 : ℝ) ^ (w + 8) ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ (w + 8) ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  obtain ⟨sl, hsl, hsl1, hsl2⟩ := ofAzRatRound_floor_abs (1 + q.abs) (w + 8)
  obtain ⟨dl, hdl, hdl1, hdl2⟩ := ofAzRatRound_ceiling_abs (1 - q.abs) (w + 8)
  rw [hp] at hsl1 hsl2
  rw [hm] at hdl1 hdl2
  rw [abs_of_pos (by linarith)] at hsl2
  rw [abs_of_pos (by linarith)] at hdl2
  have hsl0 : 0 ≤ sl := by nlinarith
  exact atanhOfArg_spec hw hA0 hq1 hsl hsl0 hsl1 hsl2 hdl hdl1 hdl2

/-- `atanhRatApprox` as a pair of `Roundable`s bracketing `atanh q`. -/
theorem atanhRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0)
    (hq1 : |((AzRat.toRat q : ℚ) : ℝ)| < 1) :
    ∃ lv hv : ℝ, Rounds (atanhRatApprox q w).1 lv ∧ Rounds (atanhRatApprox q w).2 hv ∧
      lv ≤ Real.artanh (AzRat.toRat q : ℝ) ∧ Real.artanh (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ atanhEps |((AzRat.toRat q : ℚ) : ℝ)| w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := atanhRatBracket_spec hw q hq1
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec (!q.sign) hlo hhi h1 h2
  rw [atanh_abs_eq (toRat_neg_iff q h0)] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `atanh q` is irrational for a rational `0 < |q| < 1`. -/
theorem irrational_atanh_toRat (q : AzRat) (h0 : q.num ≠ 0)
    (hq1 : |((AzRat.toRat q : ℚ) : ℝ)| < 1) : Irrational (Real.artanh (AzRat.toRat q : ℝ)) :=
  irrational_artanh_rat (q := AzRat.toRat q)
    (fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp (by rw [h, Rat.cast_zero]))) hq1

/-- The Ziv certificate for `atanh q`. -/
theorem atanhRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (hq1 : |((AzRat.toRat q : ℚ) : ℝ)| < 1) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (atanhRatApprox q (w₀ * 2 ^ f)).1
      (atanhRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (atanhRatApprox q)
    (irrational_atanh_toRat q h0 hq1) (atanhEps |((AzRat.toRat q : ℚ) : ℝ)|)
    (tendsto_atanhEps _) 64 (fun _ hw => atanhRatApprox_spec hw q h0 hq1) w₀ hw₀

/-! ### Tiny arguments -/

/-- `a < atanh a ≤ a + a³` for `0 < a ≤ 1/4`. -/
theorem artanh_tiny_bounds {a : ℝ} (h0 : 0 < a) (h1 : a ≤ 1 / 4) :
    a < Real.artanh a ∧ Real.artanh a ≤ a + a ^ 3 := by
  have hmem : a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  constructor
  · have hb0 : 0 < Real.artanh a := artanh_pos ⟨h0, by linarith⟩
    have := tanh_lt_self hb0
    rwa [tanh_artanh hmem] at this
  · have habs : |a| < 1 := by rw [abs_of_pos h0]; linarith
    have habs' : |-a| < 1 := by rwa [abs_neg]
    have s1 := abs_log_sub_add_sum_range_le habs 3
    have s2 := abs_log_sub_add_sum_range_le habs' 3
    rw [abs_neg] at s2
    rw [abs_of_pos h0] at s1 s2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at s1 s2
    norm_num at s1 s2
    have hE : a ^ 4 / (1 - a) ≤ a ^ 3 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      have ha3 : 0 ≤ a ^ 3 := by positivity
      have : a ^ 4 = a ^ 3 * a := by ring
      nlinarith
    obtain ⟨l1, u1⟩ := abs_le.mp s1
    obtain ⟨l2, u2⟩ := abs_le.mp s2
    have hart : Real.artanh a = 1 / 2 * Real.log ((1 + a) / (1 - a)) :=
      artanh_eq_half_log ⟨by linarith, by linarith⟩
    rw [hart, Real.log_div (by linarith) (by linarith)]
    have ha3 : 0 ≤ a ^ 3 := by positivity
    linarith

/-- The function to which the tiny-argument test of the tangent is applied: `atanh` on
`[−1/4, 1/4]`, continued by `x + x³`. -/
noncomputable def atanhTinyFn (x : ℝ) : ℝ := if |x| ≤ 1 / 4 then Real.artanh x else x + x ^ 3

theorem atanhTinyFn_neg (x : ℝ) : atanhTinyFn (-x) = -atanhTinyFn x := by
  unfold atanhTinyFn
  rw [abs_neg]
  split_ifs
  · exact artanh_neg' x
  · ring

theorem atanhTinyFn_bounds (a : ℝ) (h0 : 0 < a) (_h1 : a ≤ 1) :
    a < atanhTinyFn a ∧ atanhTinyFn a ≤ a + a ^ 3 := by
  unfold atanhTinyFn
  rw [abs_of_pos h0]
  split_ifs with h
  · exact artanh_tiny_bounds h0 h
  · exact ⟨by have : 0 < a ^ 3 := by positivity
              linarith, le_rfl⟩

/-- `2^e ≤ 1/4` for an exponent `e ≤ −2`. -/
theorem two_zpow_le_quarter {e : AzInt} (hs : e.sign = false) (he : 2 ≤ e.abs.toNat) :
    (2 : ℝ) ^ e.toInt ≤ 1 / 4 := by
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [htoInt, hs]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
  calc (1 / 2 : ℝ) ^ e.abs.toNat ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) he
    _ = 1 / 4 := by norm_num

/-- The tiny-argument path of the tangent answers with the rounding of `atanh x`. -/
theorem atanhTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : tanTiny? s (finite s e q m hv) e q p mode = some r) :
    r = roundVal p mode (some ((Real.artanh (finiteVal s e m) : ℝ) : EReal)) := by
  have hr := tanTiny?_eq_of atanhTinyFn_neg atanhTinyFn_bounds hv p mode h
  have hc : e.sign = false ∧ max p q + zivGuardBits + 8 ≤ e.abs.toNat := by
    unfold tanTiny? at h
    dsimp only at h
    by_contra hc
    rw [ite_eq_right hc] at h
    cases h
  have hlt := (abs_finiteVal_bounds s e hv).2
  have hq := two_zpow_le_quarter hc.1 (by omega)
  have : atanhTinyFn (finiteVal s e m) = Real.artanh (finiteVal s e m) := by
    unfold atanhTinyFn
    rw [ite_eq_left (by linarith)]
  rwa [this] at hr

/-- The tiny-argument path of the tangent answers with the rounding of `atanh q`. -/
theorem atanhTinyRat?_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (hT : tanTinyRat? q p mode = some r) :
    r = roundVal p mode (some ((Real.artanh (AzRat.toRat q : ℝ) : ℝ) : EReal)) := by
  have hr := tanTinyRat?_eq_of atanhTinyFn_neg atanhTinyFn_bounds q h0 hT
  have hc : (ratExpBound q).sign = false ∧ p + zivGuardBits + 8 ≤ (ratExpBound q).abs.toNat := by
    unfold tanTinyRat? tanTinyCore? at hT
    dsimp only at hT
    by_contra hc
    rw [ite_eq_right hc] at hT
    cases hT
  have hlt : |((AzRat.toRat q : ℚ) : ℝ)| < (2 : ℝ) ^ (ratExpBound q).toInt :=
    lt_of_lt_of_le (abs_toRat_lt_two_zpow q) (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hq := two_zpow_le_quarter hc.1 (by omega)
  have : atanhTinyFn (AzRat.toRat q : ℝ) = Real.artanh (AzRat.toRat q : ℝ) := by
    unfold atanhTinyFn
    rw [ite_eq_left (by linarith)]
  rwa [this] at hr

end Azurite.AzFloat
