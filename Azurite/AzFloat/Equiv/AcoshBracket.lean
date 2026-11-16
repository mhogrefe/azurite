/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcoshBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.Equiv.LnBracket
import Azurite.AzFloat.Equiv.AsecRat
import Azurite.AzFloat.Equiv.AtanRatWithPeriodBracket
import Azurite.AzRat.Equiv.Add
import Azurite.AzRat.Equiv.Sub
import Azurite.Transcendental.Sinh

/-!
# Equivalence: the brackets of `acosh x` and `acosh q`

`acoshArg_lower`, `acoshArg_bounds` (the real arithmetic of the rounded-down argument
`x + √((x − 1)(x + 1))`), `acoshArg_spec`, `acoshLn_spec` (the bracket from floats just below
`x`, `x − 1`, `x + 1`), `acoshBracket_spec`, `acoshApprox_spec`, `irrational_acosh_of_toVal`,
`acoshApprox_isSome_exists`, `one_lt_of_acosh_cond`, and the rational versions
`acoshRatBracket_spec`, `acoshRatApprox_spec`, `irrational_acosh_toRat`,
`acoshRatApprox_isSome_exists`, `one_lt_toRat_of_acosh_cond`, `toRat_lt_one_of_not_acosh_cond`.
-/

open Real

namespace Azurite.AzFloat

/-- The lower chain of `acoshArg`: with every step rounded down by a factor `c ∈ (0, 1]`, the
result is at least `c⁴ (X + √(X² − 1))`. -/
theorem acoshArg_lower {X xl dl sl m r y c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hX : 1 ≤ X)
    (hxl : c * X ≤ xl) (hdl0 : 0 ≤ dl) (hdl : c * (X - 1) ≤ dl) (hsl : c * (X + 1) ≤ sl)
    (hm : c * (dl * sl) ≤ m) (hr : c * √m ≤ r) (hy : c * (xl + r) ≤ y) :
    c * c * c * c * (X + √(X ^ 2 - 1)) ≤ y := by
  have hP0 : 0 ≤ X ^ 2 - 1 := by nlinarith
  have hRsq : √(X ^ 2 - 1) ^ 2 = X ^ 2 - 1 := sq_sqrt hP0
  have hR0 : 0 ≤ √(X ^ 2 - 1) := sqrt_nonneg _
  have hcc1 : c * c ≤ 1 := by nlinarith
  have hprod : (c * (X - 1)) * (c * (X + 1)) ≤ dl * sl :=
    mul_le_mul hdl hsl (by positivity) hdl0
  have hm' : c * ((c * (X - 1)) * (c * (X + 1))) ≤ m :=
    (mul_le_mul_of_nonneg_left hprod hc0.le).trans hm
  have hs' : c * c * c * c * (X ^ 2 - 1) ≤ m := by
    have e : c * ((c * (X - 1)) * (c * (X + 1))) = c * c * c * (X ^ 2 - 1) := by ring
    rw [e] at hm'
    have h3 : 0 ≤ c * c * c * (X ^ 2 - 1) := by positivity
    have h4 : c * (c * c * c * (X ^ 2 - 1)) ≤ 1 * (c * c * c * (X ^ 2 - 1)) :=
      mul_le_mul_of_nonneg_right hc1 h3
    have e2 : c * (c * c * c * (X ^ 2 - 1)) = c * c * c * c * (X ^ 2 - 1) := by ring
    linarith
  have hsq : c * c * √(X ^ 2 - 1) ≤ √m := by
    have h1 : (c * c * √(X ^ 2 - 1)) ^ 2 ≤ m := by
      have : (c * c * √(X ^ 2 - 1)) ^ 2 = c * c * c * c * √(X ^ 2 - 1) ^ 2 := by ring
      rw [this, hRsq]
      exact hs'
    exact (le_abs_self _).trans (abs_le_sqrt h1)
  have hr' : c * (c * c * √(X ^ 2 - 1)) ≤ r := (mul_le_mul_of_nonneg_left hsq hc0.le).trans hr
  have hX' : c * c * c * X ≤ c * X := by
    have := mul_le_mul_of_nonneg_right hcc1 (mul_nonneg hc0.le (by linarith : (0 : ℝ) ≤ X))
    have e : c * c * (c * X) = c * c * c * X := by ring
    linarith
  have hsum : c * c * c * (X + √(X ^ 2 - 1)) ≤ xl + r := by
    have e : c * c * c * (X + √(X ^ 2 - 1)) = c * c * c * X + c * (c * c * √(X ^ 2 - 1)) := by
      ring
    rw [e]
    linarith
  have := (mul_le_mul_of_nonneg_left hsum hc0.le).trans hy
  have e : c * (c * c * c * (X + √(X ^ 2 - 1))) = c * c * c * c * (X + √(X ^ 2 - 1)) := by ring
  linarith

/-- The real arithmetic of `acoshArg`: with every step rounded down within a relative `2η`,
the result is within a relative `8η` below `X + √(X² − 1)`. -/
theorem acoshArg_bounds {X xl dl sl m r y η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 64) (hX : 1 ≤ X)
    (hxl1 : xl ≤ X) (hxl2 : X ≤ xl + 2 * X * η)
    (hdl0 : 0 ≤ dl) (hdl1 : dl ≤ X - 1) (hdl2 : X - 1 ≤ dl + 2 * (X - 1) * η)
    (hsl0 : 0 ≤ sl) (hsl1 : sl ≤ X + 1) (hsl2 : X + 1 ≤ sl + 2 * (X + 1) * η)
    (hm1 : m ≤ dl * sl) (hm2 : dl * sl ≤ m + 2 * (dl * sl) * η)
    (hr1 : r ≤ √m) (hr2 : √m ≤ r + 2 * √m * η)
    (hy1 : y ≤ xl + r) (hy2 : xl + r ≤ y + 2 * (xl + r) * η) :
    y ≤ X + √(X ^ 2 - 1) ∧ X + √(X ^ 2 - 1) ≤ y + 8 * (X + √(X ^ 2 - 1)) * η := by
  have hR0 : 0 ≤ √(X ^ 2 - 1) := sqrt_nonneg _
  have hc0 : 0 < 1 - 2 * η := by linarith
  have g1 : (1 - 2 * η) * X ≤ xl := by linarith
  have g2 : (1 - 2 * η) * (X - 1) ≤ dl := by linarith
  have g3 : (1 - 2 * η) * (X + 1) ≤ sl := by linarith
  have g4 : (1 - 2 * η) * (dl * sl) ≤ m := by linarith
  have g5 : (1 - 2 * η) * √m ≤ r := by linarith
  have g6 : (1 - 2 * η) * (xl + r) ≤ y := by linarith
  have hlow := acoshArg_lower hc0 (by linarith) hX g1 hdl0 g2 g3 g4 g5 g6
  have hbern : 1 - 8 * η ≤ (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) := by
    have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(2 * η)) 4
    have e : (1 + -(2 * η)) ^ 4 = (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) := by
      ring
    rw [e] at h
    push_cast at h
    linarith
  have hV0 : 0 ≤ X + √(X ^ 2 - 1) := by positivity
  have hfin : (1 - 8 * η) * (X + √(X ^ 2 - 1)) ≤ y :=
    (mul_le_mul_of_nonneg_right hbern hV0).trans hlow
  have hmle : m ≤ X ^ 2 - 1 := by
    have : dl * sl ≤ (X - 1) * (X + 1) := mul_le_mul hdl1 hsl1 hsl0 (by linarith)
    have e : (X - 1) * (X + 1) = X ^ 2 - 1 := by ring
    linarith
  have hrle : r ≤ √(X ^ 2 - 1) := hr1.trans (sqrt_le_sqrt hmle)
  constructor
  · linarith
  · have e : (1 - 8 * η) * (X + √(X ^ 2 - 1))
        = (X + √(X ^ 2 - 1)) - 8 * (X + √(X ^ 2 - 1)) * η := by ring
    linarith

/-- The width bound of the brackets of `acosh x`. -/
noncomputable def acoshEps (X : ℝ) (w : ℕ) : ℝ :=
  lnRatEps (⌊2 * |Real.arcosh X|⌋₊ + 2) |Real.arcosh X| w

theorem tendsto_acoshEps (X : ℝ) : Filter.Tendsto (acoshEps X) Filter.atTop (nhds 0) :=
  tendsto_lnRatEps _ _

/-- **The logarithm of `acoshArg` encloses `acosh X`**, `X ≥ 1`, for floats `xl`, `dl`, `sl`
just below `X`, `X − 1`, `X + 1`. -/
theorem acoshLn_spec {xl dl sl : AzFloat} {xlv dlv slv X : ℝ} {w : ℕ} (hw : 64 ≤ w)
    (hX : 1 ≤ X) (hxl : xl.toVal = some (xlv : EReal)) (hxl1 : xlv ≤ X)
    (hxl2 : X ≤ xlv + 2 * X * (1 / 2 : ℝ) ^ (w + 8))
    (hdl : dl.toVal = some (dlv : EReal)) (hdl0 : 0 ≤ dlv) (hdl1 : dlv ≤ X - 1)
    (hdl2 : X - 1 ≤ dlv + 2 * (X - 1) * (1 / 2 : ℝ) ^ (w + 8))
    (hsl : sl.toVal = some (slv : EReal)) (hsl0 : 0 ≤ slv) (hsl1 : slv ≤ X + 1)
    (hsl2 : X + 1 ≤ slv + 2 * (X + 1) * (1 / 2 : ℝ) ^ (w + 8)) :
    IsEnclW (lnFloorBracket (acoshArg xl dl sl (w + 8)) w) (Real.arcosh X) (acoshEps X w) := by
  have : NeZero (w + 8) := ⟨by omega⟩
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 8) := by positivity
  have hη : (1 / 2 : ℝ) ^ (w + 8) ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ (w + 8) ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  have hxl0 : 0 ≤ xlv := by nlinarith
  obtain ⟨m, hm, hm0, hm1, hm2⟩ := mulFloor_err hdl hsl (w + 8) (mul_nonneg hdl0 hsl0)
  obtain ⟨r, hr, hr0, hr1, hr2⟩ := sqrtFloor_err hm hm0 (w + 8)
  obtain ⟨y, hy, -, hy1, hy2⟩ := addFloor_err hxl hr (w + 8) (by linarith)
  obtain ⟨b1, b2⟩ := acoshArg_bounds hη0 hη hX hxl1 hxl2 hdl0 hdl1 hdl2 hsl0 hsl1 hsl2
    hm1 hm2 hr1 hr2 hy1 hy2
  have hV : 0 < X + √(X ^ 2 - 1) := by
    have : 0 ≤ √(X ^ 2 - 1) := sqrt_nonneg _
    linarith
  have hpw : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  have hy2' : X + √(X ^ 2 - 1) ≤ y + 2 * (X + √(X ^ 2 - 1)) * (1 / 2 : ℝ) ^ w := by
    rw [hpw] at b2
    have : 0 ≤ (X + √(X ^ 2 - 1)) * (1 / 2 : ℝ) ^ w := by positivity
    linarith
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := lnFloorBracket_spec hw hy hV b1 hy2'
  exact ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩

/-! ### Floats -/

/-- **`acoshBracket x w` encloses `acosh x`** for a float `x ≥ 1`. -/
theorem acoshBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 ≤ xv) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (acoshBracket x w) (Real.arcosh xv) (acoshEps xv w) := by
  have : NeZero (w + 8) := ⟨by omega⟩
  obtain ⟨d, hd, hd0, hd1, hd2⟩ := subFloor_err hx toVal_one' (w + 8) (by linarith)
  obtain ⟨s, hs, hs0, hs1, hs2⟩ := addFloor_err hx toVal_one' (w + 8) (by linarith)
  exact acoshLn_spec hw hx1 hx le_rfl (by
    have : 0 ≤ 2 * xv * (1 / 2 : ℝ) ^ (w + 8) := by positivity
    linarith) hd hd0 hd1 hd2 hs hs0 hs1 hs2

/-- `acoshApprox` as a pair of `Roundable`s bracketing `acosh x`. -/
theorem acoshApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 ≤ xv) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (acoshApprox x w).1 lv ∧ Rounds (acoshApprox x w).2 hv ∧
      lv ≤ Real.arcosh xv ∧ Real.arcosh xv ≤ hv ∧ hv - lv ≤ acoshEps xv w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := acoshBracket_spec hx hx1 hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `acosh x` is irrational for a finite float `x > 1`. -/
theorem irrational_acosh_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < xv) : Irrational (Real.arcosh xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  rw [hq] at hx1 ⊢
  exact irrational_arcosh_rat (by exact_mod_cast hx1)

/-- The Ziv certificate for `acosh x`, `x` a finite float above `1`. -/
theorem acoshApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : 1 < xv) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acoshApprox x (w₀ * 2 ^ f)).1
      (acoshApprox x (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (acoshApprox x)
    (irrational_acosh_of_toVal hx hx1) (acoshEps xv) (tendsto_acoshEps _) 64
    (fun _ hw => acoshApprox_spec hx hx1.le hw) w₀ hw₀

/-- A positive float of positive exponent that is not `1` is above `1`. -/
theorem one_lt_of_acosh_cond {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hs : s = true)
    (h1 : ¬ eqIEEE (finite s e q m hv) one = true) (he : e.sign = true ∧ e.abs.toNat ≠ 0) :
    1 < finiteVal s e m := by
  have hpos : 0 < finiteVal s e m := (finiteVal_sign_iff s e hv).mp hs
  have hb := (abs_finiteVal_bounds s e hv).1
  have hne : |finiteVal s e m| ≠ 1 := fun h => by
    rw [abs_of_pos hpos] at h
    exact h1 ((eqIEEE_iff _ _).mpr ⟨_, toVal_finite s e q m hv, by rw [h]; exact toVal_one'⟩)
  have := one_lt_abs_of_exponent hb he hne
  rwa [abs_of_pos hpos] at this

/-! ### Rationals -/

/-- A positive rational with `den ≤ num`, `num ≠ den` is above `1`. -/
theorem one_lt_toRat_of_acosh_cond (q : AzRat) (hc : q.sign = true ∧ q.den ≤ q.num)
    (h1 : q.num ≠ q.den) : 1 < ((AzRat.toRat q : ℚ) : ℝ) := by
  have habs := (one_le_abs_toRat_iff q).mp hc.2
  have h0 : q.num ≠ 0 := fun h => by
    rw [coe_toRat_eq_zero_of_num_eq_zero q h, abs_zero] at habs
    linarith
  have hpos := (toRat_sign_iff q h0).mp hc.1
  rw [abs_of_pos hpos] at habs
  refine lt_of_le_of_ne habs fun h => h1 ((abs_toRat_eq_one_iff q).mp ?_)
  rw [abs_of_pos hpos]
  exact h.symm

/-- A rational failing the test `sign ∧ den ≤ num` is below `1`. -/
theorem toRat_lt_one_of_not_acosh_cond (q : AzRat) (hc : ¬ (q.sign = true ∧ q.den ≤ q.num)) :
    ((AzRat.toRat q : ℚ) : ℝ) < 1 := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < ((AzRat.toRat q : ℚ) : ℝ) := by linarith
  have h0 : q.num ≠ 0 := fun h => by
    rw [coe_toRat_eq_zero_of_num_eq_zero q h] at hpos
    exact lt_irrefl _ hpos
  refine hc ⟨(toRat_sign_iff q h0).mpr hpos, (one_le_abs_toRat_iff q).mpr ?_⟩
  rw [abs_of_pos hpos]
  exact hcon

/-- **`acoshRatBracket q w` encloses `acosh q`** for a rational `q ≥ 1`. -/
theorem acoshRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat)
    (hq1 : 1 ≤ ((AzRat.toRat q : ℚ) : ℝ)) :
    IsEnclW (acoshRatBracket q w) (Real.arcosh (AzRat.toRat q : ℝ))
      (acoshEps (AzRat.toRat q : ℝ) w) := by
  have : NeZero (w + 8) := ⟨by omega⟩
  set X := ((AzRat.toRat q : ℚ) : ℝ) with hXdef
  have hm : ((AzRat.toRat (q - 1) : ℚ) : ℝ) = X - 1 := by
    rw [AzRat.toRat_sub, AzRat.toRat_one]
    push_cast
    rfl
  have hp : ((AzRat.toRat (q + 1) : ℚ) : ℝ) = X + 1 := by
    rw [AzRat.toRat_add, AzRat.toRat_one]
    push_cast
    rfl
  have hη : (1 / 2 : ℝ) ^ (w + 8) ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ (w + 8) ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  obtain ⟨xl, hxl, hxl1, hxl2⟩ := ofAzRatRound_floor_abs q (w + 8)
  obtain ⟨dl, hdl, hdl1, hdl2⟩ := ofAzRatRound_floor_abs (q - 1) (w + 8)
  obtain ⟨sl, hsl, hsl1, hsl2⟩ := ofAzRatRound_floor_abs (q + 1) (w + 8)
  rw [hm] at hdl1 hdl2
  rw [hp] at hsl1 hsl2
  rw [← hXdef, abs_of_pos (by linarith)] at hxl2
  rw [abs_of_nonneg (by linarith)] at hdl2
  rw [abs_of_pos (by linarith)] at hsl2
  have hdl0 : 0 ≤ dl := by nlinarith
  have hsl0 : 0 ≤ sl := by nlinarith
  exact acoshLn_spec hw hq1 hxl hxl1 hxl2 hdl hdl0 hdl1 hdl2 hsl hsl0 hsl1 hsl2

/-- `acoshRatApprox` as a pair of `Roundable`s bracketing `acosh q`. -/
theorem acoshRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat)
    (hq1 : 1 ≤ ((AzRat.toRat q : ℚ) : ℝ)) :
    ∃ lv hv : ℝ, Rounds (acoshRatApprox q w).1 lv ∧ Rounds (acoshRatApprox q w).2 hv ∧
      lv ≤ Real.arcosh (AzRat.toRat q : ℝ) ∧ Real.arcosh (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ acoshEps (AzRat.toRat q : ℝ) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := acoshRatBracket_spec hw q hq1
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `acosh q` is irrational for a rational `q > 1`. -/
theorem irrational_acosh_toRat (q : AzRat) (hq1 : 1 < ((AzRat.toRat q : ℚ) : ℝ)) :
    Irrational (Real.arcosh (AzRat.toRat q : ℝ)) :=
  irrational_arcosh_rat (q := AzRat.toRat q) (by exact_mod_cast hq1)

/-- The Ziv certificate for `acosh q`. -/
theorem acoshRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (hq1 : 1 < ((AzRat.toRat q : ℚ) : ℝ)) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acoshRatApprox q (w₀ * 2 ^ f)).1
      (acoshRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (acoshRatApprox q)
    (irrational_acosh_toRat q hq1) (acoshEps (AzRat.toRat q : ℝ)) (tendsto_acoshEps _) 64
    (fun _ hw => acoshRatApprox_spec hw q hq1.le) w₀ hw₀

end Azurite.AzFloat
