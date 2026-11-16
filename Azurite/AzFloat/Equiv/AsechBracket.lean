/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsechBracket
import Azurite.AzFloat.Equiv.AcoshBracket
import Azurite.AzFloat.Equiv.AsinBracket

/-!
# Equivalence: the bracket of `asech x`

`arcosh_inv_eq_log` (`acosh (1/x) = ln ((1 + √(1 − x²))/x)`), `asechArg_lower`,
`asechArg_bounds` (the real arithmetic of the rounded-down argument), `asechArg_spec`,
`asechBracket_spec`, `asechApprox_spec`, `irrational_asech_of_toVal`,
`asechApprox_isSome_exists`.
-/

open Real

namespace Azurite.AzFloat

/-- `acosh (1/x) = ln ((1 + √(1 − x²))/x)` for `0 < x ≤ 1`. -/
theorem arcosh_inv_eq_log {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) :
    Real.arcosh x⁻¹ = Real.log ((1 + √(1 - x ^ 2)) / x) := by
  unfold Real.arcosh
  congr 1
  have e : x⁻¹ ^ 2 - 1 = (1 - x ^ 2) / x ^ 2 := by
    field_simp
  rw [e, sqrt_div (by nlinarith), sqrt_sq h0.le]
  field_simp

/-- The lower chain of `asechArg`: with every step rounded down by a factor `c ∈ (0, 1]`, the
result is at least `c⁵ (1 + √(1 − X²))/X`. -/
theorem asechArg_lower {X dl sl m r n y c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hX0 : 0 < X)
    (hX1 : X ≤ 1) (hdl0 : 0 ≤ dl) (hdl : c * (1 - X) ≤ dl) (hsl : c * (1 + X) ≤ sl)
    (hm : c * (dl * sl) ≤ m) (hr : c * √m ≤ r) (hn : c * (1 + r) ≤ n)
    (hy : c * (n / X) ≤ y) :
    c * c * c * c * c * ((1 + √(1 - X ^ 2)) / X) ≤ y := by
  have hP0 : 0 ≤ 1 - X ^ 2 := by nlinarith
  have hRsq : √(1 - X ^ 2) ^ 2 = 1 - X ^ 2 := sq_sqrt hP0
  have hR0 : 0 ≤ √(1 - X ^ 2) := sqrt_nonneg _
  have hcc1 : c * c ≤ 1 := by nlinarith
  have hccc1 : c * c * c ≤ 1 := by nlinarith
  have hprod : (c * (1 - X)) * (c * (1 + X)) ≤ dl * sl :=
    mul_le_mul hdl hsl (by positivity) hdl0
  have hm' : c * ((c * (1 - X)) * (c * (1 + X))) ≤ m :=
    (mul_le_mul_of_nonneg_left hprod hc0.le).trans hm
  have hs' : c * c * c * c * (1 - X ^ 2) ≤ m := by
    have e : c * ((c * (1 - X)) * (c * (1 + X))) = c * c * c * (1 - X ^ 2) := by ring
    rw [e] at hm'
    have h3 : 0 ≤ c * c * c * (1 - X ^ 2) := by positivity
    have h4 : c * (c * c * c * (1 - X ^ 2)) ≤ 1 * (c * c * c * (1 - X ^ 2)) :=
      mul_le_mul_of_nonneg_right hc1 h3
    have e2 : c * (c * c * c * (1 - X ^ 2)) = c * c * c * c * (1 - X ^ 2) := by ring
    linarith
  have hsq : c * c * √(1 - X ^ 2) ≤ √m := by
    have h1 : (c * c * √(1 - X ^ 2)) ^ 2 ≤ m := by
      have : (c * c * √(1 - X ^ 2)) ^ 2 = c * c * c * c * √(1 - X ^ 2) ^ 2 := by ring
      rw [this, hRsq]
      exact hs'
    exact (le_abs_self _).trans (abs_le_sqrt h1)
  have hr' : c * (c * c * √(1 - X ^ 2)) ≤ r := (mul_le_mul_of_nonneg_left hsq hc0.le).trans hr
  have hsum : c * c * c * (1 + √(1 - X ^ 2)) ≤ 1 + r := by
    have e : c * c * c * (1 + √(1 - X ^ 2)) = c * c * c + c * (c * c * √(1 - X ^ 2)) := by ring
    rw [e]
    linarith
  have hn' : c * (c * c * c * (1 + √(1 - X ^ 2))) ≤ n :=
    (mul_le_mul_of_nonneg_left hsum hc0.le).trans hn
  have hq : c * (c * c * c * (1 + √(1 - X ^ 2))) / X ≤ n / X :=
    div_le_div_of_nonneg_right hn' hX0.le
  have hfin := (mul_le_mul_of_nonneg_left hq hc0.le).trans hy
  have e : c * (c * (c * c * c * (1 + √(1 - X ^ 2))) / X)
      = c * c * c * c * c * ((1 + √(1 - X ^ 2)) / X) := by ring
  rw [e] at hfin
  exact hfin

/-- The real arithmetic of `asechArg`: with every step rounded down within a relative `2η`,
the result is within a relative `10η` below `(1 + √(1 − X²))/X`. -/
theorem asechArg_bounds {X dl sl m r n y η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 64) (hX0 : 0 < X)
    (hX1 : X ≤ 1)
    (hdl0 : 0 ≤ dl) (hdl1 : dl ≤ 1 - X) (hdl2 : 1 - X ≤ dl + 2 * (1 - X) * η)
    (hsl0 : 0 ≤ sl) (hsl1 : sl ≤ 1 + X) (hsl2 : 1 + X ≤ sl + 2 * (1 + X) * η)
    (hm1 : m ≤ dl * sl) (hm2 : dl * sl ≤ m + 2 * (dl * sl) * η)
    (hr1 : r ≤ √m) (hr2 : √m ≤ r + 2 * √m * η)
    (hn1 : n ≤ 1 + r) (hn2 : 1 + r ≤ n + 2 * (1 + r) * η)
    (hy1 : y ≤ n / X) (hy2 : n / X ≤ y + 2 * (n / X) * η) :
    y ≤ (1 + √(1 - X ^ 2)) / X ∧
      (1 + √(1 - X ^ 2)) / X ≤ y + 10 * ((1 + √(1 - X ^ 2)) / X) * η := by
  have hR0 : 0 ≤ √(1 - X ^ 2) := sqrt_nonneg _
  have hc0 : 0 < 1 - 2 * η := by linarith
  have g2 : (1 - 2 * η) * (1 - X) ≤ dl := by linarith
  have g3 : (1 - 2 * η) * (1 + X) ≤ sl := by linarith
  have g4 : (1 - 2 * η) * (dl * sl) ≤ m := by linarith
  have g5 : (1 - 2 * η) * √m ≤ r := by linarith
  have g6 : (1 - 2 * η) * (1 + r) ≤ n := by linarith
  have g7 : (1 - 2 * η) * (n / X) ≤ y := by linarith
  have hlow := asechArg_lower hc0 (by linarith) hX0 hX1 hdl0 g2 g3 g4 g5 g6 g7
  have hbern : 1 - 10 * η
      ≤ (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) := by
    have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(2 * η)) 5
    have e : (1 + -(2 * η)) ^ 5
        = (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) := by ring
    rw [e] at h
    push_cast at h
    linarith
  have hV0 : 0 ≤ (1 + √(1 - X ^ 2)) / X := by positivity
  have hfin : (1 - 10 * η) * ((1 + √(1 - X ^ 2)) / X) ≤ y :=
    (mul_le_mul_of_nonneg_right hbern hV0).trans hlow
  have hmle : m ≤ 1 - X ^ 2 := by
    have : dl * sl ≤ (1 - X) * (1 + X) := mul_le_mul hdl1 hsl1 hsl0 (by linarith)
    have e : (1 - X) * (1 + X) = 1 - X ^ 2 := by ring
    linarith
  have hrle : r ≤ √(1 - X ^ 2) := hr1.trans (sqrt_le_sqrt hmle)
  have hup : n / X ≤ (1 + √(1 - X ^ 2)) / X := div_le_div_of_nonneg_right (by linarith) hX0.le
  constructor
  · linarith
  · have e : (1 - 10 * η) * ((1 + √(1 - X ^ 2)) / X)
        = (1 + √(1 - X ^ 2)) / X - 10 * ((1 + √(1 - X ^ 2)) / X) * η := by ring
    linarith

/-- **`asechArg x W` is just below `(1 + √(1 − x²))/x`**, for a float `0 < x ≤ 1`. -/
theorem asechArg_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : 0 < xv) (hx1 : xv ≤ 1) {W : ℕ} (hW : 6 ≤ W) :
    ∃ y : ℝ, (asechArg x W).toVal = some (y : EReal) ∧ y ≤ (1 + √(1 - xv ^ 2)) / xv ∧
      (1 + √(1 - xv ^ 2)) / xv
        ≤ y + 10 * ((1 + √(1 - xv ^ 2)) / xv) * (1 / 2 : ℝ) ^ W := by
  have : NeZero W := ⟨by omega⟩
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hη : (1 / 2 : ℝ) ^ W ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hW
      _ = 1 / 64 := by norm_num
  obtain ⟨dl, hdl, hdl0, hdl1, hdl2⟩ := subFloor_err toVal_one' hx W (by linarith)
  obtain ⟨sl, hsl, hsl0, hsl1, hsl2⟩ := addFloor_err toVal_one' hx W (by linarith)
  obtain ⟨m, hm, hm0, hm1, hm2⟩ := mulFloor_err hdl hsl W (mul_nonneg hdl0 hsl0)
  obtain ⟨r, hr, hr0, hr1, hr2⟩ := sqrtFloor_err hm hm0 W
  obtain ⟨n, hn, hn0, hn1, hn2⟩ := addFloor_err toVal_one' hr W (by linarith)
  obtain ⟨y, hy, -, hy1, hy2⟩ := divFloor_err hn hx hx0 hn0 W
  exact ⟨y, hy, asechArg_bounds hη0 hη hx0 hx1 hdl0 hdl1 hdl2 hsl0 hsl1 hsl2 hm1 hm2 hr1 hr2
    hn1 hn2 hy1 hy2⟩

/-- **`asechBracket x w` encloses `asech x = acosh (1/x)`** for a float `0 < x ≤ 1`. -/
theorem asechBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : 0 < xv) (hx1 : xv ≤ 1) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (asechBracket x w) (Real.arcosh xv⁻¹) (acoshEps xv⁻¹ w) := by
  obtain ⟨y, hy, hy1, hy2⟩ := asechArg_spec hx hx0 hx1 (W := w + 8) (by omega)
  have hV : 0 < (1 + √(1 - xv ^ 2)) / xv := by
    have : 0 ≤ √(1 - xv ^ 2) := sqrt_nonneg _
    positivity
  have hpw : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  have hy2' : (1 + √(1 - xv ^ 2)) / xv
      ≤ y + 2 * ((1 + √(1 - xv ^ 2)) / xv) * (1 / 2 : ℝ) ^ w := by
    rw [hpw] at hy2
    have : 0 ≤ (1 + √(1 - xv ^ 2)) / xv * (1 / 2 : ℝ) ^ w := by positivity
    linarith
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := lnFloorBracket_spec hw hy hV hy1 hy2'
  rw [← arcosh_inv_eq_log hx0 hx1] at hlo hhi hwid
  exact ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩

/-- `asechApprox` as a pair of `Roundable`s bracketing `asech x`. -/
theorem asechApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : 0 < xv) (hx1 : xv ≤ 1) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (asechApprox x w).1 lv ∧ Rounds (asechApprox x w).2 hv ∧
      lv ≤ Real.arcosh xv⁻¹ ∧ Real.arcosh xv⁻¹ ≤ hv ∧ hv - lv ≤ acoshEps xv⁻¹ w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := asechBracket_spec hx hx0 hx1 hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `asech x` is irrational for a finite float `0 < x < 1`. -/
theorem irrational_asech_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : 0 < xv) (hx1 : xv < 1) : Irrational (Real.arcosh xv⁻¹) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  rw [hq] at hx0 hx1 ⊢
  rw [← Rat.cast_inv]
  refine irrational_arcosh_rat ?_
  have : (1 : ℝ) < ((q⁻¹ : ℚ) : ℝ) := by
    rw [Rat.cast_inv]
    exact (one_lt_inv₀ hx0).mpr hx1
  exact_mod_cast this

/-- The Ziv certificate for `asech x`, `x` a finite float with `0 < x < 1`. -/
theorem asechApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : 0 < xv) (hx1 : xv < 1)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (asechApprox x (w₀ * 2 ^ f)).1
      (asechApprox x (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (asechApprox x)
    (irrational_asech_of_toVal hx hx0 hx1) (acoshEps xv⁻¹) (tendsto_acoshEps _) 64
    (fun _ hw => asechApprox_spec hx hx0 hx1.le hw) w₀ hw₀

end Azurite.AzFloat
