/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotBracket
import Azurite.AzFloat.Equiv.AcscBracket
import Azurite.AzFloat.Equiv.AtanRatBracket
import Azurite.AzFloat.Equiv.Atan2Bracket

/-!
# Equivalence: the bracket of `arccot x`

`acotTinyEncl_spec`, `acotBracket_spec` (the enclosure of `arctan (1/|x|)`, nonnegative lower
end, width at most `2^(−w)`), `acotApprox_spec`, `irrational_acot_of_toVal`,
`acotApprox_isSome_exists` (the Ziv certificate), `acot_abs_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- **The enclosure for a huge argument**: for a float `a > 0` with `1/a ≤ 1/2` and
`1/a² ≤ 2^(−w−14)`, `acotTinyEncl a w` encloses `arctan (1/a)` with a nonnegative lower end and
width at most `2^(−w)`. -/
theorem acotTinyEncl_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) (hy1 : av⁻¹ ≤ 1 / 2) {w : ℕ} (hy2 : av⁻¹ ^ 2 ≤ (1 / 2 : ℝ) ^ (w + 14)) :
    IsEncl0W (acotTinyEncl a w) (arctan av⁻¹) ((1 / 2 : ℝ) ^ w) := by
  have : NeZero (w + 16) := ⟨by omega⟩
  set y := av⁻¹ with hy
  have hy0 : 0 < y := inv_pos.mpr ha0
  have hdiv : (1 : ℝ) / av = y := by rw [hy, one_div]
  set ε := (1 / 2 : ℝ) ^ (w + 16) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 65536 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (show 16 ≤ w + 16 by omega)
    rw [← hε] at this
    norm_num at this
    linarith
  have hη : (1 / 2 : ℝ) ^ (w + 14) = 4 * ε := by
    rw [hε]
    ring
  have hw : (1 / 2 : ℝ) ^ w = 65536 * ε := by
    rw [hε]
    ring
  rw [hη] at hy2
  -- the factor
  have hsh : (one <<< AzInt.ofInt (-((w : Int) + 14))).toVal = some ((4 * ε : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt, one_mul, ← hη,
      show (-((w : ℤ) + 14)) = -((w + 14 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      one_div, inv_pow]
  obtain ⟨cv, hc, hc1, hc2⟩ := subFloor_abs toVal_one' hsh (w + 16)
  rw [abs_of_pos (by linarith), ← hε] at hc2
  have hc6 : 1 - 6 * ε ≤ cv := by nlinarith
  have hcv0 : 0 ≤ cv := by linarith
  -- the quotients
  obtain ⟨l0, hl0, hl1, hl2⟩ := divFloor_abs toVal_one' ha ha0.ne' (w + 16)
  obtain ⟨u, hu, hu1, hu2⟩ := divCeiling_abs toVal_one' ha ha0.ne' (w + 16)
  rw [hdiv] at hl1 hl2 hu1 hu2
  rw [abs_of_pos hy0, ← hε] at hl2 hu2
  have hyε : 0 ≤ y * ε := by positivity
  have hyε1 : y * ε ≤ y / 65536 := by
    have := mul_le_mul_of_nonneg_left hε1 hy0.le
    linarith
  have hl00 : 0 ≤ l0 := by linarith
  obtain ⟨l, hl, hll1, hll2⟩ := mulFloor_abs hl0 hc (w + 16)
  rw [abs_of_nonneg (mul_nonneg hl00 hcv0), ← hε] at hll2
  have hprod0 : 0 ≤ l0 * cv := mul_nonneg hl00 hcv0
  have hprodle : l0 * cv ≤ y * (1 - 4 * ε) := mul_le_mul hl1 hc1 hcv0 hy0.le
  have hprodge : y - 8 * (y * ε) ≤ l0 * cv := by
    calc y - 8 * (y * ε) ≤ (y - 2 * y * ε) * (1 - 6 * ε) := by
          have : 0 ≤ (y * ε) * ε := by positivity
          nlinarith
      _ ≤ l0 * cv := mul_le_mul (by linarith) hc6 (by linarith) hl00
  have hprodε : (l0 * cv) * ε ≤ y * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε0.le
  have hl0' : 0 ≤ l := by
    have : (l0 * cv) * ε ≤ (l0 * cv) * (1 / 65536) := mul_le_mul_of_nonneg_left hε1 hprod0
    linarith
  have hlow := sub_cube_div_three_le_arctan hy0.le
  have hup := arctan_le_self hy0.le
  have hcube : y ^ 3 ≤ y * (4 * ε) := by
    have := mul_le_mul_of_nonneg_left hy2 hy0.le
    calc y ^ 3 = y * y ^ 2 := by ring
      _ ≤ y * (4 * ε) := this
  have hy3 : 0 ≤ y ^ 3 := by positivity
  have hy12 : y * ε ≤ ε / 2 := by
    have := mul_le_mul_of_nonneg_right hy1 hε0.le
    linarith
  have hwid : u - l ≤ (1 / 2 : ℝ) ^ w := by
    rw [hw]
    linarith
  exact ⟨l, u, hl, hu, hl0', by linarith, by linarith, hwid⟩

/-- **The bracket of `arccot |x| = arctan (1/|x|)`** for a finite float `x ≠ 0` of exponent
`e`: nonnegative lower end, width at most `2^(−w)`. -/
theorem acotBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {e : AzInt} (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|)
    (hex : |xv| < (2 : ℝ) ^ e.toInt) (w : ℕ) :
    IsEncl0W (acotBracket x e w) (arctan |xv|⁻¹) ((1 / 2 : ℝ) ^ w) := by
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  have hy0 : 0 < a⁻¹ := inv_pos.mpr ha0
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold acotBracket
  dsimp only
  split_ifs with he hc
  · -- huge argument
    have hen := two_pow_le_of_exponent hex1 he
    have h2 : a⁻¹ * (2 : ℝ) ^ e.abs.toNat ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hen hy0.le
      have e1 : a⁻¹ * (2 * a) = 2 := by field_simp
      linarith
    have hyle : a⁻¹ ≤ 2 * (1 / 2 : ℝ) ^ e.abs.toNat := by
      have e1 : a⁻¹ = a⁻¹ * (2 : ℝ) ^ e.abs.toNat * (1 / 2 : ℝ) ^ e.abs.toNat := by
        rw [mul_assoc, ← mul_pow]
        norm_num
      rw [e1]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hen8 : (1 / 2 : ℝ) ^ e.abs.toNat ≤ (1 / 2 : ℝ) ^ 8 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    refine acotTinyEncl_spec habs ha0 ?_ ?_
    · norm_num at hen8
      linarith
    · calc a⁻¹ ^ 2 ≤ (2 * (1 / 2 : ℝ) ^ e.abs.toNat) ^ 2 := pow_le_pow_left₀ hy0.le hyle 2
        _ = 4 * (1 / 2 : ℝ) ^ (2 * e.abs.toNat) := by
            rw [mul_pow, ← pow_mul, mul_comm e.abs.toNat 2]
            norm_num
        _ ≤ 4 * (1 / 2 : ℝ) ^ (w + 16) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one (by norm_num) (by norm_num) hc) (by norm_num)
        _ = (1 / 2 : ℝ) ^ (w + 14) := by ring
  · -- `|x| ≥ 1`
    have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
    have h1e : 1 ≤ e.toInt := by
      rw [htoInt, he.1]
      simp only [↓reduceIte]
      have := he.2
      omega
    have hge : 1 ≤ a := le_trans (one_le_zpow₀ (by norm_num) (by omega)) hex1
    have hy1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hge
    have hdiv : (1 : ℝ) / a = a⁻¹ := one_div a
    set K := w + 8 + e.abs.toNat with hK
    have : NeZero (K + 64) := ⟨by omega⟩
    obtain ⟨rl, hrl, hrl1, hrl2⟩ := divFloor_abs toVal_one' habs ha0.ne' (K + 64)
    obtain ⟨rh, hrh, hrh1, hrh2⟩ := divCeiling_abs toVal_one' habs ha0.ne' (K + 64)
    rw [hdiv] at hrl1 hrl2 hrh1 hrh2
    rw [abs_of_pos hy0] at hrl2 hrh2
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (K + 64) := by positivity
    have hu1 : (1 / 2 : ℝ) ^ (K + 64) ≤ 1 / 4 := by
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        (show 2 ≤ K + 64 by omega)
      norm_num at this
      linarith
    have hyu : a⁻¹ * (1 / 2 : ℝ) ^ (K + 64) ≤ 1 * (1 / 2 : ℝ) ^ (K + 64) :=
      mul_le_mul_of_nonneg_right hy1 hu0
    have hyu' : a⁻¹ * (1 / 2 : ℝ) ^ (K + 64) ≤ a⁻¹ * (1 / 4) :=
      mul_le_mul_of_nonneg_left hu1 hy0.le
    obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2, -, h3⟩ :=
      atanWiden_spec hrl hrh (by linarith) hrl1 hrh1 hy1 K (by linarith)
    have hKle : (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ (w + 8) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by ring
    have h64 : (1 / 2 : ℝ) ^ (K + 64) ≤ (1 / 2 : ℝ) ^ K / 1024 := by
      have h10 : (1 / 2 : ℝ) ^ (K + 10) = (1 / 2 : ℝ) ^ K / 1024 := by ring
      rw [← h10]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
    exact ⟨lo, hi, hlo, hhi, hlo0, h1, h2, by linarith⟩
  · -- `|x| < 1`
    have hlt1 : a < 1 := abs_lt_one_of_exponent hex he
    have hid : arctan a⁻¹ = π / 2 - arctan a := arctan_inv_of_pos ha0
    obtain ⟨al, ah, hal, hah, hal0, h1, h2, h3⟩ :=
      atanLoop_spec habs ha0.le hlt1.le (w + 8) (w + 8)
    have h3' := h3 (by omega)
    have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by ring
    have hat1 : arctan a ≤ π / 4 := by
      have h := arctan_strictMono.monotone hlt1.le
      rwa [arctan_one] at h
    have hπ := pi_lt_four
    have hπ3 := pi_gt_three
    obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ := piShiftEncl_spec true false hal hah hal0 h1 h2
      (by linarith) h3' (V := w + 72) (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
    have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
      have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by ring
      rw [← h10]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hwd' : hi - lo ≤ (1 / 2 : ℝ) ^ w / 16 := by linarith
    rw [hid]
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith, by linarith⟩

/-- `acotApprox` as a pair of `Roundable`s bracketing `−arctan (1/|x|)`. -/
theorem acotApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {e : AzInt} (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|)
    (hex : |xv| < (2 : ℝ) ^ e.toInt) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (acotApprox x e w).1 lv ∧ Rounds (acotApprox x e w).2 hv ∧
      lv ≤ -arctan |xv|⁻¹ ∧ -arctan |xv|⁻¹ ≤ hv ∧ hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, -, h1, h2, hwid⟩ := acotBracket_spec hx hx0 hex1 hex w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec true hlo hhi h1 h2
  simp only [↓reduceIte, neg_one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `arccot x = arctan (1/x)` is irrational for a finite float `x ≠ 0`. -/
theorem irrational_acot_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (arctan xv⁻¹) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hq, Rat.cast_zero])
  rw [hq, ← Rat.cast_inv]
  exact irrational_arctan_rat (inv_ne_zero hq0)

/-- The Ziv certificate for `−arccot |x|`, `x ≠ 0` a finite float. -/
theorem acotApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat}
    {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {e : AzInt}
    (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|) (hex : |xv| < (2 : ℝ) ^ e.toInt) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acotApprox x e (w₀ * 2 ^ f)).1
      (acotApprox x e (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have habs : (x.abs).toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  exact exists_isSome_of_irrational_threshold p mode (acotApprox x e)
    (irrational_acot_of_toVal habs (abs_ne_zero.mpr hx0)).neg (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => acotApprox_spec hx hx0 hex1 hex w) w₀ hw₀

/-- `−arctan (1/|x|) = ∓ arctan (1/x)` (`pos`: `x > 0`). -/
theorem acot_abs_eq {pos : Bool} {xv : ℝ} (hpos : pos = true ↔ 0 < xv) (hx0 : xv ≠ 0) :
    -arctan |xv|⁻¹ = (if pos then -1 else 1) * arctan xv⁻¹ := by
  cases pos with
  | true =>
    simp only [↓reduceIte]
    rw [abs_of_pos (hpos.mp rfl)]
    ring
  | false =>
    have hneg : xv < 0 :=
      lt_of_le_of_ne (not_lt.mp fun h => by simpa using hpos.mpr h) hx0
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_neg hneg, inv_neg, arctan_neg, neg_neg]

end Azurite.AzFloat
