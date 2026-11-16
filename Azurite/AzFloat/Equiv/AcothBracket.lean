/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcothBracket
import Azurite.AzFloat.Equiv.AcscBracket
import Azurite.AzFloat.Equiv.AcschBracket
import Azurite.AzFloat.Equiv.AtanhBracket
import Azurite.AzFloat.Equiv.AsecBracket

/-!
# Equivalence: the bracket of `acoth x`

`artanh_inv_eq_half_log` (`atanh (1/a) = (1/2) ln ((a + 1)/(a − 1))`), `quotFloor_bounds` (the
real arithmetic of a rounded-down quotient), `lnRatEps_nonneg`, `acothBracket_spec`,
`acothApprox_spec`, `irrational_acoth_of_toVal`, `acothApprox_isSome_exists`, `acoth_abs_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- `atanh (1/a) = (1/2) ln ((a + 1)/(a − 1))` for `a > 1`. -/
theorem artanh_inv_eq_half_log {a : ℝ} (h1 : 1 < a) :
    Real.artanh a⁻¹ = 1 / 2 * Real.log ((a + 1) / (a - 1)) := by
  have ha0 : 0 < a := by linarith
  have hinv1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have hinv0 : 0 < a⁻¹ := inv_pos.mpr ha0
  rw [artanh_eq_half_log ⟨by linarith, hinv1.le⟩]
  congr 2
  have hd : a - 1 ≠ 0 := by linarith
  field_simp

/-- The quotient, rounded down, of a numerator rounded down and a denominator rounded up is
within a relative `8η` below `N/D`. -/
theorem quotFloor_bounds {N D su df y η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 64) (hN0 : 0 ≤ N)
    (hD0 : 0 < D) (hsu1 : su ≤ N) (hsu2 : N ≤ su + 2 * N * η)
    (hdf1 : D ≤ df) (hdf2 : df ≤ D + 2 * D * η)
    (hy1 : y ≤ su / df) (hy2 : su / df ≤ y + 2 * (su / df) * η) :
    y ≤ N / D ∧ N / D ≤ y + 8 * (N / D) * η := by
  have hdf0 : 0 < df := lt_of_lt_of_le hD0 hdf1
  set V := N / D with hV
  have hV0 : 0 ≤ V := div_nonneg hN0 hD0.le
  have hVd : V * D = N := div_mul_cancel₀ _ hD0.ne'
  have hc0 : 0 < 1 - 2 * η := by linarith
  have hup : su / df ≤ V := div_le_div₀ hN0 hsu1 hD0 hdf1
  have hVdf : V * df ≤ N * (1 + 2 * η) := by
    have := mul_le_mul_of_nonneg_left hdf2 hV0
    have e : V * (D + 2 * D * η) = V * D * (1 + 2 * η) := by ring
    rw [e, hVd] at this
    exact this
  have hlow : (1 - 2 * η) * (1 - 2 * η) * V ≤ su / df := by
    rw [le_div_iff₀ hdf0]
    have h1 : (1 - 2 * η) * (1 - 2 * η) * V * df
        ≤ (1 - 2 * η) * (1 - 2 * η) * (N * (1 + 2 * η)) := by
      have := mul_le_mul_of_nonneg_left hVdf (mul_nonneg hc0.le hc0.le)
      linarith
    have h2 : (1 - 2 * η) * (1 + 2 * η) ≤ 1 := by nlinarith
    have h3 : (1 - 2 * η) * (1 - 2 * η) * (N * (1 + 2 * η)) ≤ (1 - 2 * η) * N := by
      have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hc0.le hN0)
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

theorem lnRatEps_nonneg (E : ℕ) {A : ℝ} (hA : 0 ≤ A) (w : ℕ) : 0 ≤ lnRatEps E A w := by
  have hL : 0 ≤ lnEps (E : ℤ) w := by
    unfold lnEps
    positivity
  unfold lnRatEps
  positivity

/-- The width bound of `acothBracket`. -/
noncomputable def acothEps (av : ℝ) (w : ℕ) : ℝ :=
  lnRatEps (⌊2 * |Real.log ((av + 1) / (av - 1))|⌋₊ + 2) |Real.log ((av + 1) / (av - 1))| w
    + (1 / 2 : ℝ) ^ w

theorem tendsto_acothEps (av : ℝ) : Filter.Tendsto (acothEps av) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := (tendsto_lnRatEps (⌊2 * |Real.log ((av + 1) / (av - 1))|⌋₊ + 2)
    |Real.log ((av + 1) / (av - 1))|).add hp
  rw [add_zero] at h
  exact h

/-- **`acothBracket a e w` encloses `acoth a = atanh (1/a)`** for a float `a > 1` of exponent
`e ≥ 1` (`2^(e−1) ≤ a`). -/
theorem acothBracket_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha1 : 1 < av) {e : AzInt} (he : e.sign = true ∧ e.abs.toNat ≠ 0)
    (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ av) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (acothBracket a e w) (Real.artanh av⁻¹) (acothEps av w) := by
  have ha0 : 0 < av := by linarith
  have hy0 : 0 < av⁻¹ := inv_pos.mpr ha0
  have hpw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hLn := lnRatEps_nonneg (⌊2 * |Real.log ((av + 1) / (av - 1))|⌋₊ + 2)
    (abs_nonneg (Real.log ((av + 1) / (av - 1)))) w
  unfold acothBracket acothEps
  split_ifs with hc
  · have hen := two_pow_le_of_exponent (xv := av) (by rwa [abs_of_pos ha0]) he
    rw [abs_of_pos ha0] at hen
    have h2 : av⁻¹ * (2 : ℝ) ^ e.abs.toNat ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hen hy0.le
      have e1 : av⁻¹ * (2 * av) = 2 := by field_simp
      linarith
    have hyle : av⁻¹ ≤ 2 * (1 / 2 : ℝ) ^ e.abs.toNat := by
      have e1 : av⁻¹ = av⁻¹ * (2 : ℝ) ^ e.abs.toNat * (1 / 2 : ℝ) ^ e.abs.toNat := by
        rw [mul_assoc, ← mul_pow]
        norm_num
      rw [e1]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hen8 : (1 / 2 : ℝ) ^ e.abs.toNat ≤ (1 / 2 : ℝ) ^ 8 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hsmall : av⁻¹ ≤ 1 / 4 := by
      norm_num at hen8
      linarith
    have hsq : av⁻¹ ^ 2 ≤ (1 / 2 : ℝ) ^ (w + 14) := by
      calc av⁻¹ ^ 2 ≤ (2 * (1 / 2 : ℝ) ^ e.abs.toNat) ^ 2 := pow_le_pow_left₀ hy0.le hyle 2
        _ = 4 * (1 / 2 : ℝ) ^ (2 * e.abs.toNat) := by
            rw [mul_pow, ← pow_mul, mul_comm e.abs.toNat 2]
            norm_num
        _ ≤ 4 * (1 / 2 : ℝ) ^ (w + 16) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one (by norm_num) (by norm_num) hc) (by norm_num)
        _ = (1 / 2 : ℝ) ^ (w + 14) := by ring
    obtain ⟨hlt, hle⟩ := artanh_tiny_bounds hy0 hsmall
    have h := (acscTinyEncl_spec_of ha ha0 (by linarith) hsq hlt.le hle).toW
    exact h.mono (by linarith)
  · have : NeZero (w + 8) := ⟨by omega⟩
    have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 8) := by positivity
    have hη : (1 / 2 : ℝ) ^ (w + 8) ≤ 1 / 64 := by
      calc (1 / 2 : ℝ) ^ (w + 8) ≤ (1 / 2 : ℝ) ^ 6 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 64 := by norm_num
    obtain ⟨su, hsu, hsu0, hsu1, hsu2⟩ := addFloor_err ha toVal_one' (w + 8) (by linarith)
    obtain ⟨df, hdf, hdf1, hdf2⟩ := subCeiling_err ha toVal_one' (w + 8) (by linarith)
    have hd0 : 0 < av - 1 := by linarith
    have hdf0 : 0 < df := lt_of_lt_of_le hd0 hdf1
    obtain ⟨y, hy, -, hy1, hy2⟩ := divFloor_err hsu hdf hdf0 hsu0 (w + 8)
    obtain ⟨b1, b2⟩ := quotFloor_bounds hη0 hη (by linarith : (0 : ℝ) ≤ av + 1) hd0 hsu1 hsu2
      hdf1 hdf2 hy1 hy2
    have hV : 0 < (av + 1) / (av - 1) := div_pos (by linarith) hd0
    have hpw : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
      rw [pow_add]
      norm_num
      ring
    have hy2' : (av + 1) / (av - 1) ≤ y + 2 * ((av + 1) / (av - 1)) * (1 / 2 : ℝ) ^ w := by
      rw [hpw] at b2
      have : 0 ≤ (av + 1) / (av - 1) * (1 / 2 : ℝ) ^ w := by positivity
      linarith
    obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := lnFloorBracket_spec hw hy hV b1 hy2'
    have hsh1 := toVal_shiftLeft_of_toVal hlv (AzInt.ofInt (-1))
    have hsh2 := toVal_shiftLeft_of_toVal hhv (AzInt.ofInt (-1))
    rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at hsh1 hsh2
    have hart := artanh_inv_eq_half_log ha1
    have hw0 : 0 ≤ hv - lv := by linarith
    exact ⟨lv / 2, hv / 2, hsh1, hsh2, by rw [hart]; linarith, by rw [hart]; linarith,
      by linarith⟩

/-- `acothApprox` as a pair of `Roundable`s bracketing `atanh (1/|x|)`. -/
theorem acothApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) {e : AzInt} (he : e.sign = true ∧ e.abs.toNat ≠ 0)
    (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (acothApprox x e w).1 lv ∧ Rounds (acothApprox x e w).2 hv ∧
      lv ≤ Real.artanh |xv|⁻¹ ∧ Real.artanh |xv|⁻¹ ≤ hv ∧ hv - lv ≤ acothEps |xv| w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := acothBracket_spec habs hx1 he hex1 hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, hee⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [hee]; exact hwid⟩

/-- `acoth x = atanh (1/x)` is irrational for a finite float `|x| > 1`. -/
theorem irrational_acoth_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) : Irrational (Real.artanh xv⁻¹) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hx0 : xv ≠ 0 := fun h => by
    rw [h, abs_zero] at hx1
    linarith
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hq, Rat.cast_zero])
  have hlt : |xv⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hx1
  rw [hq, ← Rat.cast_inv] at hlt ⊢
  exact irrational_artanh_rat (inv_ne_zero hq0) hlt

/-- The Ziv certificate for `acoth |x|`, `x` a finite float with `|x| > 1`. -/
theorem acothApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat}
    {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : 1 < |xv|) {e : AzInt}
    (he : e.sign = true ∧ e.abs.toNat ≠ 0) (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acothApprox x e (w₀ * 2 ^ f)).1
      (acothApprox x e (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have habs : (x.abs).toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  exact exists_isSome_of_irrational_threshold p mode (acothApprox x e)
    (irrational_acoth_of_toVal habs (by rwa [abs_abs])) (acothEps |xv|) (tendsto_acothEps _)
    64 (fun _ hw => acothApprox_spec hx hx1 he hex1 hw) w₀ hw₀

/-- `atanh (1/|x|) = ± atanh (1/x)` (`neg`: `x < 0`). -/
theorem acoth_abs_eq {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    Real.artanh |xv|⁻¹ = (if neg then -1 else 1) * Real.artanh xv⁻¹ := by
  cases neg with
  | true =>
    have hlt : xv < 0 := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg hlt, inv_neg, artanh_neg']
    ring
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg hpos]

end Azurite.AzFloat
