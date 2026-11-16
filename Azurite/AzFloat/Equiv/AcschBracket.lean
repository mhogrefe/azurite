/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcschBracket
import Azurite.AzFloat.Equiv.AcotBracket
import Azurite.AzFloat.Equiv.AsinhBracket
import Azurite.AzFloat.Equiv.AcscBracket

/-!
# Equivalence: the bracket of `acsch x`

`arsinh_inv_eq_log` (`asinh (1/a) = ln ((1 + √(1 + a²))/a)`), `acschArg_lower`,
`acschArg_bounds` (the real arithmetic of the rounded-down argument), `acschArg_spec`,
`acschBracket_spec`, `acschApprox_spec`, `irrational_acsch_of_toVal`,
`acschApprox_isSome_exists`, `acsch_abs_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- `asinh (1/a) = ln ((1 + √(1 + a²))/a)` for `a > 0`. -/
theorem arsinh_inv_eq_log {a : ℝ} (h0 : 0 < a) :
    Real.arsinh a⁻¹ = Real.log ((1 + √(1 + a ^ 2)) / a) := by
  unfold Real.arsinh
  congr 1
  have e : 1 + a⁻¹ ^ 2 = (1 + a ^ 2) / a ^ 2 := by
    field_simp
    ring
  rw [e, sqrt_div (by positivity), sqrt_sq h0.le]
  field_simp

/-- The lower chain of `acschArg`: with every step rounded down by a factor `c ∈ (0, 1]`, the
result is at least `c⁴ (1 + √(1 + A²))/A`. -/
theorem acschArg_lower {A m s r n y c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hA0 : 0 < A)
    (hm : c * (A * A) ≤ m) (hs : c * (1 + m) ≤ s) (hr : c * √s ≤ r) (hn : c * (1 + r) ≤ n)
    (hy : c * (n / A) ≤ y) :
    c * c * c * c * ((1 + √(1 + A ^ 2)) / A) ≤ y := by
  have hRsq : √(1 + A ^ 2) ^ 2 = 1 + A ^ 2 := sq_sqrt (by positivity)
  have hR0 : 0 ≤ √(1 + A ^ 2) := sqrt_nonneg _
  have hcc1 : c * c ≤ 1 := by nlinarith
  have hcc : c * c ≤ c := by nlinarith
  have hs' : c * c * (1 + A ^ 2) ≤ s := by
    have h1 : c * (1 + c * (A * A)) ≤ s := (mul_le_mul_of_nonneg_left (by linarith) hc0.le).trans hs
    have e : c * (1 + c * (A * A)) = c + c * c * A ^ 2 := by ring
    rw [e] at h1
    have e2 : c * c * (1 + A ^ 2) = c * c + c * c * A ^ 2 := by ring
    rw [e2]
    linarith
  have hsq : c * √(1 + A ^ 2) ≤ √s := by
    have h1 : (c * √(1 + A ^ 2)) ^ 2 ≤ s := by
      have : (c * √(1 + A ^ 2)) ^ 2 = c * c * √(1 + A ^ 2) ^ 2 := by ring
      rw [this, hRsq]
      exact hs'
    exact (le_abs_self _).trans (abs_le_sqrt h1)
  have hr' : c * (c * √(1 + A ^ 2)) ≤ r := (mul_le_mul_of_nonneg_left hsq hc0.le).trans hr
  have hsum : c * c * (1 + √(1 + A ^ 2)) ≤ 1 + r := by
    have e : c * c * (1 + √(1 + A ^ 2)) = c * c + c * (c * √(1 + A ^ 2)) := by ring
    rw [e]
    linarith
  have hn' : c * (c * c * (1 + √(1 + A ^ 2))) ≤ n :=
    (mul_le_mul_of_nonneg_left hsum hc0.le).trans hn
  have hq : c * (c * c * (1 + √(1 + A ^ 2))) / A ≤ n / A :=
    div_le_div_of_nonneg_right hn' hA0.le
  have hfin := (mul_le_mul_of_nonneg_left hq hc0.le).trans hy
  have e : c * (c * (c * c * (1 + √(1 + A ^ 2))) / A)
      = c * c * c * c * ((1 + √(1 + A ^ 2)) / A) := by ring
  rw [e] at hfin
  exact hfin

/-- The real arithmetic of `acschArg`: with every step rounded down within a relative `2η`,
the result is within a relative `8η` below `(1 + √(1 + A²))/A`. -/
theorem acschArg_bounds {A m s r n y η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 64) (hA0 : 0 < A)
    (hm1 : m ≤ A * A) (hm2 : A * A ≤ m + 2 * (A * A) * η)
    (hs1 : s ≤ 1 + m) (hs2 : 1 + m ≤ s + 2 * (1 + m) * η)
    (hr1 : r ≤ √s) (hr2 : √s ≤ r + 2 * √s * η)
    (hn1 : n ≤ 1 + r) (hn2 : 1 + r ≤ n + 2 * (1 + r) * η)
    (hy1 : y ≤ n / A) (hy2 : n / A ≤ y + 2 * (n / A) * η) :
    y ≤ (1 + √(1 + A ^ 2)) / A ∧
      (1 + √(1 + A ^ 2)) / A ≤ y + 8 * ((1 + √(1 + A ^ 2)) / A) * η := by
  have hR0 : 0 ≤ √(1 + A ^ 2) := sqrt_nonneg _
  have hc0 : 0 < 1 - 2 * η := by linarith
  have g1 : (1 - 2 * η) * (A * A) ≤ m := by linarith
  have g2 : (1 - 2 * η) * (1 + m) ≤ s := by linarith
  have g3 : (1 - 2 * η) * √s ≤ r := by linarith
  have g4 : (1 - 2 * η) * (1 + r) ≤ n := by linarith
  have g5 : (1 - 2 * η) * (n / A) ≤ y := by linarith
  have hlow := acschArg_lower hc0 (by linarith) hA0 g1 g2 g3 g4 g5
  have hbern : 1 - 8 * η ≤ (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) := by
    have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(2 * η)) 4
    have e : (1 + -(2 * η)) ^ 4 = (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) := by
      ring
    rw [e] at h
    push_cast at h
    linarith
  have hV0 : 0 ≤ (1 + √(1 + A ^ 2)) / A := by positivity
  have hfin : (1 - 8 * η) * ((1 + √(1 + A ^ 2)) / A) ≤ y :=
    (mul_le_mul_of_nonneg_right hbern hV0).trans hlow
  have hsle : s ≤ 1 + A ^ 2 := by
    have e : A ^ 2 = A * A := sq A
    linarith
  have hrle : r ≤ √(1 + A ^ 2) := hr1.trans (sqrt_le_sqrt hsle)
  have hup : n / A ≤ (1 + √(1 + A ^ 2)) / A := div_le_div_of_nonneg_right (by linarith) hA0.le
  constructor
  · linarith
  · have e : (1 - 8 * η) * ((1 + √(1 + A ^ 2)) / A)
        = (1 + √(1 + A ^ 2)) / A - 8 * ((1 + √(1 + A ^ 2)) / A) * η := by ring
    linarith

/-- **`acschArg a W` is just below `(1 + √(1 + a²))/a`**, for a float `a > 0`. -/
theorem acschArg_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) {W : ℕ} (hW : 6 ≤ W) :
    ∃ y : ℝ, (acschArg a W).toVal = some (y : EReal) ∧ y ≤ (1 + √(1 + av ^ 2)) / av ∧
      (1 + √(1 + av ^ 2)) / av
        ≤ y + 8 * ((1 + √(1 + av ^ 2)) / av) * (1 / 2 : ℝ) ^ W := by
  have : NeZero W := ⟨by omega⟩
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hη : (1 / 2 : ℝ) ^ W ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hW
      _ = 1 / 64 := by norm_num
  obtain ⟨m, hm, hm0, hm1, hm2⟩ := mulFloor_err ha ha W (by positivity)
  obtain ⟨s, hs, hs0, hs1, hs2⟩ := addFloor_err toVal_one' hm W (by linarith)
  obtain ⟨r, hr, hr0, hr1, hr2⟩ := sqrtFloor_err hs hs0 W
  obtain ⟨n, hn, hn0, hn1, hn2⟩ := addFloor_err toVal_one' hr W (by linarith)
  obtain ⟨y, hy, -, hy1, hy2⟩ := divFloor_err hn ha ha0 hn0 W
  exact ⟨y, hy, acschArg_bounds hη0 hη ha0 hm1 hm2 hs1 hs2 hr1 hr2 hn1 hn2 hy1 hy2⟩

/-- The width bound of `acschBracket`. -/
noncomputable def acschEps (av : ℝ) (w : ℕ) : ℝ := asinhEps av⁻¹ w + (1 / 2 : ℝ) ^ w

theorem tendsto_acschEps (av : ℝ) : Filter.Tendsto (acschEps av) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := (tendsto_asinhEps av⁻¹).add hp
  rw [add_zero] at h
  exact h

theorem asinhEps_nonneg (A : ℝ) (w : ℕ) : 0 ≤ asinhEps A w := by
  have := abs_nonneg (Real.arsinh A)
  unfold asinhEps lnRatEps
  have hL : 0 ≤ lnEps (⌊2 * |Real.arsinh A|⌋₊ + 2 : ℕ) w := by
    unfold lnEps
    positivity
  positivity

/-- **`acschBracket a e w` encloses `acsch a = asinh (1/a)`** for a float `a > 0` with
`2^(e−1) ≤ a`. -/
theorem acschBracket_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) {e : AzInt} (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ av) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (acschBracket a e w) (Real.arsinh av⁻¹) (acschEps av w) := by
  have hy0 : 0 < av⁻¹ := inv_pos.mpr ha0
  have hpw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  unfold acschBracket acschEps
  split_ifs with hc
  · obtain ⟨hs, hn0, hc2⟩ := hc
    have hen := two_pow_le_of_exponent (xv := av) (by rwa [abs_of_pos ha0]) ⟨hs, hn0⟩
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
    have hsmall : av⁻¹ ≤ 1 / 2 := by
      norm_num at hen8
      linarith
    have hsq : av⁻¹ ^ 2 ≤ (1 / 2 : ℝ) ^ (w + 14) := by
      calc av⁻¹ ^ 2 ≤ (2 * (1 / 2 : ℝ) ^ e.abs.toNat) ^ 2 := pow_le_pow_left₀ hy0.le hyle 2
        _ = 4 * (1 / 2 : ℝ) ^ (2 * e.abs.toNat) := by
            rw [mul_pow, ← pow_mul, mul_comm e.abs.toNat 2]
            norm_num
        _ ≤ 4 * (1 / 2 : ℝ) ^ (w + 16) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one (by norm_num) (by norm_num) hc2) (by norm_num)
        _ = (1 / 2 : ℝ) ^ (w + 14) := by ring
    have h := (acotTinyEncl_spec_of ha ha0 hsmall hsq (sub_cube_le_arsinh hy0)
      (arsinh_lt_self hy0).le).toW
    exact h.mono (by linarith [asinhEps_nonneg av⁻¹ w])
  · obtain ⟨y, hy, hy1, hy2⟩ := acschArg_spec ha ha0 (W := w + 8) (by omega)
    have hV : 0 < (1 + √(1 + av ^ 2)) / av := by
      have : 0 ≤ √(1 + av ^ 2) := sqrt_nonneg _
      positivity
    have hpw : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
      rw [pow_add]
      norm_num
      ring
    have hy2' : (1 + √(1 + av ^ 2)) / av
        ≤ y + 2 * ((1 + √(1 + av ^ 2)) / av) * (1 / 2 : ℝ) ^ w := by
      rw [hpw] at hy2
      have : 0 ≤ (1 + √(1 + av ^ 2)) / av * (1 / 2 : ℝ) ^ w := by positivity
      linarith
    obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := lnFloorBracket_spec hw hy hV hy1 hy2'
    rw [← arsinh_inv_eq_log ha0] at hlo hhi hwid
    exact ⟨lv, hv, hlv, hhv, hlo, hhi, by unfold asinhEps; linarith⟩

/-- `acschApprox` as a pair of `Roundable`s bracketing `−asinh (1/|x|)`. -/
theorem acschApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {e : AzInt} (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|) {w : ℕ}
    (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (acschApprox x e w).1 lv ∧ Rounds (acschApprox x e w).2 hv ∧
      lv ≤ -Real.arsinh |xv|⁻¹ ∧ -Real.arsinh |xv|⁻¹ ≤ hv ∧ hv - lv ≤ acschEps |xv| w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    acschBracket_spec habs (abs_pos.mpr hx0) hex1 hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec true hlo hhi h1 h2
  simp only [↓reduceIte, neg_one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `acsch x = asinh (1/x)` is irrational for a finite float `x ≠ 0`. -/
theorem irrational_acsch_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.arsinh xv⁻¹) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hq, Rat.cast_zero])
  rw [hq, ← Rat.cast_inv]
  exact irrational_arsinh_rat (inv_ne_zero hq0)

/-- The Ziv certificate for `−acsch |x|`, `x ≠ 0` a finite float. -/
theorem acschApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat}
    {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {e : AzInt}
    (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acschApprox x e (w₀ * 2 ^ f)).1
      (acschApprox x e (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have habs : (x.abs).toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  exact exists_isSome_of_irrational_threshold p mode (acschApprox x e)
    (irrational_acsch_of_toVal habs (abs_ne_zero.mpr hx0)).neg (acschEps |xv|)
    (tendsto_acschEps _) 64 (fun _ hw => acschApprox_spec hx hx0 hex1 hw) w₀ hw₀

/-- `−asinh (1/|x|) = ∓ asinh (1/x)` (`pos`: `x > 0`). -/
theorem acsch_abs_eq {pos : Bool} {xv : ℝ} (hpos : pos = true ↔ 0 < xv) (hx0 : xv ≠ 0) :
    -Real.arsinh |xv|⁻¹ = (if pos then -1 else 1) * Real.arsinh xv⁻¹ := by
  cases pos with
  | true =>
    simp only [↓reduceIte]
    rw [abs_of_pos (hpos.mp rfl)]
    ring
  | false =>
    have hneg : xv < 0 :=
      lt_of_le_of_ne (not_lt.mp fun h => by simpa using hpos.mpr h) hx0
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_neg hneg, inv_neg, arsinh_neg, neg_neg]

end Azurite.AzFloat
