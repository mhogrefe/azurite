/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinhBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.Equiv.LnBracket
import Azurite.AzFloat.Equiv.SinRatBracket
import Azurite.AzFloat.Equiv.TanhBracket
import Azurite.Transcendental.Sinh

/-!
# Equivalence: the brackets of `asinh x` and `asinh q`

`asinhArg_bounds` (the real arithmetic of the rounded-down argument `a + √(a² + 1)`),
`asinhArg_spec`, `asinhLn_spec` (the bracket from any float just below `a`),
`asinhBracket_spec`, `asinhApprox_spec`, `irrational_asinh_of_toVal`,
`asinhApprox_isSome_exists`, the rational versions `asinhRatBracket_spec`,
`asinhRatApprox_spec`, `irrational_asinh_toRat`, `asinhRatApprox_isSome_exists`, and the
tiny-argument bounds `arsinh_lt_self`, `sub_cube_le_arsinh`.
-/

open Real

namespace Azurite.AzFloat

/-- The lower chain of `asinhArg`: with every step rounded down by a factor `c ∈ (0, 1]`, the
result is at least `c⁴ (A + √(1 + A²))`. -/
theorem asinhArg_lower {A al m s r y c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hal0 : 0 ≤ al)
    (hA0 : 0 ≤ A) (hal : c * A ≤ al) (hm : c * (al * al) ≤ m) (hs : c * (m + 1) ≤ s)
    (hr : c * √s ≤ r) (hy : c * (al + r) ≤ y) :
    c * c * c * c * (A + √(1 + A ^ 2)) ≤ y := by
  have hRsq : √(1 + A ^ 2) ^ 2 = 1 + A ^ 2 := sq_sqrt (by positivity)
  have hR0 : 0 ≤ √(1 + A ^ 2) := sqrt_nonneg _
  have hcc1 : c * c ≤ 1 := by nlinarith
  have hccc1 : c * c * c ≤ 1 := by nlinarith
  have halsq : (c * A) * (c * A) ≤ al * al := mul_le_mul hal hal (by positivity) hal0
  have hm' : c * ((c * A) * (c * A)) ≤ m := (mul_le_mul_of_nonneg_left halsq hc0.le).trans hm
  have hs' : c * c * c * c * (1 + A ^ 2) ≤ s := by
    have h1 : c * (c * ((c * A) * (c * A)) + 1) ≤ s :=
      (mul_le_mul_of_nonneg_left (by linarith) hc0.le).trans hs
    have h2 : c * c * c * c * 1 ≤ c * 1 := by
      have := mul_le_mul_of_nonneg_right hccc1 hc0.le
      linarith
    have e : c * (c * ((c * A) * (c * A)) + 1) = c * c * c * c * A ^ 2 + c := by ring
    rw [e] at h1
    have e2 : c * c * c * c * (1 + A ^ 2) = c * c * c * c * A ^ 2 + c * c * c * c * 1 := by ring
    rw [e2]
    linarith
  have hsq : c * c * √(1 + A ^ 2) ≤ √s := by
    have h1 : (c * c * √(1 + A ^ 2)) ^ 2 ≤ s := by
      have : (c * c * √(1 + A ^ 2)) ^ 2 = c * c * c * c * √(1 + A ^ 2) ^ 2 := by ring
      rw [this, hRsq]
      exact hs'
    exact (le_abs_self _).trans (abs_le_sqrt h1)
  have hr' : c * (c * c * √(1 + A ^ 2)) ≤ r := (mul_le_mul_of_nonneg_left hsq hc0.le).trans hr
  have hA' : c * c * c * A ≤ c * A := by
    have := mul_le_mul_of_nonneg_right hcc1 (mul_nonneg hc0.le hA0)
    have e : c * c * (c * A) = c * c * c * A := by ring
    linarith
  have hsum : c * c * c * (A + √(1 + A ^ 2)) ≤ al + r := by
    have e : c * c * c * (A + √(1 + A ^ 2)) = c * c * c * A + c * (c * c * √(1 + A ^ 2)) := by
      ring
    rw [e]
    linarith
  have := (mul_le_mul_of_nonneg_left hsum hc0.le).trans hy
  have e : c * (c * c * c * (A + √(1 + A ^ 2))) = c * c * c * c * (A + √(1 + A ^ 2)) := by ring
  linarith

/-- The real arithmetic of `asinhArg`: with every step rounded down within a relative `2η`,
the result is within a relative `8η` below `A + √(1 + A²)`. -/
theorem asinhArg_bounds {A al m s r y η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 64) (hal0 : 0 ≤ al)
    (hal1 : al ≤ A) (hal2 : A ≤ al + 2 * A * η)
    (hm1 : m ≤ al * al) (hm2 : al * al ≤ m + 2 * (al * al) * η)
    (hs1 : s ≤ m + 1) (hs2 : m + 1 ≤ s + 2 * (m + 1) * η)
    (hr1 : r ≤ √s) (hr2 : √s ≤ r + 2 * √s * η)
    (hy1 : y ≤ al + r) (hy2 : al + r ≤ y + 2 * (al + r) * η) :
    y ≤ A + √(1 + A ^ 2) ∧ A + √(1 + A ^ 2) ≤ y + 8 * (A + √(1 + A ^ 2)) * η := by
  have hA0 : 0 ≤ A := hal0.trans hal1
  have hR0 : 0 ≤ √(1 + A ^ 2) := sqrt_nonneg _
  have hc0 : 0 < 1 - 2 * η := by linarith
  have g1 : (1 - 2 * η) * A ≤ al := by linarith
  have g2 : (1 - 2 * η) * (al * al) ≤ m := by linarith
  have g3 : (1 - 2 * η) * (m + 1) ≤ s := by linarith
  have g4 : (1 - 2 * η) * √s ≤ r := by linarith
  have g5 : (1 - 2 * η) * (al + r) ≤ y := by linarith
  have hlow := asinhArg_lower hc0 (by linarith) hal0 hA0 g1 g2 g3 g4 g5
  have hbern : 1 - 8 * η ≤ (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) := by
    have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(2 * η)) 4
    have e : (1 + -(2 * η)) ^ 4 = (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) * (1 - 2 * η) := by
      ring
    rw [e] at h
    push_cast at h
    linarith
  have hV0 : 0 ≤ A + √(1 + A ^ 2) := by positivity
  have hfin : (1 - 8 * η) * (A + √(1 + A ^ 2)) ≤ y :=
    (mul_le_mul_of_nonneg_right hbern hV0).trans hlow
  have hsle : s ≤ 1 + A ^ 2 := by
    have : al * al ≤ A * A := mul_le_mul hal1 hal1 hal0 hA0
    have e : A ^ 2 = A * A := sq A
    linarith
  have hrle : r ≤ √(1 + A ^ 2) := hr1.trans (sqrt_le_sqrt hsle)
  constructor
  · linarith
  · have e : (1 - 8 * η) * (A + √(1 + A ^ 2))
        = (A + √(1 + A ^ 2)) - 8 * (A + √(1 + A ^ 2)) * η := by ring
    linarith

/-- **`asinhArg alo W` is just below `A + √(1 + A²)`**, for a float `alo` just below `A ≥ 0`. -/
theorem asinhArg_spec {alo : AzFloat} {al A : ℝ} (hal : alo.toVal = some (al : EReal))
    (hal0 : 0 ≤ al) (hal1 : al ≤ A) {W : ℕ} (hW : 6 ≤ W)
    (hal2 : A ≤ al + 2 * A * (1 / 2 : ℝ) ^ W) :
    ∃ y : ℝ, (asinhArg alo W).toVal = some (y : EReal) ∧ y ≤ A + √(1 + A ^ 2) ∧
      A + √(1 + A ^ 2) ≤ y + 8 * (A + √(1 + A ^ 2)) * (1 / 2 : ℝ) ^ W := by
  have : NeZero W := ⟨by omega⟩
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hη : (1 / 2 : ℝ) ^ W ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hW
      _ = 1 / 64 := by norm_num
  obtain ⟨m, hm, hm0, hm1, hm2⟩ := mulFloor_err hal hal W (mul_nonneg hal0 hal0)
  obtain ⟨s, hs, hs0, hs1, hs2⟩ := addFloor_err hm toVal_one' W (by linarith)
  obtain ⟨r, hr, hr0, hr1, hr2⟩ := sqrtFloor_err hs hs0 W
  obtain ⟨y, hy, -, hy1, hy2⟩ := addFloor_err hal hr W (by linarith)
  exact ⟨y, hy, asinhArg_bounds hη0 hη hal0 hal1 hal2 hm1 hm2 hs1 hs2 hr1 hr2 hy1 hy2⟩

/-- The width bound of the brackets of `asinh a`. -/
noncomputable def asinhEps (A : ℝ) (w : ℕ) : ℝ :=
  lnRatEps (⌊2 * |Real.arsinh A|⌋₊ + 2) |Real.arsinh A| w

theorem tendsto_asinhEps (A : ℝ) : Filter.Tendsto (asinhEps A) Filter.atTop (nhds 0) :=
  tendsto_lnRatEps _ _

/-- **The logarithm of `asinhArg` encloses `asinh A`**, for a float `alo` just below `A ≥ 0`. -/
theorem asinhLn_spec {alo : AzFloat} {al A : ℝ} (hal : alo.toVal = some (al : EReal))
    (hal0 : 0 ≤ al) (hal1 : al ≤ A) {w : ℕ} (hw : 64 ≤ w)
    (hal2 : A ≤ al + 2 * A * (1 / 2 : ℝ) ^ (w + 8)) :
    IsEnclW (lnFloorBracket (asinhArg alo (w + 8)) w) (Real.arsinh A) (asinhEps A w) := by
  obtain ⟨y, hy, hy1, hy2⟩ := asinhArg_spec hal hal0 hal1 (W := w + 8) (by omega) hal2
  have hA0 : 0 ≤ A := hal0.trans hal1
  have hV : 0 < A + √(1 + A ^ 2) := by
    have : 0 < √(1 + A ^ 2) := sqrt_pos.mpr (by positivity)
    linarith
  have hpw : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  have hy2' : A + √(1 + A ^ 2) ≤ y + 2 * (A + √(1 + A ^ 2)) * (1 / 2 : ℝ) ^ w := by
    rw [hpw] at hy2
    have : 0 ≤ (A + √(1 + A ^ 2)) * (1 / 2 : ℝ) ^ w := by positivity
    linarith
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := lnFloorBracket_spec hw hy hV hy1 hy2'
  exact ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩

/-- `asinh x` from `asinh |x|`. -/
theorem asinh_abs_eq {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    (if neg then -1 else 1) * Real.arsinh |xv| = Real.arsinh xv := by
  cases neg with
  | true =>
    have hlt : xv < 0 := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg hlt, arsinh_neg]
    ring
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg hpos]

/-! ### Floats -/

/-- **`asinhBracket a w` encloses `asinh a`** for a float `a ≥ 0`. -/
theorem asinhBracket_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 ≤ av) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (asinhBracket a w) (Real.arsinh av) (asinhEps av w) :=
  asinhLn_spec ha ha0 le_rfl hw (by
    have : 0 ≤ 2 * av * (1 / 2 : ℝ) ^ (w + 8) := by positivity
    linarith)

/-- `asinhApprox neg` as a pair of `Roundable`s bracketing `asinh x`. -/
theorem asinhApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {neg : Bool} (hneg : neg = true ↔ xv < 0) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (asinhApprox neg x w).1 lv ∧ Rounds (asinhApprox neg x w).2 hv ∧
      lv ≤ Real.arsinh xv ∧ Real.arsinh xv ≤ hv ∧ hv - lv ≤ asinhEps |xv| w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := asinhBracket_spec habs (abs_nonneg xv) hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  rw [asinh_abs_eq hneg] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `asinh x` is irrational for a finite float `x ≠ 0`. -/
theorem irrational_asinh_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.arsinh xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  rw [hq] at hx0 ⊢
  exact irrational_arsinh_rat (by exact_mod_cast hx0)

/-- The Ziv certificate for `asinh x`, `x` a finite nonzero float. -/
theorem asinhApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (asinhApprox neg x (w₀ * 2 ^ f)).1
      (asinhApprox neg x (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (asinhApprox neg x)
    (irrational_asinh_of_toVal hx hx0) (asinhEps |xv|) (tendsto_asinhEps _) 64
    (fun _ hw => asinhApprox_spec hx hneg hw) w₀ hw₀

/-! ### Rationals -/

/-- **`asinhRatBracket q w` encloses `asinh |q|`** for a rational `q`. -/
theorem asinhRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) :
    IsEnclW (asinhRatBracket q w) (Real.arsinh |((AzRat.toRat q : ℚ) : ℝ)|)
      (asinhEps |((AzRat.toRat q : ℚ) : ℝ)| w) := by
  have : NeZero (w + 8) := ⟨by omega⟩
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs q.abs (w + 8)
  rw [habs] at hl1 hl2
  rw [abs_abs] at hl2
  have hη : (1 / 2 : ℝ) ^ (w + 8) ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ (w + 8) ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hl0 : 0 ≤ l := by nlinarith [abs_nonneg ((AzRat.toRat q : ℚ) : ℝ)]
  exact asinhLn_spec hl hl0 hl1 hw hl2

/-- `asinhRatApprox` as a pair of `Roundable`s bracketing `asinh q`. -/
theorem asinhRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    ∃ lv hv : ℝ, Rounds (asinhRatApprox q w).1 lv ∧ Rounds (asinhRatApprox q w).2 hv ∧
      lv ≤ Real.arsinh (AzRat.toRat q : ℝ) ∧ Real.arsinh (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ asinhEps |((AzRat.toRat q : ℚ) : ℝ)| w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := asinhRatBracket_spec hw q
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec (!q.sign) hlo hhi h1 h2
  rw [asinh_abs_eq (toRat_neg_iff q h0)] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `asinh q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_asinh_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.arsinh (AzRat.toRat q : ℝ)) :=
  irrational_arsinh_rat (q := AzRat.toRat q)
    (fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp (by rw [h, Rat.cast_zero])))

/-- The Ziv certificate for `asinh q`. -/
theorem asinhRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (asinhRatApprox q (w₀ * 2 ^ f)).1
      (asinhRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (asinhRatApprox q) (irrational_asinh_toRat q h0)
    (asinhEps |((AzRat.toRat q : ℚ) : ℝ)|) (tendsto_asinhEps _) 64
    (fun _ hw => asinhRatApprox_spec hw q h0) w₀ hw₀

/-! ### Tiny arguments -/

/-- `asinh a < a` for `a > 0`. -/
theorem arsinh_lt_self {a : ℝ} (h0 : 0 < a) : Real.arsinh a < a := by
  have h := arsinh_lt_arsinh.mpr (self_lt_sinh_iff.mpr h0)
  rwa [arsinh_sinh] at h

/-- `a − a³ ≤ asinh a` for `a > 0`. -/
theorem sub_cube_le_arsinh {a : ℝ} (h0 : 0 < a) : a - a ^ 3 ≤ Real.arsinh a := by
  have hb0 : 0 < Real.arsinh a := arsinh_pos_iff.mpr h0
  rcases le_or_gt a 1 with h1 | h1
  · have hba := (arsinh_lt_self h0).le
    obtain ⟨-, hs⟩ := sinh_tiny_bounds (Real.arsinh a) hb0 (hba.trans h1)
    rw [sinh_arsinh] at hs
    have hcube : Real.arsinh a ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hb0.le hba 3
    linarith
  · have : a ≤ a ^ 3 := le_self_pow₀ h1.le (by norm_num)
    linarith

end Azurite.AzFloat
