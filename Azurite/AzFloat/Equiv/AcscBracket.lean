/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscBracket
import Azurite.AzFloat.Equiv.AcosBracket
import Azurite.AzFloat.Equiv.AsinBracket

/-!
# Equivalence: the bracket of `arccsc x`

`arcsin_inv_eq_two_arctan` (`arcsin (1/a) = 2 arctan (1/(a + (a + 1) √((a − 1)/(a + 1))))` for
`a > 1`), `acscArg_spec` (width at most `40·2^(−P)`), `acscTinyEncl_spec`,
`acscBracket_spec` (the enclosure of `arcsin (1/|x|)`, nonnegative lower end, width at most
`2^(−w)`), `acscApprox_spec`, `irrational_acsc_of_toVal`, `acscApprox_isSome_exists` (the Ziv
certificate), `two_pow_le_of_exponent`, `acsc_abs_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- `arcsin (1/a) = 2 arctan (1/(a + √(a² − 1)))` for `a > 1`, the root written as
`(a + 1) √((a − 1)/(a + 1))`. -/
theorem arcsin_inv_eq_two_arctan {a : ℝ} (h1 : 1 < a) :
    arcsin a⁻¹ = 2 * arctan (1 / (a + (a + 1) * √((a - 1) / (a + 1)))) := by
  have ha0 : 0 < a := by linarith
  have hE : 0 < a + 1 := by linarith
  set R := √((a - 1) / (a + 1)) with hR
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have hR2 : R ^ 2 = (a - 1) / (a + 1) := sq_sqrt (div_nonneg (by linarith) hE.le)
  set S := (a + 1) * R with hS
  have hS0 : 0 ≤ S := mul_nonneg hE.le hR0
  have hS2 : S ^ 2 = a ^ 2 - 1 := by
    rw [hS, mul_pow, hR2]
    field_simp
    ring
  have hroot : √(1 - a⁻¹ ^ 2) = S / a := by
    have : 1 - a⁻¹ ^ 2 = (S / a) ^ 2 := by
      rw [div_pow, hS2]
      field_simp
    rw [this, sqrt_sq (div_nonneg hS0 ha0.le)]
  rw [arcsin_eq_two_arctan (inv_nonneg.mpr ha0.le) (inv_le_one_of_one_le₀ h1.le), hroot]
  congr 2
  have hpos : 0 < a + S := by linarith
  field_simp

/-- The real arithmetic of `acscArg`, first half: the enclosure of `D = a + (a + 1) R` from
those of `R ∈ [0, 1]` (absolute error `40ε`) and directed roundings of relative error `2ε`. -/
theorem acscArg_sum {av R ε rl rh el eh sl sh dl dh : ℝ} (h1 : 1 < av) (hR0 : 0 ≤ R)
    (hR1 : R ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2048) (hrl0 : 0 ≤ rl) (hrl1 : rl ≤ R)
    (hrh1 : R ≤ rh) (hrw : rh - rl ≤ 40 * ε) (hel1 : el ≤ av + 1)
    (hel2 : av + 1 ≤ el + 2 * |av + 1| * ε) (heh1 : av + 1 ≤ eh)
    (heh2 : eh ≤ av + 1 + 2 * |av + 1| * ε) (hsl1 : sl ≤ el * rl)
    (hsl2 : el * rl ≤ sl + 2 * |el * rl| * ε) (hsh1 : eh * rh ≤ sh)
    (hsh2 : sh ≤ eh * rh + 2 * |eh * rh| * ε) (hdl1 : dl ≤ av + sl)
    (hdl2 : av + sl ≤ dl + 2 * |av + sl| * ε) (hdh1 : av + sh ≤ dh)
    (hdh2 : dh ≤ av + sh + 2 * |av + sh| * ε) :
    (av + (av + 1) * R) * (1 - 90 * ε) ≤ dl ∧ dl ≤ av + (av + 1) * R ∧
      av + (av + 1) * R ≤ dh ∧ dh ≤ (av + (av + 1) * R) * (1 + 100 * ε) := by
  set E := av + 1 with hE
  have hE0 : 0 < E := by rw [hE]; linarith
  set S := E * R with hS
  have hS0 : 0 ≤ S := mul_nonneg hE0.le hR0
  have hSE : S ≤ E := by
    have := mul_le_mul_of_nonneg_left hR1 hE0.le
    rw [mul_one] at this
    exact this
  set D := av + S with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hED : E ≤ 2 * D := by rw [hE, hD]; linarith
  rw [abs_of_pos hE0] at hel2 heh2
  have hel0 : 0 ≤ el := by nlinarith
  have heh0 : 0 ≤ eh := by linarith
  have hrh0 : 0 ≤ rh := by linarith
  have hrh2 : rh ≤ 2 := by linarith
  rw [abs_of_nonneg (mul_nonneg hel0 hrl0)] at hsl2
  rw [abs_of_nonneg (mul_nonneg heh0 hrh0)] at hsh2
  have hlrS : el * rl ≤ S := mul_le_mul hel1 hrl1 hrl0 hE0.le
  have hSeh : S ≤ eh * rh := mul_le_mul heh1 hrh1 hR0 heh0
  have hlow : S - el * rl ≤ 42 * ε * E := by
    have e1 : S - el * rl = (E - el) * R + el * (R - rl) := by rw [hS]; ring
    have a1 : (E - el) * R ≤ (2 * E * ε) * 1 :=
      mul_le_mul (by linarith) hR1 hR0 (by positivity)
    have a2 : el * (R - rl) ≤ E * (40 * ε) :=
      mul_le_mul hel1 (by linarith) (by linarith) hE0.le
    rw [e1]
    linarith
  have hupp : eh * rh - S ≤ 44 * ε * E := by
    have e1 : eh * rh - S = (eh - E) * rh + E * (rh - R) := by rw [hS]; ring
    have a1 : (eh - E) * rh ≤ (2 * E * ε) * 2 :=
      mul_le_mul (by linarith) hrh2 hrh0 (by positivity)
    have a2 : E * (rh - R) ≤ E * (40 * ε) :=
      mul_le_mul_of_nonneg_left (by linarith) hE0.le
    rw [e1]
    linarith
  have hεE : 0 ≤ ε * E := by positivity
  have hεD : 0 ≤ ε * D := by positivity
  have hεED : ε * E ≤ 2 * (ε * D) := by
    have := mul_le_mul_of_nonneg_left hED hε0.le
    linarith
  have hεE1 : ε * E ≤ E / 2048 := by
    have := mul_le_mul_of_nonneg_right hε1 hE0.le
    linarith
  have hsl0 : 0 ≤ sl := by
    have h0 : 0 ≤ el * rl := mul_nonneg hel0 hrl0
    have : (el * rl) * ε ≤ (el * rl) * (1 / 2048) := mul_le_mul_of_nonneg_left hε1 h0
    linarith
  have hslow : S - sl ≤ 44 * (ε * E) := by
    have : (el * rl) * ε ≤ E * ε := mul_le_mul_of_nonneg_right (hlrS.trans hSE) hε0.le
    linarith
  have hsupp : sh - S ≤ 48 * (ε * E) := by
    have h2E : eh * rh ≤ 2 * E := by linarith
    have : (eh * rh) * ε ≤ (2 * E) * ε := mul_le_mul_of_nonneg_right h2E hε0.le
    linarith
  rw [abs_of_nonneg (by linarith)] at hdl2
  rw [abs_of_nonneg (by linarith)] at hdh2
  refine ⟨?_, by rw [hD]; linarith, by rw [hD]; linarith, ?_⟩
  · have : (av + sl) * ε ≤ D * ε := mul_le_mul_of_nonneg_right (by rw [hD]; linarith) hε0.le
    have hDe : D - dl ≤ 44 * (ε * E) + 2 * (D * ε) := by rw [hD]; linarith
    linarith
  · have h3 : av + sh ≤ D + 96 * (ε * D) := by rw [hD]; linarith
    have h4 : (av + sh) * ε ≤ (D + 96 * (ε * D)) * ε := mul_le_mul_of_nonneg_right h3 hε0.le
    have h5 : (ε * D) * ε ≤ (ε * D) / 2048 := by
      have := mul_le_mul_of_nonneg_left hε1 hεD
      linarith
    linarith

/-- The real arithmetic of `acscArg`, second half: the directed reciprocals of an enclosure of
`D ≥ 1` with relative errors `90ε`, `100ε` enclose `1/D` with width at most `320ε`. -/
theorem acscArg_quot {D ε dl dh tl th : ℝ} (hD1 : 1 ≤ D) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2048)
    (hdl90 : D * (1 - 90 * ε) ≤ dl) (hdlD : dl ≤ D) (hDdh : D ≤ dh)
    (hdh100 : dh ≤ D * (1 + 100 * ε)) (htl1 : tl ≤ 1 / dh)
    (htl2 : 1 / dh ≤ tl + 2 * |1 / dh| * ε) (hth1 : 1 / dl ≤ th)
    (hth2 : th ≤ 1 / dl + 2 * |1 / dl| * ε) :
    0 ≤ tl ∧ tl ≤ 1 / D ∧ 1 / D ≤ th ∧ th - tl ≤ 320 * ε := by
  have hD0 : 0 < D := by linarith
  have hεε : ε * ε ≤ ε / 2048 := by nlinarith
  set T := 1 / D with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  have hT1 : T ≤ 1 := by
    rw [hT, div_le_one hD0]
    exact hD1
  have hTD : T * D = 1 := by
    rw [hT]
    field_simp
  have hdl0 : 0 < dl := lt_of_lt_of_le (mul_pos hD0 (by linarith)) hdl90
  have hdh0 : 0 < dh := by linarith
  have hu0 : 0 < 1 / dh := by positivity
  have hv0 : 0 < 1 / dl := by positivity
  rw [abs_of_pos hu0] at htl2
  rw [abs_of_pos hv0] at hth2
  generalize hu : 1 / dh = u at htl1 htl2 hu0
  generalize hv : 1 / dl = v at hth1 hth2 hv0
  have huT : u ≤ T := by
    rw [← hu, hT]
    exact one_div_le_one_div_of_le hD0 hDdh
  have hTv : T ≤ v := by
    rw [← hv, hT]
    exact one_div_le_one_div_of_le hdl0 hdlD
  have hTu : T * (1 - 100 * ε) ≤ u := by
    rw [← hu, le_div_iff₀ hdh0]
    have h100 : 0 ≤ 1 - 100 * ε := by linarith
    calc T * (1 - 100 * ε) * dh ≤ T * (1 - 100 * ε) * (D * (1 + 100 * ε)) :=
          mul_le_mul_of_nonneg_left hdh100 (mul_nonneg hT0.le h100)
      _ = T * D * (1 - 10000 * (ε * ε)) := by ring
      _ ≤ 1 := by
          rw [hTD]
          nlinarith
  have hvT : v ≤ T * (1 + 95 * ε) := by
    rw [← hv, div_le_iff₀ hdl0]
    calc (1 : ℝ) ≤ T * D * (1 + 5 * ε - 8550 * (ε * ε)) := by
          rw [hTD]
          linarith
      _ = T * (1 + 95 * ε) * (D * (1 - 90 * ε)) := by ring
      _ ≤ T * (1 + 95 * ε) * dl :=
          mul_le_mul_of_nonneg_left hdl90 (by positivity)
  have hεT : 0 ≤ ε * T := by positivity
  have hεu : u * ε ≤ T * ε := mul_le_mul_of_nonneg_right huT hε0.le
  have hεv : v * ε ≤ (2 * T) * ε := by
    refine mul_le_mul_of_nonneg_right ?_ hε0.le
    have : T * (95 * ε) ≤ T * 1 := mul_le_mul_of_nonneg_left (by linarith) hT0.le
    linarith
  have htl0 : 0 ≤ tl := by
    have : u * ε ≤ u * (1 / 2048) := mul_le_mul_of_nonneg_left hε1 hu0.le
    linarith
  have hεT1 : ε * T ≤ ε := by
    have := mul_le_mul_of_nonneg_left hT1 hε0.le
    linarith
  exact ⟨htl0, htl1.trans huT, hTv.trans hth1, by linarith⟩

/-- **The argument of the arctangent**: `acscArg a P` encloses `1/(a + √(a² − 1))` with a
nonnegative lower end and width at most `40·2^(−P)`. -/
theorem acscArg_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) (h1 : 1 < av)
    {P : ℕ} (hP : 8 ≤ P) :
    ∃ tl th : ℝ, (acscArg a P).1.toVal = some (tl : EReal) ∧
      (acscArg a P).2.toVal = some (th : EReal) ∧ 0 ≤ tl ∧
      tl ≤ 1 / (av + (av + 1) * √((av - 1) / (av + 1))) ∧
      1 / (av + (av + 1) * √((av - 1) / (av + 1))) ≤ th ∧
      th - tl ≤ 40 * (1 / 2 : ℝ) ^ P := by
  have : NeZero (P + 3) := ⟨by omega⟩
  have hε0 : 0 < (1 / 2 : ℝ) ^ (P + 3) := by positivity
  have hε1 : (1 / 2 : ℝ) ^ (P + 3) ≤ 1 / 2048 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (show 11 ≤ P + 3 by omega)
    norm_num at this
    linarith
  have hεP : (1 / 2 : ℝ) ^ P = 8 * (1 / 2 : ℝ) ^ (P + 3) := by ring
  have hR0 : 0 ≤ √((av - 1) / (av + 1)) := sqrt_nonneg _
  have hR1 : √((av - 1) / (av + 1)) ≤ 1 := by
    apply sqrt_le_one.mpr
    rw [div_le_one (by linarith)]
    linarith
  have hD1 : 1 ≤ av + (av + 1) * √((av - 1) / (av + 1)) := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ av + 1) hR0
    linarith
  obtain ⟨rl, rh, hrl, hrh, hrl0, hrl1, hrh1, hrw⟩ :=
    diffQuotSqrt_spec ha toVal_one' one_pos h1 (P := P + 3) (by omega)
  obtain ⟨el, hel, hel1, hel2⟩ := addFloor_abs ha toVal_one' (P + 3)
  obtain ⟨eh, heh, heh1, heh2⟩ := addCeiling_abs ha toVal_one' (P + 3)
  obtain ⟨sl, hsl, hsl1, hsl2⟩ := mulFloor_abs hel hrl (P + 3)
  obtain ⟨sh, hsh, hsh1, hsh2⟩ := mulCeiling_abs heh hrh (P + 3)
  obtain ⟨dl, hdl, hdl1, hdl2⟩ := addFloor_abs ha hsl (P + 3)
  obtain ⟨dh, hdh, hdh1, hdh2⟩ := addCeiling_abs ha hsh (P + 3)
  obtain ⟨hdl90, hdlD, hDdh, hdh100⟩ := acscArg_sum h1 hR0 hR1 hε0 hε1 hrl0 hrl1 hrh1 hrw
    hel1 hel2 heh1 heh2 hsl1 hsl2 hsh1 hsh2 hdl1 hdl2 hdh1 hdh2
  have hdl0 : 0 < dl := lt_of_lt_of_le (mul_pos (by linarith) (by linarith)) hdl90
  have hdh0 : 0 < dh := by linarith
  obtain ⟨tl, htl, htl1, htl2⟩ := divFloor_abs toVal_one' hdh hdh0.ne' (P + 3)
  obtain ⟨th, hth, hth1, hth2⟩ := divCeiling_abs toVal_one' hdl hdl0.ne' (P + 3)
  obtain ⟨htl0, htlT, hTth, hwid⟩ := acscArg_quot hD1 hε0 hε1 hdl90 hdlD hDdh hdh100
    htl1 htl2 hth1 hth2
  exact ⟨tl, th, htl, hth, htl0, htlT, hTth, by rw [hεP]; linarith⟩

/-- **The enclosure for a huge argument**: for a float `a > 0` with `y = 1/a ≤ 1/2` and
`y² ≤ 2^(−w−14)`, `acscTinyEncl a w` encloses every `v` with `y ≤ v ≤ y + y³` (the arcsine and
the inverse hyperbolic tangent of `y`), with a nonnegative lower end and width at most
`2^(−w)`. -/
theorem acscTinyEncl_spec_of {a : AzFloat} {av v : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) (hy1 : av⁻¹ ≤ 1 / 2) {w : ℕ} (hy2 : av⁻¹ ^ 2 ≤ (1 / 2 : ℝ) ^ (w + 14))
    (hlt : av⁻¹ ≤ v) (hle : v ≤ av⁻¹ + av⁻¹ ^ 3) :
    IsEncl0W (acscTinyEncl a w) v ((1 / 2 : ℝ) ^ w) := by
  unfold acscTinyEncl
  dsimp only
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
  obtain ⟨cv, hc, hc1, hc2⟩ := addCeiling_abs toVal_one' hsh (w + 16)
  rw [abs_of_pos (by positivity), ← hε] at hc2
  have hc7 : cv ≤ 1 + 7 * ε := by nlinarith
  -- the quotients
  obtain ⟨l, hl, hl1, hl2⟩ := divFloor_abs toVal_one' ha ha0.ne' (w + 16)
  obtain ⟨h0, hh0, hh1, hh2⟩ := divCeiling_abs toVal_one' ha ha0.ne' (w + 16)
  rw [hdiv] at hl1 hl2 hh1 hh2
  rw [abs_of_pos hy0, ← hε] at hl2 hh2
  have hyε : 0 ≤ y * ε := by positivity
  have hyε1 : y * ε ≤ y / 65536 := by
    have := mul_le_mul_of_nonneg_left hε1 hy0.le
    linarith
  have hl0 : 0 ≤ l := by linarith
  have hh00 : 0 ≤ h0 := by linarith
  have hcv0 : 0 ≤ cv := by linarith
  obtain ⟨u, hu, hu1, hu2⟩ := mulCeiling_abs hh0 hc (w + 16)
  rw [abs_of_nonneg (mul_nonneg hh00 hcv0), ← hε] at hu2
  have hprod : h0 * cv ≤ y * (1 + 10 * ε) := by
    calc h0 * cv ≤ (y + 2 * y * ε) * (1 + 7 * ε) :=
          mul_le_mul hh2 hc7 hcv0 (by linarith)
      _ = y + 9 * (y * ε) + 14 * (y * ε) * ε := by ring
      _ ≤ y * (1 + 10 * ε) := by
          have : (y * ε) * ε ≤ (y * ε) / 65536 := by
            have := mul_le_mul_of_nonneg_left hε1 hyε
            linarith
          linarith
  have hprodε : (h0 * cv) * ε ≤ (2 * y) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε0.le
  have hcube : y ^ 3 ≤ y * (4 * ε) := by
    have := mul_le_mul_of_nonneg_left hy2 hy0.le
    calc y ^ 3 = y * y ^ 2 := by ring
      _ ≤ y * (4 * ε) := this
  have hyc : y * (1 + 4 * ε) ≤ h0 * cv := mul_le_mul hh1 hc1 (by linarith) hh00
  have hy12 : y * ε ≤ ε / 2 := by
    have := mul_le_mul_of_nonneg_right hy1 hε0.le
    linarith
  refine ⟨l, u, hl, hu, hl0, by linarith, by linarith, ?_⟩
  rw [hw]
  linarith

/-- The enclosure for a huge argument, for the arcsine. -/
theorem acscTinyEncl_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) (hy1 : av⁻¹ ≤ 1 / 2) {w : ℕ} (hy2 : av⁻¹ ^ 2 ≤ (1 / 2 : ℝ) ^ (w + 14)) :
    IsEncl0W (acscTinyEncl a w) (arcsin av⁻¹) ((1 / 2 : ℝ) ^ w) := by
  obtain ⟨hlt, hle⟩ := arcsin_bounds_of_small (inv_pos.mpr ha0) hy1
  exact acscTinyEncl_spec_of ha ha0 hy1 hy2 hlt.le hle

/-- **The bracket of `arccsc |x| = arcsin (1/|x|)`** for a finite float with `|x| > 1` and
`2^en ≤ 2|x|`: nonnegative lower end, width at most `2^(−w)`. -/
theorem acscBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) {en : ℕ} (hen : (2 : ℝ) ^ en ≤ 2 * |xv|) (w : ℕ) :
    IsEncl0W (acscBracket x en w) (arcsin |xv|⁻¹) ((1 / 2 : ℝ) ^ w) := by
  set a := |xv| with ha
  have ha0 : 0 < a := by linarith
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  unfold acscBracket
  dsimp only
  split_ifs with hc
  · have hy0 : 0 < a⁻¹ := inv_pos.mpr ha0
    have h2 : a⁻¹ * (2 : ℝ) ^ en ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hen hy0.le
      have e1 : a⁻¹ * (2 * a) = 2 := by field_simp
      linarith
    have hyle : a⁻¹ ≤ 2 * (1 / 2 : ℝ) ^ en := by
      have e1 : a⁻¹ = a⁻¹ * (2 : ℝ) ^ en * (1 / 2 : ℝ) ^ en := by
        rw [mul_assoc, ← mul_pow]
        norm_num
      rw [e1]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hen8 : (1 / 2 : ℝ) ^ en ≤ (1 / 2 : ℝ) ^ 8 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    refine acscTinyEncl_spec habs ha0 ?_ ?_
    · norm_num at hen8
      linarith
    · calc a⁻¹ ^ 2 ≤ (2 * (1 / 2 : ℝ) ^ en) ^ 2 := pow_le_pow_left₀ hy0.le hyle 2
        _ = 4 * (1 / 2 : ℝ) ^ (2 * en) := by
            rw [mul_pow, ← pow_mul, mul_comm en 2]
            norm_num
        _ ≤ 4 * (1 / 2 : ℝ) ^ (w + 16) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one (by norm_num) (by norm_num) hc) (by norm_num)
        _ = (1 / 2 : ℝ) ^ (w + 14) := by ring
  · have hid := arcsin_inv_eq_two_arctan hx1
    have hT1 : 1 / (a + (a + 1) * √((a - 1) / (a + 1))) ≤ 1 := by
      have h0 : 0 ≤ (a + 1) * √((a - 1) / (a + 1)) :=
        mul_nonneg (by linarith) (sqrt_nonneg _)
      rw [div_le_one (by linarith)]
      linarith
    obtain ⟨tl, th, htl, hth, htl0, htl1, hth1, htw⟩ :=
      acscArg_spec habs hx1 (P := w + 8 + en + 64 + 8) (by omega)
    obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2, -, h3⟩ :=
      atanDouble_spec hT1 (show w + 8 ≤ w + 8 + en by omega) htl hth htl0 htl1 hth1 htw
    rw [← hid] at h1 h2
    have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    exact ⟨lo, hi, hlo, hhi, hlo0, h1, h2, by linarith⟩

/-- `acscApprox` as a pair of `Roundable`s bracketing `arcsin (1/|x|)`. -/
theorem acscApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 < |xv|) {en : ℕ} (hen : (2 : ℝ) ^ en ≤ 2 * |xv|) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (acscApprox x en w).1 lv ∧ Rounds (acscApprox x en w).2 hv ∧
      lv ≤ arcsin |xv|⁻¹ ∧ arcsin |xv|⁻¹ ≤ hv ∧ hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, -, h1, h2, hwid⟩ := acscBracket_spec hx hx1 hen w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `arccsc x = arcsin (1/x)` is irrational for a finite float `x` with `|x| ≥ 1`. -/
theorem irrational_acsc_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : 1 ≤ |xv|) : Irrational (arcsin xv⁻¹) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hx0 : xv ≠ 0 := fun h => by
    rw [h, abs_zero] at hx1
    linarith
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hq, Rat.cast_zero])
  have hinv : |xv⁻¹| ≤ 1 := by
    rw [abs_inv]
    exact inv_le_one_of_one_le₀ hx1
  obtain ⟨h1, h2⟩ := abs_le.mp hinv
  rw [hq, ← Rat.cast_inv] at h1 h2 ⊢
  exact irrational_arcsin_rat (inv_ne_zero hq0) h1 h2

/-- The Ziv certificate for `arccsc |x|`, `x` a finite float with `|x| > 1`. -/
theorem acscApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat}
    {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : 1 < |xv|) {en : ℕ}
    (hen : (2 : ℝ) ^ en ≤ 2 * |xv|) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acscApprox x en (w₀ * 2 ^ f)).1
      (acscApprox x en (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have habs : (x.abs).toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  exact exists_isSome_of_irrational_threshold p mode (acscApprox x en)
    (irrational_acsc_of_toVal habs (by rw [abs_abs]; exact hx1.le)) (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => acscApprox_spec hx hx1 hen w) w₀ hw₀

/-- A float of exponent `e ≥ 1` has `2^e ≤ 2|x|`. -/
theorem two_pow_le_of_exponent {xv : ℝ} {e : AzInt} (hex1 : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|)
    (he : e.sign = true ∧ e.abs.toNat ≠ 0) : (2 : ℝ) ^ e.abs.toNat ≤ 2 * |xv| := by
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [he.1] at htoInt
  simp only [↓reduceIte] at htoInt
  rw [htoInt, zpow_sub_one₀ (by norm_num), zpow_natCast] at hex1
  linarith

/-- `arcsin (1/|x|) = ± arcsin (1/x)`. -/
theorem acsc_abs_eq {o : Bool} {xv : ℝ} (ho : o = true ↔ xv < 0) :
    arcsin |xv|⁻¹ = (if o then -1 else 1) * arcsin xv⁻¹ := by
  cases o with
  | true =>
    simp only [↓reduceIte]
    rw [abs_of_neg (ho.mp rfl), inv_neg, arcsin_neg]
    ring
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using ho.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg hpos]

end Azurite.AzFloat
