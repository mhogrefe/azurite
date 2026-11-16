/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.Transcendental.Cos

/-!
# Equivalence: the bracket of `arccos x`

* Real analysis: `arccos_eq_two_arctan` (the half-angle identity), `irrational_arccos_rat`
  (from `irrational_cos_rat`).
* `acosQuot_spec` and `acosArg_spec` (relative error analysis; width at most `40·2^(−P)`),
  `atanDouble_spec` (the doubled `atanWiden`, width at most `2^(−w)/128`),
  `acosBracket_spec` (width at most `2^(−w)`), `acosApprox_spec`,
  `acosApprox_isSome_exists` (the Ziv certificate).
-/

open Real

namespace Azurite.AzFloat

/-! ### Real analysis -/

/-- The half-angle identity `arccos a = 2 arctan √((1 − a)/(1 + a))` for `0 ≤ a ≤ 1`. -/
theorem arccos_eq_two_arctan {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    arccos a = 2 * arctan (√((1 - a) / (1 + a))) := by
  set φ := arccos a with hφ
  have hφ0 : 0 ≤ φ := arccos_nonneg a
  have hφ1 : φ ≤ π / 2 := arccos_le_pi_div_two.mpr h0
  have hπ := pi_pos
  have hcos : cos φ = a := cos_arccos (by linarith) h1
  have hc2 : 0 < cos (φ / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs2 : 0 ≤ sin (φ / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have htan0 : 0 ≤ tan (φ / 2) := by
    rw [tan_eq_sin_div_cos]
    positivity
  have hsq : (1 - a) / (1 + a) = tan (φ / 2) ^ 2 := by
    rw [← hcos, tan_eq_sin_div_cos]
    have e1 : 1 - cos φ = 2 * sin (φ / 2) ^ 2 := by
      have := cos_sq' (φ / 2)
      have h2 := cos_sq (φ / 2)
      rw [show 2 * (φ / 2) = φ by ring] at h2
      linarith
    have e2 : 1 + cos φ = 2 * cos (φ / 2) ^ 2 := by
      have h2 := cos_sq (φ / 2)
      rw [show 2 * (φ / 2) = φ by ring] at h2
      linarith
    rw [e1, e2]
    field_simp
  rw [hsq, sqrt_sq htan0, arctan_tan (by linarith) (by linarith)]
  ring

/-- `arccos q` is irrational for a rational `q` in `[−1, 1)`. -/
theorem irrational_arccos_rat {q : ℚ} (h1 : -1 ≤ (q : ℝ)) (h2 : (q : ℝ) < 1) :
    Irrational (arccos q) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero] at hr
    exact absurd (arccos_eq_zero.mp hr.symm) (not_le.mpr h2)
  apply irrational_cos_rat hr0
  rw [hr, cos_arccos h1 h2.le]
  exact ⟨q, rfl⟩

/-! ### The argument -/

/-- **The enclosure of `Q = (1 − a)/(1 + a)`** for a float `0 < a < 1`, with relative accuracy:
`0 ≤ lo`, `(1 − 6ε) Q ≤ lo ≤ Q ≤ hi ≤ (1 + 8ε) Q`, `ε = 2^(−P)`. -/
theorem acosQuot_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) (h0 : 0 < av)
    (h1 : av < 1) {P : ℕ} (hP : 8 ≤ P) :
    ∃ ql qh : ℝ, (acosQuot a P).1.toVal = some (ql : EReal) ∧
      (acosQuot a P).2.toVal = some (qh : EReal) ∧ 0 ≤ ql ∧
      (1 - 6 * (1 / 2 : ℝ) ^ P) * ((1 - av) / (1 + av)) ≤ ql ∧ ql ≤ (1 - av) / (1 + av) ∧
      (1 - av) / (1 + av) ≤ qh ∧ qh ≤ (1 + 8 * (1 / 2 : ℝ) ^ P) * ((1 - av) / (1 + av)) := by
  unfold acosQuot
  dsimp only
  have : NeZero P := ⟨by omega⟩
  set ε := (1 / 2 : ℝ) ^ P with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 256 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hP
    rw [← hε] at this
    norm_num at this
    linarith
  have hεε : ε * ε ≤ ε / 256 := by nlinarith
  set D := 1 - av with hD
  set E := 1 + av with hE
  have hD0 : 0 < D := by rw [hD]; linarith
  have hE0 : 0 < E := by rw [hE]; linarith
  set Q := D / E with hQ
  have hQ0 : 0 < Q := div_pos hD0 hE0
  have hQE : Q * E = D := by rw [hQ, div_mul_cancel₀]; exact hE0.ne'
  have hQ1 : Q ≤ 1 := by
    rw [hQ, div_le_one hE0, hD, hE]
    linarith
  obtain ⟨dl, hdl, hdl1, hdl2⟩ := subFloor_abs toVal_one' ha P
  obtain ⟨dh, hdh, hdh1, hdh2⟩ := subCeiling_abs toVal_one' ha P
  obtain ⟨el, hel, hel1, hel2⟩ := addFloor_abs toVal_one' ha P
  obtain ⟨eh, heh, heh1, heh2⟩ := addCeiling_abs toVal_one' ha P
  rw [← hD, abs_of_pos hD0, ← hε] at hdl2 hdh2
  rw [← hD] at hdl1 hdh1
  rw [← hE, abs_of_pos hE0, ← hε] at hel2 heh2
  rw [← hE] at hel1 heh1
  have hDε : 0 ≤ D * ε := by positivity
  have hEε : 0 ≤ E * ε := by positivity
  have hdl0 : 0 ≤ dl := by nlinarith
  have hel0 : 0 < el := by nlinarith
  have hdh0 : 0 ≤ dh := by linarith
  have heh0 : 0 < eh := by linarith
  obtain ⟨ql, hql, hql0, hql1, hql2⟩ := divFloor_err hdl heh heh0 hdl0 P
  obtain ⟨qh, hqh, hqh1, hqh2⟩ := divCeiling_err hdh hel hel0 hdh0 P
  rw [← hε] at hql2 hqh2
  set X := dl / eh with hX
  set Y := dh / el with hY
  -- `(1 − 4ε) Q ≤ X ≤ Q`
  have hXQ : X ≤ Q := by
    rw [hX, hQ]
    exact (div_le_div_of_nonneg_right hdl1 heh0.le).trans
      (div_le_div_of_nonneg_left hD0.le hE0 heh1)
  have hX4 : (1 - 4 * ε) * Q ≤ X := by
    rw [hX, le_div_iff₀ heh0]
    have m1 : Q * eh ≤ Q * (E + 2 * E * ε) := mul_le_mul_of_nonneg_left heh2 hQ0.le
    have e1 : Q * (E + 2 * E * ε) = Q * E + 2 * (Q * E) * ε := by ring
    have e2 : (1 - 4 * ε) * Q * eh = (1 - 4 * ε) * (Q * eh) := by ring
    have m2 : (1 - 4 * ε) * (Q * eh) ≤ (1 - 4 * ε) * (D + 2 * D * ε) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [e1, hQE] at m1
      exact m1
    have e3 : (1 - 4 * ε) * (D + 2 * D * ε) = D - 2 * (D * ε) - 8 * (D * (ε * ε)) := by ring
    have m3 : 0 ≤ D * (ε * ε) := by positivity
    rw [e2]
    linarith
  -- `Q ≤ Y ≤ (1 + 5ε) Q`
  have hQY : Q ≤ Y := by
    rw [hY, hQ]
    exact (div_le_div_of_nonneg_right hdh1 hE0.le).trans
      (div_le_div_of_nonneg_left hdh0 hel0 hel1)
  have hY5 : Y ≤ (1 + 5 * ε) * Q := by
    rw [hY, div_le_iff₀ hel0]
    have m1 : Q * (E - 2 * E * ε) ≤ Q * el := mul_le_mul_of_nonneg_left (by linarith) hQ0.le
    have e1 : Q * (E - 2 * E * ε) = Q * E - 2 * (Q * E) * ε := by ring
    have e2 : (1 + 5 * ε) * Q * el = (1 + 5 * ε) * (Q * el) := by ring
    have m2 : (1 + 5 * ε) * (D - 2 * D * ε) ≤ (1 + 5 * ε) * (Q * el) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [e1, hQE] at m1
      exact m1
    have e3 : (1 + 5 * ε) * (D - 2 * D * ε) = D + 3 * (D * ε) - 10 * (D * (ε * ε)) := by ring
    have m3 : D * (ε * ε) ≤ D * (ε / 256) := mul_le_mul_of_nonneg_left hεε hD0.le
    rw [e2]
    linarith
  have hXε : X * ε ≤ Q * ε := mul_le_mul_of_nonneg_right hXQ hε0.le
  have hYε : Y * ε ≤ (1 + 5 * ε) * Q * ε := mul_le_mul_of_nonneg_right hY5 hε0.le
  have e4 : (1 + 5 * ε) * Q * ε = Q * ε + 5 * (Q * (ε * ε)) := by ring
  have m4 : Q * (ε * ε) ≤ Q * (ε / 256) := mul_le_mul_of_nonneg_left hεε hQ0.le
  have hQε : 0 ≤ Q * ε := by positivity
  refine ⟨ql, qh, hql, hqh, hql0, ?_, hql1.trans hXQ, hQY.trans hqh1, ?_⟩
  · have e5 : (1 - 6 * ε) * Q = Q - 6 * (Q * ε) := by ring
    have e6 : (1 - 4 * ε) * Q = Q - 4 * (Q * ε) := by ring
    rw [e5]
    linarith
  · have e5 : (1 + 8 * ε) * Q = Q + 8 * (Q * ε) := by ring
    have e6 : (1 + 5 * ε) * Q = Q + 5 * (Q * ε) := by ring
    rw [e5]
    linarith

/-- **The enclosure of `t = √((1 − a)/(1 + a))`** for a float `0 < a < 1`: nonnegative lower
end, width at most `40·2^(−P)`. -/
theorem acosArg_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) (h0 : 0 < av)
    (h1 : av < 1) {P : ℕ} (hP : 8 ≤ P) :
    ∃ tl th : ℝ, (acosArg a P).1.toVal = some (tl : EReal) ∧
      (acosArg a P).2.toVal = some (th : EReal) ∧ 0 ≤ tl ∧
      tl ≤ √((1 - av) / (1 + av)) ∧ √((1 - av) / (1 + av)) ≤ th ∧
      th - tl ≤ 40 * (1 / 2 : ℝ) ^ P := by
  unfold acosArg
  dsimp only
  have : NeZero P := ⟨by omega⟩
  obtain ⟨ql, qh, hql, hqh, hql0, hql6, hqlQ, hQqh, hqh8⟩ := acosQuot_spec ha h0 h1 hP
  set ε := (1 / 2 : ℝ) ^ P with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 256 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hP
    rw [← hε] at this
    norm_num at this
    linarith
  set Q := (1 - av) / (1 + av) with hQ
  have hQ0 : 0 < Q := div_pos (by linarith) (by linarith)
  have hQ1 : Q ≤ 1 := by
    rw [hQ, div_le_one (by linarith)]
    linarith
  set T := √Q with hT
  have hT0 : 0 ≤ T := sqrt_nonneg Q
  have hT1 : T ≤ 1 := sqrt_le_one.mpr hQ1
  have hqh0 : 0 ≤ qh := hQ0.le.trans hQqh
  obtain ⟨tl, htl, htl0, htl1, htl2⟩ := sqrtFloor_err hql hql0 P
  obtain ⟨th, hth, hth1, hth2⟩ := sqrtCeiling_err hqh hqh0 P
  rw [← hε] at htl2 hth2
  have hsl : (1 - 6 * ε) * T ≤ √ql := by
    have h1 : (1 - 6 * ε) ^ 2 * Q ≤ ql := by
      have : (1 - 6 * ε) ^ 2 * Q ≤ (1 - 6 * ε) * Q := by
        apply mul_le_mul_of_nonneg_right _ hQ0.le
        nlinarith
      linarith
    have h2 := sqrt_le_sqrt h1
    rwa [sqrt_mul (by positivity), sqrt_sq (by linarith)] at h2
  have hsh : √qh ≤ (1 + 8 * ε) * T := by
    have h1 : qh ≤ (1 + 8 * ε) ^ 2 * Q := by
      have : (1 + 8 * ε) * Q ≤ (1 + 8 * ε) ^ 2 * Q := by
        apply mul_le_mul_of_nonneg_right _ hQ0.le
        nlinarith
      linarith
    have h2 := sqrt_le_sqrt h1
    rwa [sqrt_mul (by positivity), sqrt_sq (by linarith)] at h2
  have hslT : √ql ≤ T := sqrt_le_sqrt hqlQ
  have hTsh : T ≤ √qh := sqrt_le_sqrt hQqh
  have hTε : T * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hT1 hε0.le
  have hTε0 : 0 ≤ T * ε := mul_nonneg hT0 hε0.le
  have m1 : √ql * ε ≤ T * ε := mul_le_mul_of_nonneg_right hslT hε0.le
  have m2 : √qh * ε ≤ (1 + 8 * ε) * T * ε := mul_le_mul_of_nonneg_right hsh hε0.le
  have e1 : (1 + 8 * ε) * T * ε = T * ε + 8 * (T * ε) * ε := by ring
  have m3 : T * ε * ε ≤ 1 * ε * (1 / 256) := mul_le_mul hTε hε1 hε0.le (by linarith)
  have e2 : (1 - 6 * ε) * T = T - 6 * (T * ε) := by ring
  have e3 : (1 + 8 * ε) * T = T + 8 * (T * ε) := by ring
  exact ⟨tl, th, htl, hth, htl0, htl1.trans hslT, hTsh.trans hth1, by linarith⟩

/-! ### The bracket -/

/-- **The doubled arctangent**: from an enclosure `[tl, th]` of `0 ≤ T ≤ 1` of width at most
`40·2^(−K−72)` with `0 ≤ tl`, the doubled `atanWiden` at level `K ≥ w + 8` encloses
`2 arctan T` with a nonnegative lower end, an upper end at most `4` and width at most
`2^(−w)/128`. -/
theorem atanDouble_spec {t : Encl} {T tl th : ℝ} (hT1 : T ≤ 1) {K w : ℕ} (hKw : w + 8 ≤ K)
    (htl : t.1.toVal = some (tl : EReal)) (hth : t.2.toVal = some (th : EReal))
    (htl0 : 0 ≤ tl) (htl1 : tl ≤ T) (hth1 : T ≤ th)
    (htw : th - tl ≤ 40 * (1 / 2 : ℝ) ^ (K + 64 + 8)) :
    ∃ lo hi : ℝ, ((atanWiden t.1 t.2 K (K + 64)).1 <<< AzInt.ofInt 1).toVal
        = some (lo : EReal) ∧
      ((atanWiden t.1 t.2 K (K + 64)).2 <<< AzInt.ofInt 1).toVal = some (hi : EReal) ∧
      0 ≤ lo ∧ lo ≤ 2 * arctan T ∧ 2 * arctan T ≤ hi ∧ hi ≤ 4 ∧
      hi - lo ≤ (1 / 2 : ℝ) ^ w / 128 := by
  have hd : th - tl ≤ 4 * (1 / 2 : ℝ) ^ (K + 64) := by
    have e : (1 / 2 : ℝ) ^ (K + 64 + 8) = (1 / 2 : ℝ) ^ (K + 64) / 256 := by
      rw [pow_add (1 / 2 : ℝ) (K + 64) 8]
      norm_num
      ring
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (K + 64) := by positivity
    rw [e] at htw
    linarith
  obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2, -, h3⟩ :=
    atanWiden_spec htl hth htl0 htl1 hth1 hT1 K hd
  have hlo2 : ((atanWiden t.1 t.2 K (K + 64)).1 <<< AzInt.ofInt 1).toVal
      = some ((lo * 2 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hlo (AzInt.ofInt 1)
    rw [h, AzInt.toInt_ofInt, zpow_one]
  have hhi2 : ((atanWiden t.1 t.2 K (K + 64)).2 <<< AzInt.ofInt 1).toVal
      = some ((hi * 2 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hhi (AzInt.ofInt 1)
    rw [h, AzInt.toInt_ofInt, zpow_one]
  have hKle : (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ (w + 8) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hKw
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
  have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 ^ 64 := by norm_num
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [h8] at hKle
  rw [pow_add] at h3
  have hwid : hi - lo ≤ (1 / 2 : ℝ) ^ w / 256 := by nlinarith
  have hat : arctan T ≤ 1 := by
    have h := arctan_strictMono.monotone hT1
    rw [arctan_one] at h
    linarith [pi_lt_four]
  exact ⟨lo * 2, hi * 2, hlo2, hhi2, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- **The bracket of `arccos x`** for `0 < |x| < 1`: width at most `2^(−w)`. -/
theorem acosBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) {neg : Bool} (hneg : neg = true ↔ xv < 0) (w : ℕ) :
    ∃ lo hi : ℝ, (acosBracket neg x w).1.toVal = some (lo : EReal) ∧
      (acosBracket neg x w).2.toVal = some (hi : EReal) ∧ lo ≤ arccos xv ∧
      arccos xv ≤ hi ∧ hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hT1 : √((1 - a) / (1 + a)) ≤ 1 := by
    apply sqrt_le_one.mpr
    rw [div_le_one (by linarith)]
    linarith
  have hid := arccos_eq_two_arctan ha0.le hx1.le
  unfold acosBracket
  dsimp only
  cases neg with
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    have hxa : xv = a := by rw [ha, abs_of_nonneg hpos]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hKw : w + 8 ≤ acosWork x.abs w := by
      unfold acosWork
      omega
    obtain ⟨tl, th, htl, hth, htl0, htl1, hth1, htw⟩ :=
      acosArg_spec habs ha0 hx1 (P := acosWork x.abs w + 64 + 8) (by omega)
    obtain ⟨lo, hi, hlo, hhi, -, h1, h2, -, h3⟩ :=
      atanDouble_spec hT1 hKw htl hth htl0 htl1 hth1 htw
    rw [← hid] at h1 h2
    rw [hxa]
    exact ⟨lo, hi, hlo, hhi, h1, h2, by linarith⟩
  | true =>
    have hlt : xv < 0 := hneg.mp rfl
    have hxa : xv = -a := by rw [ha, abs_of_neg hlt, neg_neg]
    simp only [↓reduceIte]
    obtain ⟨tl, th, htl, hth, htl0, htl1, hth1, htw⟩ :=
      acosArg_spec habs ha0 hx1 (P := w + 8 + 64 + 8) (by omega)
    obtain ⟨al, ah, hal, hah, hal0, h1, h2, hah4, h3⟩ :=
      atanDouble_spec hT1 (le_refl (w + 8)) htl hth htl0 htl1 hth1 htw
    rw [← hid] at h1 h2
    obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ := piShiftEncl_spec false false
      (A := ((atanWiden (acosArg x.abs (w + 8 + 64 + 8)).1 (acosArg x.abs (w + 8 + 64 + 8)).2
        (w + 8) (w + 8 + 64)).1 <<< AzInt.ofInt 1,
        (atanWiden (acosArg x.abs (w + 8 + 64 + 8)).1 (acosArg x.abs (w + 8 + 64 + 8)).2
        (w + 8) (w + 8 + 64)).2 <<< AzInt.ofInt 1))
      hal hah hal0 h1 h2 hah4 h3 (V := w + 72) (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
    have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
      have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
        rw [pow_add]
        norm_num
        ring
      rw [← h10]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [hxa, arccos_neg]
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩

/-- `acosApprox neg` as a pair of `Roundable`s bracketing `arccos x`. -/
theorem acosApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) {neg : Bool} (hneg : neg = true ↔ xv < 0) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (acosApprox neg x w).1 lv ∧ Rounds (acosApprox neg x w).2 hv ∧
      lv ≤ arccos xv ∧ arccos xv ≤ hv ∧ hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := acosBracket_spec hx hx0 hx1 hneg w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `arccos x` is irrational for a finite float `x` with `|x| < 1`. -/
theorem irrational_arccos_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx1 : |xv| < 1) : Irrational (arccos xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  obtain ⟨h1, h2⟩ := abs_lt.mp hx1
  rw [hq] at h1 h2 ⊢
  exact irrational_arccos_rat h1.le h2

/-- The Ziv certificate for `arccos x`, `x` a finite float with `0 < |x| < 1`. -/
theorem acosApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hx1 : |xv| < 1) (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acosApprox neg x (w₀ * 2 ^ f)).1
      (acosApprox neg x (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (acosApprox neg x)
    (irrational_arccos_of_toVal hx hx1) (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => acosApprox_spec hx hx0 hx1 hneg w) w₀ hw₀

end Azurite.AzFloat
