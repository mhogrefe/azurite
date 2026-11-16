/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.Equiv.TanBracket
import Azurite.Transcendental.Sinh

/-!
# Equivalence: the bracket of `sinh x`

`sinh_eq_expm1` (`sinh a = (u + u/(1 + u))/2`, `u = e^a − 1`), `sinhStep_bounds` (the real
arithmetic of the outward rounding), `sinhOfExpM1_spec`, `sinhOfExpM1_width` (width at most
`sinhWidth`, which tends to `0`: `tendsto_sinhWidth`), `sinhBracket_spec`, `sinhApprox_spec`,
`irrational_sinh_of_toVal`, `sinhApprox_isSome_exists` (the Ziv certificate),
`sinh_tiny_bounds` (`a < sinh a ≤ a + a³` on `(0, 1]`).
-/

open Real

namespace Azurite.AzFloat

/-- `sinh a = (u + u/(1 + u))/2` with `u = e^a − 1`. -/
theorem sinh_eq_expm1 (a : ℝ) :
    Real.sinh a = ((Real.exp a - 1) + (Real.exp a - 1) / (1 + (Real.exp a - 1))) / 2 := by
  have h := exp_pos a
  rw [sinh_eq, exp_neg]
  field_simp
  ring

/-- `u/(1 + u)` is increasing on `u ≥ 0`. -/
theorem div_one_add_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : u / (1 + u) ≤ v / (1 + v) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The difference of the two rounded quotients `uh/d2` and `ul/d1`. -/
theorem sinhQuot_diff {ul uh d1 d2 A1 A2 η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8)
    (hul0 : 0 ≤ ul) (hlh : ul ≤ uh) (hd1a : 1 + ul ≤ d1) (hd1b : d1 ≤ 1 + ul + 2 * (1 + ul) * η)
    (hd2b : 1 + uh ≤ d2 + 2 * (1 + uh) * η) (hA1 : A1 * d1 = ul)
    (hA2 : A2 * d2 = uh) : A2 - A1 ≤ 2 * (uh - ul) + η * (8 * uh + 8 * uh ^ 2) := by
  have huh0 : 0 ≤ uh := hul0.trans hlh
  have hd1 : 1 ≤ d1 := by linarith
  have hd2 : 3 / 4 ≤ d2 := by nlinarith
  have hprod : 3 / 4 ≤ d1 * d2 := by nlinarith
  have h1 : uh * d1 ≤ uh * (1 + ul + 2 * (1 + ul) * η) := mul_le_mul_of_nonneg_left hd1b huh0
  have h2 : ul * (1 + uh - 2 * (1 + uh) * η) ≤ ul * d2 :=
    mul_le_mul_of_nonneg_left (by linarith) hul0
  have hN : uh * d1 - ul * d2 ≤ (uh - ul) + 2 * η * (uh + ul + 2 * uh * ul) := by
    nlinarith
  have hulh : uh * ul ≤ uh * uh := mul_le_mul_of_nonneg_left hlh huh0
  have hN' : uh * d1 - ul * d2 ≤ (uh - ul) + η * (4 * uh + 4 * uh ^ 2) := by
    have : 2 * η * (uh + ul + 2 * uh * ul) ≤ η * (4 * uh + 4 * uh ^ 2) := by
      have : uh + ul + 2 * (uh * ul) ≤ 2 * uh + 2 * (uh * uh) := by linarith
      nlinarith
    linarith
  have hkey : (A2 - A1) * (d1 * d2) = uh * d1 - ul * d2 := by
    rw [← hA1, ← hA2]
    ring
  set N := (uh - ul) + η * (4 * uh + 4 * uh ^ 2) with hNdef
  have hN0 : 0 ≤ N := by
    have : 0 ≤ η * (4 * uh + 4 * uh ^ 2) := by positivity
    linarith
  by_contra hcon
  push Not at hcon
  have h3 : 2 * N < A2 - A1 := by
    have : 2 * N = 2 * (uh - ul) + η * (8 * uh + 8 * uh ^ 2) := by rw [hNdef]; ring
    linarith
  have h4 : 2 * N * (3 / 4) ≤ (A2 - A1) * (d1 * d2) :=
    mul_le_mul h3.le hprod (by norm_num) (by linarith)
  nlinarith

/-- The real arithmetic of `sinhOfExpM1`: the enclosure and its width. -/
theorem sinhStep_bounds {U ul uh d1 q1 s1 d2 q2 s2 η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8)
    (hul0 : 0 ≤ ul) (hulU : ul ≤ U) (hUuh : U ≤ uh)
    (hd1a : 1 + ul ≤ d1) (hd1b : d1 ≤ 1 + ul + 2 * |1 + ul| * η)
    (hq1a : q1 ≤ ul / d1) (hq1b : ul / d1 ≤ q1 + 2 * |ul / d1| * η)
    (hs1a : s1 ≤ ul + q1) (hs1b : ul + q1 ≤ s1 + 2 * |ul + q1| * η)
    (hd2a : d2 ≤ 1 + uh) (hd2b : 1 + uh ≤ d2 + 2 * |1 + uh| * η)
    (hq2a : uh / d2 ≤ q2) (hq2b : q2 ≤ uh / d2 + 2 * |uh / d2| * η)
    (hs2a : uh + q2 ≤ s2) (hs2b : s2 ≤ uh + q2 + 2 * |uh + q2| * η) :
    s1 ≤ U + U / (1 + U) ∧ U + U / (1 + U) ≤ s2 ∧
      s2 - s1 ≤ 3 * (uh - ul) + η * (40 * uh + 16 * uh ^ 2) := by
  have hU0 : 0 ≤ U := hul0.trans hulU
  have huh0 : 0 ≤ uh := hU0.trans hUuh
  rw [abs_of_nonneg (by linarith)] at hd1b hd2b
  have hd1 : 1 ≤ d1 := by linarith
  have hd2 : 3 / 4 ≤ d2 := by nlinarith
  have hA1 : 0 ≤ ul / d1 := div_nonneg hul0 (by linarith)
  have hA2 : 0 ≤ uh / d2 := div_nonneg huh0 (by linarith)
  rw [abs_of_nonneg hA1] at hq1b
  rw [abs_of_nonneg hA2] at hq2b
  have hA1u : ul / d1 ≤ ul := div_le_self hul0 hd1
  have hA1m : ul / d1 ≤ ul / (1 + ul) := div_le_div_of_nonneg_left hul0 (by linarith) hd1a
  have hA2m : uh / (1 + uh) ≤ uh / d2 := div_le_div_of_nonneg_left huh0 (by linarith) hd2a
  have hA2u : uh / d2 ≤ 2 * uh := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hq1 : 0 ≤ q1 := by nlinarith
  have hq2 : 0 ≤ q2 := hA2.trans hq2a
  rw [abs_of_nonneg (by linarith)] at hs1b hs2b
  have hm1 := div_one_add_mono hul0 hulU
  have hm2 := div_one_add_mono hU0 hUuh
  refine ⟨by linarith, by linarith, ?_⟩
  have hdiff := sinhQuot_diff hη0 hη hul0 (hulU.trans hUuh) hd1a hd1b hd2b
    (div_mul_cancel₀ ul (by linarith : d1 ≠ 0)) (div_mul_cancel₀ uh (by linarith : d2 ≠ 0))
  have hq2u : q2 ≤ 3 * uh := by nlinarith
  have hq1u : q1 ≤ ul := by linarith
  have e1 : (uh / d2) * η ≤ 2 * uh * η := mul_le_mul_of_nonneg_right hA2u hη0
  have e2 : (ul / d1) * η ≤ ul * η := mul_le_mul_of_nonneg_right hA1u hη0
  have e3 : (uh + q2) * η ≤ 4 * uh * η := mul_le_mul_of_nonneg_right (by linarith) hη0
  have e4 : (ul + q1) * η ≤ 2 * uh * η :=
    mul_le_mul_of_nonneg_right (by linarith [hulU.trans hUuh]) hη0
  have e5 : ul * η ≤ uh * η := mul_le_mul_of_nonneg_right (hulU.trans hUuh) hη0
  nlinarith

/-- **`sinhOfExpM1` encloses `(U + U/(1 + U))/2`** for an enclosure `[ul, uh]` of `U ≥ 0`. -/
theorem sinhOfExpM1_spec {u : Encl} {U ul uh : ℝ} (hlo : u.1.toVal = some (ul : EReal))
    (hhi : u.2.toVal = some (uh : EReal)) (hU0 : 0 ≤ U) (h1 : ul ≤ U) (h2 : U ≤ uh) {W : ℕ}
    (hW : 3 ≤ W) :
    IsEnclW (sinhOfExpM1 u W) ((U + U / (1 + U)) / 2)
      (3 * (uh - ul) + (1 / 2 : ℝ) ^ W * (40 * uh + 16 * uh ^ 2)) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hlo
  have hcU : cv ≤ U := hcvle.trans (max_le h1 hU0)
  have hrc : ul ≤ cv := by
    rcases le_or_gt 0 ul with h | h
    · rw [hcveq h]
    · linarith
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hη : (1 / 2 : ℝ) ^ W ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hW
      _ = 1 / 8 := by norm_num
  obtain ⟨d1, hd1, hd1a, hd1b⟩ := addCeiling_abs toVal_one' hcv W
  have hd1pos : (0 : ℝ) < d1 := by linarith
  obtain ⟨q1, hq1, hq1a, hq1b⟩ := divFloor_abs hcv hd1 hd1pos.ne' W
  obtain ⟨s1, hs1, hs1a, hs1b⟩ := addFloor_abs hcv hq1 W
  have huh0 : 0 ≤ uh := hU0.trans h2
  obtain ⟨d2, hd2, hd2a, hd2b⟩ := addFloor_abs toVal_one' hhi W
  have hd2pos : (0 : ℝ) < d2 := by
    rw [abs_of_nonneg (by linarith)] at hd2b
    nlinarith
  obtain ⟨q2, hq2, hq2a, hq2b⟩ := divCeiling_abs hhi hd2 hd2pos.ne' W
  obtain ⟨s2, hs2, hs2a, hs2b⟩ := addCeiling_abs hhi hq2 W
  obtain ⟨b1, b2, b3⟩ := sinhStep_bounds hη0 hη hcv0 hcU h2 hd1a hd1b hq1a hq1b hs1a hs1b
    hd2a hd2b hq2a hq2b hs2a hs2b
  have hsh1 := toVal_shiftLeft_of_toVal hs1 (AzInt.ofInt (-1))
  have hsh2 := toVal_shiftLeft_of_toVal hs2 (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at hsh1 hsh2
  have hpos : 0 ≤ (1 / 2 : ℝ) ^ W * (40 * uh + 16 * uh ^ 2) := by positivity
  exact ⟨s1 / 2, s2 / 2, hsh1, hsh2, by linarith, by linarith, by linarith⟩

/-- The width of `sinhOfExpM1` at precision `w + 16` on an enclosure of `U` of width `E`. -/
noncomputable def sinhWidth (U E : ℝ) (w : ℕ) : ℝ :=
  3 * E + (1 / 2 : ℝ) ^ w * (40 * (U + E) + 16 * (U + E) ^ 2)

theorem tendsto_sinhWidth (U : ℝ) {E : ℕ → ℝ} (hE : Filter.Tendsto E Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun w => sinhWidth U (E w) w) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hU := hE.const_add U
  have h := (hE.const_mul 3).add
    (hp.mul ((hU.const_mul 40).add ((hU.pow 2).const_mul 16)))
  have h0 : (3 * 0 + 0 * (40 * (U + 0) + 16 * (U + 0) ^ 2) : ℝ) = 0 := by ring
  rw [h0] at h
  exact h

/-- **`sinhOfExpM1` at precision `w + 16` encloses `sinh a`**, `a ≥ 0`, from an enclosure of
`e^a − 1` of width at most `E`, with width at most `sinhWidth (e^a − 1) E w`. -/
theorem sinhOfExpM1_width {u : Encl} {av lo hi E : ℝ} (hlo : u.1.toVal = some (lo : EReal))
    (hhi : u.2.toVal = some (hi : EReal)) (ha0 : 0 ≤ av) (h1 : lo ≤ Real.exp av - 1)
    (h2 : Real.exp av - 1 ≤ hi) (h3 : hi - lo ≤ E) (w : ℕ) :
    IsEnclW (sinhOfExpM1 u (w + 16)) (Real.sinh av) (sinhWidth (Real.exp av - 1) E w) := by
  have hU0 : 0 ≤ Real.exp av - 1 := by linarith [add_one_le_exp av]
  have hs := sinhOfExpM1_spec hlo hhi hU0 h1 h2 (W := w + 16) (by omega)
  rw [← sinh_eq_expm1] at hs
  refine hs.mono ?_
  unfold sinhWidth
  set U := Real.exp av - 1 with hUdef
  have hhiU : hi ≤ U + E := by linarith
  have hhi0 : 0 ≤ hi := hU0.trans h2
  have hpw : (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hsq : hi ^ 2 ≤ (U + E) ^ 2 := pow_le_pow_left₀ hhi0 hhiU 2
  have hin : 40 * hi + 16 * hi ^ 2 ≤ 40 * (U + E) + 16 * (U + E) ^ 2 := by linarith
  have hin0 : 0 ≤ 40 * hi + 16 * hi ^ 2 := by positivity
  have hm : (1 / 2 : ℝ) ^ (w + 16) * (40 * hi + 16 * hi ^ 2)
      ≤ (1 / 2 : ℝ) ^ w * (40 * (U + E) + 16 * (U + E) ^ 2) :=
    mul_le_mul hpw hin hin0 (by positivity)
  linarith

/-- The width bound of `sinhBracket` at compensation `c`. -/
noncomputable def sinhEps (av : ℝ) (c w : ℕ) : ℝ :=
  sinhWidth (Real.exp av - 1) (expM1Eps av c w) w

theorem tendsto_sinhEps (av : ℝ) (c : ℕ) :
    Filter.Tendsto (sinhEps av c) Filter.atTop (nhds 0) :=
  tendsto_sinhWidth _ (tendsto_expM1Eps av c)

/-- **`sinhBracket a e w` encloses `sinh a`** for a float `0 < a < 2^e`, with width at most
`sinhEps a (expM1Comp e) w`. -/
theorem sinhBracket_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) (e : AzInt) (hae : av < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (sinhBracket a e w) (Real.sinh av) (sinhEps av (expM1Comp e) w) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ :=
    expM1Bracket_spec ha e (by rwa [abs_of_pos ha0]) hw
  exact sinhOfExpM1_width hlo hhi ha0.le h1 h2 h3 w

/-- `sinh x` from `sinh |x|`. -/
theorem sinh_abs_eq {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    (if neg then -1 else 1) * Real.sinh |xv| = Real.sinh xv := by
  cases neg with
  | true =>
    have hlt : xv < 0 := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg hlt, sinh_neg]
    ring
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg hpos]

/-- `sinhApprox neg` as a pair of `Roundable`s bracketing `sinh x`. -/
theorem sinhApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {e : AzInt} (hxe : |xv| < (2 : ℝ) ^ e.toInt) {neg : Bool}
    (hneg : neg = true ↔ xv < 0) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sinhApprox neg x e w).1 lv ∧ Rounds (sinhApprox neg x e w).2 hv ∧
      lv ≤ Real.sinh xv ∧ Real.sinh xv ≤ hv ∧ hv - lv ≤ sinhEps |xv| (expM1Comp e) w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    sinhBracket_spec habs (abs_pos.mpr hx0) e hxe hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  rw [sinh_abs_eq hneg] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `sinh x` is irrational for a finite float `x ≠ 0`. -/
theorem irrational_sinh_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.sinh xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  rw [hq] at hx0 ⊢
  exact irrational_sinh_rat (by exact_mod_cast hx0)

/-- The Ziv certificate for `sinh x`, `x` a finite nonzero float. -/
theorem sinhApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {e : AzInt}
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (sinhApprox neg x e (w₀ * 2 ^ f)).1
      (sinhApprox neg x e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (sinhApprox neg x e)
    (irrational_sinh_of_toVal hx hx0) (sinhEps |xv| (expM1Comp e)) (tendsto_sinhEps _ _) 64
    (fun _ hw => sinhApprox_spec hx hx0 hxe hneg hw) w₀ hw₀

/-- `a < sinh a ≤ a + a³` for `0 < a ≤ 1`. -/
theorem sinh_tiny_bounds (a : ℝ) (h0 : 0 < a) (h1 : a ≤ 1) :
    a < Real.sinh a ∧ Real.sinh a ≤ a + a ^ 3 := by
  refine ⟨self_lt_sinh_iff.mpr h0, ?_⟩
  have hb1 := exp_bound (x := a) (by rw [abs_of_pos h0]; exact h1) (n := 4) (by norm_num)
  have hb2 := exp_bound (x := -a) (by rw [abs_neg, abs_of_pos h0]; exact h1) (n := 4)
    (by norm_num)
  rw [abs_neg] at hb2
  rw [abs_of_pos h0] at hb1 hb2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb1 hb2
  have h4 : a ^ 4 ≤ a ^ 3 := by
    have : a ^ 4 = a ^ 3 * a := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) h1
  have ha3 : 0 ≤ a ^ 3 := by positivity
  have ha4 : 0 ≤ a ^ 4 := by positivity
  have u1 := (abs_le.mp hb1).2
  have u2 := (abs_le.mp hb2).1
  rw [sinh_eq]
  norm_num at u1 u2
  nlinarith

end Azurite.AzFloat
