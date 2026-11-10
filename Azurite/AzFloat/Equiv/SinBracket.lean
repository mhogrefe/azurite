/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinBracket
import Azurite.AzFloat.Equiv.CosRatBracket

/-!
# Equivalence: the bracket of `sin x`

`sinBracket_spec`
(`sinBracket x ex w` encloses `sin |x|` with width `sinEps ex w`), `tendsto_sinEps`,
`sinApprox_spec`, `irrational_sin_of_toVal`, `sinApprox_isSome_exists` (the Ziv certificate
from `irrational_sin_rat`), `sinTiny?_eq`.
-/

namespace Azurite.AzFloat

/-- The width of `sinBracket` at the series precision `V`. -/
noncomputable def sinEpsW (V : ℕ) : ℝ :=
  216 * (cosSeriesEps V + 80 * (1 / 2 : ℝ) ^ V) + 3440 * (1 / 2 : ℝ) ^ V

/-- The width of `sinBracket x ex w` (independent of the exponent). -/
noncomputable def sinEps (_ex : AzInt) (w : ℕ) : ℝ := sinEpsW (w + 12)

set_option maxHeartbeats 800000 in
/-- **`sinBracket` encloses `sin |x|`** for a float `x` with `|x| < 2^ex`, at Ziv level
`w ≥ 64`, with width at most `sinEps ex w`. -/
theorem sinBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (sinBracket x ex w).1.toVal = some (lo : EReal) ∧
      (sinBracket x ex w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.sin |xv| ∧ Real.sin |xv| ≤ hi ∧ hi - lo ≤ sinEps ex w := by
  have hW64 : 64 ≤ cosWork ex w := by unfold cosWork; omega
  have hV64 : 64 ≤ w + 12 := by omega
  have hexu := two_zpow_mul_half_pow_cosWork ex w
  simp only [sinBracket]
  set W := cosWork ex w with hWdef
  have : NeZero W := ⟨by omega⟩
  have : NeZero (64 : ℕ) := ⟨by norm_num⟩
  have : NeZero (w + 12) := ⟨by omega⟩
  set P := piBracket W with hP
  set y := P.1 <<< AzInt.ofInt 1 with hy
  set r := remExact x.abs y with hr
  set u := (1 / 2 : ℝ) ^ W with hu
  set uV := (1 / 2 : ℝ) ^ (w + 12) with huV
  have hu0 : 0 ≤ u := by positivity
  have huV0 : 0 ≤ uV := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hW64
  have huVs : uV ≤ 1 / 10 ^ 18 := half_pow_small hV64
  have huuV : u ≤ uV :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by rw [hWdef]; unfold cosWork; omega)
  have hex' : |xv| ≤ 2 ^ ex.toInt := hex.le
  have hx0 := abs_nonneg xv
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  -- π
  obtain ⟨lv, hv, hlv, hhv, hlv0, hlvπ, hπhv, hwid⟩ := piBracket_spec_width hW64
  rw [← hu] at hwid
  have hlv1 : 1 ≤ lv := by linarith
  have hlv' : P.1.toVal = some (lv : EReal) := hlv
  have hhv' : P.2.toVal = some (hv : EReal) := hhv
  have hyv : y.toVal = some ((2 * lv : ℝ) : EReal) := toVal_shiftLeft_one hlv'
  have h2lv : (0 : ℝ) < 2 * lv := by linarith
  -- the remainder
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hq0 : (0 : ℝ) ≤ |xv| / (2 * lv) := by positivity
  set k : ℤ := ⌊|xv| / (2 * lv)⌋ with hk
  have hrv : r.toVal = some ((|xv| - 2 * lv * k : ℝ) : EReal) := by
    rw [hr, toVal_remExact, habs, hyv, Option.bind_some, Option.bind_some,
      Spec.rem_coe_coe _ _ h2lv.ne', toInt_round_down, ite_eq_left hq0]
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast Int.floor_nonneg.mpr hq0
  have hkle : (k : ℝ) ≤ |xv| / (2 * lv) := Int.floor_le _
  have hkgt : |xv| / (2 * lv) < k + 1 := Int.lt_floor_add_one _
  set rv := |xv| - 2 * lv * k with hrvdef
  have hrv0 : 0 ≤ rv := by
    have := (le_div_iff₀ h2lv).mp hkle; linarith
  have hrvlt : rv < 2 * lv := by
    have := (div_lt_iff₀ h2lv).mp hkgt; linarith
  -- the error of the reduction
  obtain ⟨d, hd, hdc⟩ := subCeiling_err hhv' hlv' 64 (by linarith)
  have hd0 : 0 ≤ d := by linarith [hdc.ge]
  obtain ⟨Ev, hEv, hEvc⟩ := mulCeiling_err habs hd 64 (mul_nonneg hx0 hd0)
  have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
  have hd1 : d ≤ 2 * (hv - lv) := by
    have := hdc.le
    nlinarith [mul_le_mul_of_nonneg_left h64 (by linarith : 0 ≤ hv - lv)]
  have hd16 : d ≤ 16 * u := by linarith
  have hEv1 : Ev ≤ 2 * (|xv| * d) := by
    have := hEvc.le
    nlinarith [mul_le_mul_of_nonneg_left h64 (mul_nonneg hx0 hd0)]
  have hEv0 : 0 ≤ Ev := le_trans (mul_nonneg hx0 hd0) hEvc.ge
  have hEvle : Ev ≤ 32 * uV := by
    have h1 : |xv| * d ≤ |xv| * (16 * u) := mul_le_mul_of_nonneg_left hd16 hx0
    have h2 : |xv| * u ≤ (2 : ℝ) ^ ex.toInt * u := mul_le_mul_of_nonneg_right hex' hu0
    nlinarith
  have hk2 : 2 * (k : ℝ) ≤ |xv| := by
    have := (le_div_iff₀ h2lv).mp hkle
    nlinarith [mul_le_mul_of_nonneg_left hlv1 hk0]
  have hkπ0 : 0 ≤ 2 * k * (Real.pi - lv) := mul_nonneg (by linarith) (by linarith)
  have hkπ : 2 * k * (Real.pi - lv) ≤ Ev :=
    calc 2 * k * (Real.pi - lv) ≤ |xv| * (Real.pi - lv) :=
          mul_le_mul_of_nonneg_right hk2 (by linarith)
      _ ≤ |xv| * (hv - lv) := mul_le_mul_of_nonneg_left (by linarith) hx0
      _ ≤ |xv| * d := mul_le_mul_of_nonneg_left hdc.ge hx0
      _ ≤ Ev := hEvc.ge
  -- the true reduction and `sin |x| = cos (r − π/2)`
  set rt := rv - 2 * k * (Real.pi - lv) with hrt
  have hsin : Real.sin |xv| = Real.cos (rt - Real.pi / 2) := by
    rw [Real.cos_sub_pi_div_two, show |xv| = rt + k * (2 * Real.pi) by rw [hrt, hrvdef]; ring,
      Real.sin_add_int_mul_two_pi]
  -- the centre `s = ⌈r' − lo/2⌉_V`
  have hhalf : (P.1 <<< AzInt.ofInt (-1)).toVal = some ((lv / 2 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hlv' (AzInt.ofInt (-1))
    rw [AzInt.toInt_ofInt, show (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 by norm_num, mul_one_div] at h
    exact h
  obtain ⟨sv, hsv, hsv1, hsv2⟩ := subCeiling_abs hrv hhalf (w + 12)
  rw [← huV] at hsv2
  have hlv4 : lv ≤ 4 := by linarith
  have hA : |rv - lv / 2| ≤ 8 := by rw [abs_le]; constructor <;> linarith
  have hsv3 : sv ≤ rv - lv / 2 + 16 * uV := by nlinarith [mul_le_mul_of_nonneg_right hA huV0]
  -- the slack `E₂`
  obtain ⟨a1, ha1, ha1c⟩ := addCeiling_err hEv hd 64 (by linarith)
  have h16 : (1 : ℝ) * (2 : ℝ) ^ ((4 : ℤ) - ((w + 12 : ℕ) : ℤ)) = 16 * uV := by
    rw [one_mul, zpow_sub₀ two_ne_zero, zpow_natCast, huV, one_div_pow, div_eq_mul_inv, one_div]
    norm_num
  have ht16 : (one <<< AzInt.ofInt (4 - ((w + 12 : ℕ) : Int))).toVal
      = some ((16 * uV : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt, h16]
  have ha10 : 0 ≤ a1 := le_trans (by linarith) ha1c.ge
  obtain ⟨E2v, hE2, hE2c⟩ := addCeiling_err ha1 ht16 64 (by linarith)
  have ha1le : a1 ≤ 2 * (Ev + d) := by
    have := ha1c.le
    nlinarith [mul_le_mul_of_nonneg_left h64 (by linarith : 0 ≤ Ev + d)]
  have hE2le : E2v ≤ 2 * (a1 + 16 * uV) := by
    have := hE2c.le
    nlinarith [mul_le_mul_of_nonneg_left h64 (by linarith : 0 ≤ a1 + 16 * uV)]
  have hE2ge : Ev + d + 16 * uV ≤ E2v := by linarith [ha1c.ge, hE2c.ge]
  have hE20 : 0 ≤ E2v := by linarith
  have hE2b : E2v ≤ 224 * uV := by linarith
  have hE2s : E2v ≤ 1 / 128 := by linarith
  -- the tail
  have hpiDiff : Real.pi - lv ≤ d := by linarith [hdc.ge]
  have hts : |(rt - Real.pi / 2) - sv| ≤ E2v := by
    rw [abs_le]; constructor <;> linarith
  have hm1 : |sv / 8| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hfin := cosTail_spec hsv hE2 hE20 hE2s hm1 hts
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hV64
  rw [← huV] at hfin
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := hfin
  refine ⟨lo, hi, hlo, hhi, by rw [hsin]; exact h1, by rw [hsin]; exact h2, h3.trans ?_⟩
  show _ ≤ sinEpsW (w + 12)
  unfold sinEpsW
  rw [← huV]
  linarith

/-- `sinEpsW V → 0` as `V → ∞`. -/
theorem tendsto_sinEpsW : Filter.Tendsto sinEpsW Filter.atTop (nhds 0) := by
  have h1 := tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hdiv : Filter.Tendsto (fun W : ℕ => W / 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun a ha => by omega⟩
  have h3 := h2.comp hdiv
  have h := ((h1.const_mul (216 * 112)).add (h3.const_mul (216 * 2))).add
    (h2.const_mul (216 * 184 + 216 * 80 + 3440))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun W => ?_
  simp only [Function.comp, sinEpsW, cosSeriesEps]
  ring

/-- `sinEps ex w → 0` as `w → ∞`. -/
theorem tendsto_sinEps (ex : AzInt) : Filter.Tendsto (sinEps ex) Filter.atTop (nhds 0) :=
  tendsto_sinEpsW.comp (Filter.tendsto_add_atTop_nat 12)

/-- The sign of `sin x` relative to `sin |x|`. -/
theorem sin_eq_sign_mul_sin_abs (xv : ℝ) :
    Real.sin xv = (if xv < 0 then -1 else 1) * Real.sin |xv| := by
  split_ifs with h
  · rw [abs_of_neg h, Real.sin_neg]; ring
  · rw [abs_of_nonneg (not_lt.mp h), one_mul]

/-- `sinApprox neg` as a pair of `Roundable`s bracketing `± sin |x|`. -/
theorem sinApprox_spec (neg : Bool) {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sinApprox neg x ex w).1 lv ∧ Rounds (sinApprox neg x ex w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * Real.sin |xv| ∧
      (if neg then -1 else 1) * Real.sin |xv| ≤ hv ∧ hv - lv ≤ sinEps ex w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := sinBracket_spec hx hex hw
  simp only [sinApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    have hnlo : (-(sinBracket x ex w).2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(sinBracket x ex w).1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- `sin x` is irrational for a nonzero finite float `x`. -/
theorem irrational_sin_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.sin xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [hq, Rat.cast_zero]
  rw [hq]
  exact irrational_sin_rat hq0

/-- The Ziv certificate for `sin x`, `x` a nonzero finite float of sign `¬ neg`. -/
theorem sinApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hneg : neg = true ↔ xv < 0) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (sinApprox neg x ex (w₀ * 2 ^ f)).1
      (sinApprox neg x ex (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hval : Real.sin xv = (if neg then -1 else 1) * Real.sin |xv| := by
    rw [sin_eq_sign_mul_sin_abs]
    cases neg with
    | false =>
      have : ¬ xv < 0 := fun h => by simpa using hneg.mpr h
      simp [this]
    | true => simp [hneg.mp rfl]
  refine exists_isSome_of_irrational_threshold p mode (sinApprox neg x ex)
    (v := (if neg then -1 else 1) * Real.sin |xv|) ?_ (sinEps ex) (tendsto_sinEps ex) 64
    (fun _ hw => sinApprox_spec neg hx hex hw) w₀ hw₀
  rw [← hval]
  exact irrational_sin_of_toVal hx hx0

/-- The tiny-argument path answers with the rounding of `sin x`. -/
theorem sinTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : sinTiny? s (finite s e q m hv) e q p mode = some r) :
    r = roundVal p mode (some ((Real.sin (finiteVal s e m) : ℝ) : EReal)) := by
  unfold sinTiny? at h
  dsimp only at h
  set w := max p q + zivGuardBits with hw
  have : NeZero (w + 8) := ⟨by omega⟩
  set xv := finiteVal s e m with hxv
  have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
  have hlt := (abs_finiteVal_bounds s e hv).2
  rw [← hxv] at hlt
  have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  set t := (2 : ℝ) ^ e.toInt with ht
  have ht0 : 0 < t := by positivity
  have habs : (finite s e q m hv).abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hnx : (-(finite s e q m hv).abs).toVal = some ((-a : ℝ) : EReal) := by
    rw [toVal_neg, habs, Option.map_some, EReal.coe_neg]
  have hd : (((finite s e q m hv).abs <<< e) <<< e).toVal = some ((a * t * t : ℝ) : EReal) :=
    toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal habs e) e
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hnx hd (w + 8)
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hnx)
  rw [fval_of_toVal_coe hnx] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hs1 := Real.sin_lt ha0
  have hs2 := Real.sin_gt_sub_cube ha0
  have hcube : a ^ 3 ≤ a * t * t := by
    have h1 : a * a ≤ t * t := mul_le_mul hlt.le hlt.le ha0.le ht0.le
    nlinarith
  have hsgn := finiteVal_sign_iff s e hv
  rw [← hxv] at hsgn
  cases s with
  | true =>
    simp only [↓reduceIte] at h
    split_ifs at h with hc
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
    have hpos : 0 < xv := hsgn.mp rfl
    have hax : a = xv := abs_of_pos hpos
    have hr := roundingPossible_eq' p (-mode) (v := -Real.sin a) hR1 hR2 (by linarith)
      (by linarith) (Or.inl fun hEq => absurd hEq (by linarith)) hr'
    rw [hr, ← hax]
    have hneg := roundVal_neg p mode (-Real.sin a)
    rw [neg_neg] at hneg
    exact hneg.symm
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h with hc
    have hneg : xv < 0 := by
      rcases lt_or_gt_of_ne hx0 with h' | h'
      · exact h'
      · exact absurd (hsgn.mpr h') (by simp)
    have hax : xv = -a := by rw [ha, abs_of_neg hneg, neg_neg]
    have hr := roundingPossible_eq' p mode (v := -Real.sin a) hR1 hR2 (by linarith)
      (by linarith) (Or.inl fun hEq => absurd hEq (by linarith)) h
    rw [hr, hax, Real.sin_neg]

/-- `!s` is the sign bit of a negative float. -/
theorem finiteVal_neg_iff (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    (!s) = true ↔ finiteVal s e m < 0 := by
  have h1 := finiteVal_sign_iff s e hv
  have h0 := finiteVal_ne_zero s e hv
  cases s
  · simp only [Bool.not_false, true_iff]
    rcases lt_or_gt_of_ne h0 with h | h
    · exact h
    · exact absurd (h1.mpr h) (by simp)
  · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_lt]
    exact (h1.mp rfl).le

/-- `sin x = ± sin |x|` with the sign bit of `x`. -/
theorem sin_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    Real.sin xv = (if neg then -1 else 1) * Real.sin |xv| := by
  rw [sin_eq_sign_mul_sin_abs]
  cases neg with
  | false =>
    have : ¬ xv < 0 := fun h => by simpa using hneg.mpr h
    simp [this]
  | true => simp [hneg.mp rfl]

end Azurite.AzFloat
