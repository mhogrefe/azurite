/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinRatBracket
import Azurite.AzFloat.Equiv.SinBracket
import Azurite.AzFloat.Equiv.PowRatBracket
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: the bracket of `sin q` for a rational `q`

`sinEps_le_one`, `sinRatBracket_spec` (width `sinRatEps q w`), `tendsto_sinRatEps`,
`sinRatApprox_spec`, `irrational_sin_toRat`, `sinRatApprox_isSome_exists`; `sinTinyCore?_eq`,
`toRat_negAbsRat`, `sinTinyRat?_eq`.
-/

namespace Azurite.AzFloat

/-- `sinEps ex w ≤ 1` from `w = 64` on. -/
theorem sinEps_le_one (ex : AzInt) {w : ℕ} (hw : 64 ≤ w) : sinEps ex w ≤ 1 := by
  have hV : 64 ≤ w + 12 := by omega
  have h1 := cosSeriesEps_le hV
  have h3 := half_pow_small hV
  unfold sinEps sinEpsW
  linarith

/-- The width of `sinRatBracket q w`. -/
noncomputable def sinRatEps (q : AzRat) (w : ℕ) : ℝ :=
  sinEps (ratExpBound q) w
    + 8 * (2 : ℝ) ^ (ratExpBound q).toInt * (1 / 2 : ℝ) ^ cosWork (ratExpBound q) w
    + 24 * (1 / 2 : ℝ) ^ cosWork (ratExpBound q) w

/-- **`sinRatBracket` encloses `sin |q|`** at Ziv level `w ≥ 64`, with width at most
`sinRatEps q w`. -/
theorem sinRatBracket_spec (q : AzRat) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (sinRatBracket q w).1.toVal = some (lo : EReal) ∧
      (sinRatBracket q w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.sin |(AzRat.toRat q : ℝ)| ∧ Real.sin |(AzRat.toRat q : ℝ)| ≤ hi ∧
      hi - lo ≤ sinRatEps q w := by
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  set eq := ratExpBound q with heq
  have hW64 : 64 ≤ cosWork eq w := by unfold cosWork; omega
  have hexu := two_zpow_mul_half_pow_cosWork eq w
  have hεle := sinEps_le_one eq hw
  simp only [sinRatBracket]
  set W := cosWork eq w with hWdef
  have : NeZero W := ⟨by omega⟩
  have : NeZero (64 : ℕ) := ⟨by norm_num⟩
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hW64
  have h12 : (1 / 2 : ℝ) ^ (w + 12) ≤ 1 / 4096 := by
    calc (1 / 2 : ℝ) ^ (w + 12) ≤ (1 / 2 : ℝ) ^ 12 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4096 := by norm_num
  have hq := abs_toRat_lt_two_zpow q
  rw [← hqv, ← heq] at hq
  have h2e : (2 : ℝ) ^ eq.toInt = 2 * (2 : ℝ) ^ (eq.toInt - 1) := by
    rw [zpow_sub_one₀ (two_ne_zero)]
    field_simp
  have h2e0 : (0 : ℝ) < (2 : ℝ) ^ (eq.toInt - 1) := by positivity
  -- the floats around `q`
  obtain ⟨xl, hxl, hxl1, hxl2⟩ := ofAzRatRound_floor_abs q W
  obtain ⟨xh, hxh, hxh1, hxh2⟩ := ofAzRatRound_ceiling_abs q W
  rw [← hqv] at hxl1 hxh1
  rw [← hqv, ← hu] at hxl2 hxh2
  have hqu : |qv| * u ≤ (2 : ℝ) ^ (eq.toInt - 1) * u := mul_le_mul_of_nonneg_right hq.le hu0
  have hqabs := abs_nonneg qv
  have hxlabs : |xl| < (2 : ℝ) ^ eq.toInt := by
    rw [abs_lt] at hq ⊢
    rw [h2e]
    constructor <;> nlinarith [abs_le.mp (le_refl |qv|), neg_abs_le qv, le_abs_self qv]
  have hxhabs : |xh| < (2 : ℝ) ^ eq.toInt := by
    rw [abs_lt] at hq ⊢
    rw [h2e]
    constructor <;> nlinarith [abs_le.mp (le_refl |qv|), neg_abs_le qv, le_abs_self qv]
  -- the error float
  obtain ⟨Ev, hEv, hEvc⟩ := subCeiling_err hxh hxl 64 (by linarith)
  have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
  have hEv1 : Ev ≤ 2 * (xh - xl) := by
    have := hEvc.le
    nlinarith [mul_le_mul_of_nonneg_left h64 (by linarith : 0 ≤ xh - xl)]
  have hEv0 : 0 ≤ Ev := le_trans (by linarith) hEvc.ge
  have hEvle : Ev ≤ 8 * (2 : ℝ) ^ (eq.toInt - 1) * u := by linarith
  have hE2 : 8 * (2 : ℝ) ^ (eq.toInt - 1) * u = 4 * ((2 : ℝ) ^ eq.toInt * u) := by rw [h2e]; ring
  have hEvs : Ev ≤ 1 / 1024 := by linarith
  -- the centre
  have hcenter : ∃ cv : ℝ, (if q.sign then (ofAzRatRound q W .Floor).1
      else (ofAzRatRound q W .Ceiling).1).toVal = some (cv : EReal) ∧
      |cv| < (2 : ℝ) ^ eq.toInt ∧ |qv - cv| ≤ Ev := by
    cases q.sign
    · refine ⟨xh, hxh, hxhabs, ?_⟩
      rw [abs_of_nonpos (by linarith)]
      linarith [hEvc.ge]
    · refine ⟨xl, hxl, hxlabs, ?_⟩
      rw [abs_of_nonneg (by linarith)]
      linarith [hEvc.ge]
  obtain ⟨cv, hc, hcabs, hcd⟩ := hcenter
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := sinBracket_spec hc hcabs hw
  have hz : |Real.sin (|qv|) - Real.sin (|cv|)| ≤ Ev :=
    (Real.abs_sin_sub_sin_le _ _).trans ((abs_abs_sub_abs_le_abs_sub qv cv).trans hcd)
  have hB : IsEnclW (sinBracket (if q.sign then (ofAzRatRound q W .Floor).1
      else (ofAzRatRound q W .Ceiling).1) eq w) (Real.sin |cv|) (sinEps eq w) :=
    ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩
  have hC := hB.widen0 (M := 2) (isEncl0W_exact hEv hEv0) hz
    ((Real.abs_sin_le_one _).trans (by norm_num)) (by linarith) hεle (by norm_num) hW64
  obtain ⟨lo', hi', hlo', hhi', h1', h2', hwid'⟩ := hC
  rw [← hu] at hwid'
  refine ⟨lo', hi', hlo', hhi', h1', h2', hwid'.trans ?_⟩
  unfold sinRatEps
  rw [← heq, ← hWdef, ← hu]
  linarith

/-- `sinRatEps q w → 0` as `w → ∞`. -/
theorem tendsto_sinRatEps (q : AzRat) :
    Filter.Tendsto (sinRatEps q) Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (cosWork (ratExpBound q)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by unfold cosWork; omega⟩
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp hc
  have h := (tendsto_sinEps (ratExpBound q)).add
    (h2.const_mul (8 * (2 : ℝ) ^ (ratExpBound q).toInt + 24))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun w => ?_
  simp only [Function.comp, sinRatEps]
  ring

/-- `sin q = ± sin |q|` with the sign of the rational. -/
theorem sin_toRat_eq (q : AzRat) (h0 : q.num ≠ 0) :
    Real.sin (AzRat.toRat q : ℝ)
      = (if q.sign then 1 else -1) * Real.sin |(AzRat.toRat q : ℝ)| := by
  have hs := toRat_sign_iff q h0
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  cases hsg : q.sign
  · have hneg : (AzRat.toRat q : ℝ) < 0 := by
      rcases lt_or_gt_of_ne hq0 with h | h
      · exact h
      · rw [hs.mpr h] at hsg; cases hsg
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [abs_of_neg hneg, Real.sin_neg]; ring
  · simp only [↓reduceIte]
    rw [abs_of_pos (hs.mp hsg), one_mul]

/-- `sinRatApprox` as a pair of `Roundable`s bracketing `sin q`. -/
theorem sinRatApprox_spec (q : AzRat) (h0 : q.num ≠ 0) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sinRatApprox q w).1 lv ∧ Rounds (sinRatApprox q w).2 hv ∧
      lv ≤ Real.sin (AzRat.toRat q : ℝ) ∧ Real.sin (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ sinRatEps q w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := sinRatBracket_spec q hw
  rw [sin_toRat_eq q h0]
  simp only [sinRatApprox]
  cases q.sign with
  | true =>
    simp only [↓reduceIte, one_mul]
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    have hnlo : (-(sinRatBracket q w).2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(sinRatBracket q w).1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- `sin q` is irrational for a nonzero `AzRat`. -/
theorem irrational_sin_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.sin (AzRat.toRat q : ℝ)) :=
  irrational_sin_rat fun h => coe_toRat_ne_zero_of_num_ne_zero q h0 (by rw [h, Rat.cast_zero])

/-- The Ziv certificate for `sin q`, `q` a nonzero rational. -/
theorem sinRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (sinRatApprox q (w₀ * 2 ^ f)).1 (sinRatApprox q (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (sinRatApprox q) (irrational_sin_toRat q h0)
    (sinRatEps q) (tendsto_sinRatEps q) 64 (fun _ hw => sinRatApprox_spec q h0 hw) w₀ hw₀

/-! ### Tiny arguments -/

/-- The tiny-argument test answers with the rounding of `± sin a`. -/
theorem sinTinyCore?_eq {neg : Bool} {nx : Roundable} {nxHi : AzFloat} {e : AzInt} {w p : ℕ}
    [NeZero p] {mode : RoundingMode} {r : AzFloat × Ordering} {a h : ℝ} (hR : Rounds nx (-a))
    (hH : nxHi.toVal = some (h : EReal)) (hh : -a ≤ h) (ha0 : 0 < a)
    (hlt : a < (2 : ℝ) ^ e.toInt) (hT : sinTinyCore? neg nx nxHi e w p mode = some r) :
    r = roundVal p mode (some (((if neg then -1 else 1) * Real.sin a : ℝ) : EReal)) := by
  unfold sinTinyCore? at hT
  dsimp only at hT
  have : NeZero (w + 8) := ⟨by omega⟩
  set t := (2 : ℝ) ^ e.toInt with ht
  have ht0 : 0 < t := by positivity
  have hd : (((one <<< e) <<< e) <<< e).toVal = some ((1 * t * t * t : ℝ) : EReal) :=
    toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal toVal_one' e) e) e
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hH hd (w + 8)
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hs1 := Real.sin_lt ha0
  have hs2 := Real.sin_gt_sub_cube ha0
  have hcube : a ^ 3 ≤ 1 * t * t * t := by
    have h1 : a * a ≤ t * t := mul_le_mul hlt.le hlt.le ha0.le ht0.le
    have h2 : a * a * a ≤ t * t * t := mul_le_mul h1 hlt.le ha0.le (by positivity)
    nlinarith
  cases neg with
  | true =>
    simp only [↓reduceIte] at hT
    split_ifs at hT with hc
    have hr := roundingPossible_eq' p mode (v := -Real.sin a) hR hR2 (by linarith)
      (by linarith) (Or.inl fun hEq => absurd hEq (by linarith)) hT
    rw [hr]
    simp only [↓reduceIte, neg_one_mul]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hT
    split_ifs at hT with hc
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hT
    have hr := roundingPossible_eq' p (-mode) (v := -Real.sin a) hR hR2 (by linarith)
      (by linarith) (Or.inl fun hEq => absurd hEq (by linarith)) hr'
    rw [hr]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hneg := roundVal_neg p mode (-Real.sin a)
    rw [neg_neg] at hneg
    exact hneg.symm

/-- `negAbsRat q = −|q|`. -/
theorem toRat_negAbsRat (q : AzRat) (h0 : q.num ≠ 0) :
    ((AzRat.toRat (negAbsRat q) : ℚ) : ℝ) = -|((AzRat.toRat q : ℚ) : ℝ)| := by
  have hs := toRat_sign_iff q h0
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  unfold negAbsRat
  cases hsg : q.sign
  · have hneg : (AzRat.toRat q : ℝ) < 0 := by
      rcases lt_or_gt_of_ne hq0 with h | h
      · exact h
      · rw [hs.mpr h] at hsg; cases hsg
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [abs_of_neg hneg, neg_neg]
  · simp only [↓reduceIte]
    rw [AzRat.toRat_neg, abs_of_pos (hs.mp hsg)]
    push_cast
    rfl

/-- The tiny-argument path of `sin q` answers with the rounding of `sin q`. -/
theorem sinTinyRat?_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (hT : sinTinyRat? q p mode = some r) :
    r = roundVal p mode (some ((Real.sin (AzRat.toRat q : ℝ) : ℝ) : EReal)) := by
  unfold sinTinyRat? at hT
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have hneg := toRat_negAbsRat q h0
  have hR : Rounds (fun P M => ofAzRatRound (negAbsRat q) P M)
      (-|((AzRat.toRat q : ℚ) : ℝ)|) := by
    intro P _ M
    show ofAzRatRound (negAbsRat q) P M = _
    rw [ofAzRatRound_eq_roundVal, hneg]
  obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs (negAbsRat q) (p + zivGuardBits + 8)
  rw [hneg] at hc1
  have hlt : |((AzRat.toRat q : ℚ) : ℝ)| < (2 : ℝ) ^ (ratExpBound q).toInt :=
    lt_of_lt_of_le (abs_toRat_lt_two_zpow q) (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have h := sinTinyCore?_eq hR hc hc1 (abs_pos.mpr hq0) hlt hT
  rw [h, sin_toRat_eq q h0]
  cases q.sign <;> simp

end Azurite.AzFloat
