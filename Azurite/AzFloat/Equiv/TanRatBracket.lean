/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanRatBracket
import Azurite.AzFloat.Equiv.SinCosRatBracket
import Azurite.AzFloat.Equiv.TanBracket

/-!
# Equivalence: the bracket of `tan q` for a rational `q`

`sinRatEps_le_one`, `irrational_tan_toRat`, `tan_toRat_eq`, `tanRatEps`/`tendsto_tanRatEps`,
`tanRatBracket_width`, `tanRatApprox_valid_or_none`, `tanRatApprox_isSome_exists` (the Ziv
certificate), `tanTinyCore?_eq`, `tanTinyRat?_eq`.
-/

namespace Azurite.AzFloat

/-- `sinRatEps q w ≤ 1` from `w = 64` on. -/
theorem sinRatEps_le_one (q : AzRat) {w : ℕ} (hw : 64 ≤ w) : sinRatEps q w ≤ 1 := by
  have h1 := sinEps_le_one (ratExpBound q) hw
  have h2 := two_zpow_mul_half_pow_cosWork (ratExpBound q) w
  have hW : 64 ≤ cosWork (ratExpBound q) w := by unfold cosWork; omega
  have h3 := half_pow_small hW
  have h4 := half_pow_small (by omega : 64 ≤ w + 12)
  have hV : 64 ≤ w + 12 := by omega
  have h := add_nine_mul_half_pow_le hV
  have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 12) := by positivity
  have : (73 : ℝ) * (1 / 2 : ℝ) ^ 64 ≤ 1 / 10 ^ 16 := by norm_num
  have h5 : sinEps (ratExpBound q) w ≤ 1 / 2 := by
    unfold sinEps sinCosEps sinCosEpsW
    linarith
  unfold sinRatEps
  linarith

/-- `tan q` is irrational for a nonzero `AzRat`. -/
theorem irrational_tan_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.tan (AzRat.toRat q : ℝ)) :=
  irrational_tan_rat fun h => coe_toRat_ne_zero_of_num_ne_zero q h0 (by rw [h, Rat.cast_zero])

/-- `tan q = ± tan |q|` with the sign of the rational. -/
theorem tan_toRat_eq (q : AzRat) (h0 : q.num ≠ 0) :
    Real.tan (AzRat.toRat q : ℝ)
      = (if (!q.sign) = true then -1 else 1) * Real.tan |(AzRat.toRat q : ℝ)| := by
  have hs := toRat_sign_iff q h0
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  refine tan_eq_of_neg_iff ?_
  cases hsg : q.sign
  · simp only [Bool.not_false, true_iff]
    rcases lt_or_gt_of_ne hq0 with h | h
    · exact h
    · rw [hs.mpr h] at hsg; cases hsg
  · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_lt]
    exact (hs.mp hsg).le

/-- The width of `tanRatBracket` once the bracket of `cos q` is at most half of `c = |cos q|`. -/
noncomputable def tanRatEps (c : ℝ) (q : AzRat) (w : ℕ) : ℝ :=
  (sinRatEps q w + 2 * cosRatEps q w / (c / 2) + 8 * (1 / 2 : ℝ) ^ (w + 12)) / (c / 2)

/-- `tanRatEps c q w → 0` as `w → ∞`. -/
theorem tendsto_tanRatEps (c : ℝ) (q : AzRat) :
    Filter.Tendsto (tanRatEps c q) Filter.atTop (nhds 0) := by
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp (Filter.tendsto_add_atTop_nat 12)
  have h := (((tendsto_sinRatEps q).add ((tendsto_cosRatEps q).const_mul (2 / (c / 2)))).add
    (h2.const_mul 8)).div_const (c / 2)
  simp only [mul_zero, add_zero, zero_div] at h
  refine h.congr fun w => ?_
  simp only [Function.comp, tanRatEps]
  ring

theorem isEnclW_sinCosRatBracket (q : AzRat) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (sinCosRatBracket q w).1 (Real.sin |(AzRat.toRat q : ℝ)|) (sinRatEps q w) ∧
      IsEnclW (sinCosRatBracket q w).2 (Real.cos (AzRat.toRat q : ℝ)) (cosRatEps q w) := by
  rw [sinCosRatBracket_fst, sinCosRatBracket_snd]
  exact ⟨sinRatBracket_spec q hw, cosRatBracket_spec q hw⟩

/-- **`tanRatBracket` encloses `tan |q|`** with width at most `tanRatEps |cos q| q w`, as soon
as `cosRatEps q w ≤ |cos q| / 2`. -/
theorem tanRatBracket_width (q : AzRat) {w : ℕ} (hw : 64 ≤ w)
    (hc0 : 0 < |Real.cos (AzRat.toRat q : ℝ)|)
    (hc : cosRatEps q w ≤ |Real.cos (AzRat.toRat q : ℝ)| / 2) :
    IsEnclW (tanRatBracket q w) (Real.tan |(AzRat.toRat q : ℝ)|)
      (tanRatEps |Real.cos (AzRat.toRat q : ℝ)| q w) := by
  obtain ⟨hS, hC⟩ := isEnclW_sinCosRatBracket q hw
  rw [tan_abs_eq_sin_div_cos]
  exact tanOfSinCos_width hS hC (Real.abs_sin_le_one _) (sinRatEps_le_one q hw) (by omega) hc0 hc

/-- At every level `w ≥ 64` the bracket of `tanRatApprox` encloses `tan q` or is rejected by
`roundingPossible`. -/
theorem tanRatApprox_valid_or_none (q : AzRat) (h0 : q.num ≠ 0) {w : ℕ} (hw : 64 ≤ w) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (tanRatApprox q w).1 lv ∧ Rounds (tanRatApprox q w).2 hv ∧
        lv ≤ Real.tan (AzRat.toRat q : ℝ) ∧ Real.tan (AzRat.toRat q : ℝ) ≤ hv) ∨
      roundingPossible (tanRatApprox q w).1 (tanRatApprox q w).2 p mode = none := by
  obtain ⟨hS, hC⟩ := isEnclW_sinCosRatBracket q hw
  rw [tan_toRat_eq q h0, tan_abs_eq_sin_div_cos]
  exact tanOfSinCos_valid_or_none (!q.sign) hS hC (Real.abs_sin_le_one _)
    (sinRatEps_le_one q hw) (by omega) p mode

/-- The Ziv certificate for `tan q`, `q` a nonzero rational. -/
theorem tanRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (tanRatApprox q (w₀ * 2 ^ f)).1 (tanRatApprox q (w₀ * 2 ^ f)).2 p
      mode).isSome = true := by
  have hc0 : 0 < |Real.cos (AzRat.toRat q : ℝ)| :=
    abs_pos.mpr (irrational_cos_toRat q h0).ne_zero
  obtain ⟨W₁, hW₁⟩ := ((tendsto_cosRatEps q).eventually
    (gt_mem_nhds (half_pos hc0))).exists_forall_of_atTop
  refine exists_isSome_of_irrational_threshold p mode (tanRatApprox q)
    (v := (if (!q.sign) = true then -1 else 1) * Real.tan |(AzRat.toRat q : ℝ)|) ?_
    (tanRatEps |Real.cos (AzRat.toRat q : ℝ)| q) (tendsto_tanRatEps _ q) (max 64 W₁)
    (fun w hw => negSwapApprox_of_isEnclW (!q.sign) (tanRatBracket_width q
      (le_of_max_le_left hw) hc0 (hW₁ w (le_of_max_le_right hw)).le)) w₀ hw₀
  rw [← tan_toRat_eq q h0]
  exact irrational_tan_toRat q h0

/-! ### Tiny arguments -/

/-- The tiny-argument test answers with the rounding of `± tan a`. -/
theorem tanTinyCore?_eq {pos : Bool} {ax : Roundable} {axHi : AzFloat} {e : AzInt} {w p : ℕ}
    [NeZero p] {mode : RoundingMode} {r : AzFloat × Ordering} {a h : ℝ} (hR : Rounds ax a)
    (hH : axHi.toVal = some (h : EReal)) (hh : a ≤ h) (ha0 : 0 < a)
    (hlt : a < (2 : ℝ) ^ e.toInt) (hT : tanTinyCore? pos ax axHi e w p mode = some r) :
    r = roundVal p mode (some (((if pos then 1 else -1) * Real.tan a : ℝ) : EReal)) := by
  unfold tanTinyCore? at hT
  dsimp only at hT
  have : NeZero (w + 8) := ⟨by omega⟩
  set t := (2 : ℝ) ^ e.toInt with ht
  have ht0 : 0 < t := by positivity
  have hd : (((one <<< e) <<< e) <<< e).toVal = some ((1 * t * t * t : ℝ) : EReal) :=
    toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal toVal_one' e) e) e
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hH hd (w + 8)
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  by_cases hc : e.sign = false ∧ w + 8 ≤ e.abs.toNat
  swap
  · rw [ite_eq_right hc] at hT
    exact absurd hT (by simp)
  rw [ite_eq_left hc] at hT
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [hc.1] at htoInt
  simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
  have ht1 : t ≤ 1 := by
    rw [ht, htoInt, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨hs1, hs2⟩ := tan_bounds_of_small ha0 (hlt.le.trans ht1)
  have hcube : a ^ 3 ≤ 1 * t * t * t := by
    have h1 : a * a ≤ t * t := mul_le_mul hlt.le hlt.le ha0.le ht0.le
    have h2 : a * a * a ≤ t * t * t := mul_le_mul h1 hlt.le ha0.le (by positivity)
    nlinarith
  cases pos with
  | true =>
    simp only [↓reduceIte] at hT
    have hr := roundingPossible_eq' p mode (v := Real.tan a) hR hR2 hs1.le (by linarith)
      (Or.inl fun hEq => absurd hEq hs1.ne) hT
    rw [hr]
    simp only [↓reduceIte, one_mul]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hT
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hT
    have hr := roundingPossible_eq' p (-mode) (v := Real.tan a) hR hR2 hs1.le (by linarith)
      (Or.inl fun hEq => absurd hEq hs1.ne) hr'
    rw [hr]
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    exact (roundVal_neg p mode (Real.tan a)).symm

/-- The tiny-argument path of `tan q` answers with the rounding of `tan q`. -/
theorem tanTinyRat?_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (hT : tanTinyRat? q p mode = some r) :
    r = roundVal p mode (some ((Real.tan (AzRat.toRat q : ℝ) : ℝ) : EReal)) := by
  unfold tanTinyRat? at hT
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  have hR : Rounds (fun P M => ofAzRatRound q.abs P M) |((AzRat.toRat q : ℚ) : ℝ)| := by
    intro P _ M
    show ofAzRatRound q.abs P M = _
    rw [ofAzRatRound_eq_roundVal, habs]
  obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs q.abs (p + zivGuardBits + 8)
  rw [habs] at hc1
  have hlt : |((AzRat.toRat q : ℚ) : ℝ)| < (2 : ℝ) ^ (ratExpBound q).toInt :=
    lt_of_lt_of_le (abs_toRat_lt_two_zpow q) (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have h := tanTinyCore?_eq hR hc hc1 (abs_pos.mpr hq0) hlt hT
  rw [h, tan_toRat_eq q h0]
  cases q.sign <;> simp

end Azurite.AzFloat
