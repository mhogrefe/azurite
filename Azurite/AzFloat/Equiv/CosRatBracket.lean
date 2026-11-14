/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosRatBracket
import Azurite.AzFloat.Equiv.SinCosBracket
import Azurite.AzFloat.Equiv.PowRatBracket
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: the bracket of `cos q` for a rational `q`

`cosRatBracket_spec` (width `cosRatEps q w`), `tendsto_cosRatEps`, `cosRatApprox_spec`,
`cosRatApprox_isSome_exists` (the Ziv certificate from `irrational_cos_rat`).
-/

namespace Azurite.AzFloat

/-- The width of `cosRatBracket q w`. -/
noncomputable def cosRatEps (q : AzRat) (w : ℕ) : ℝ :=
  cosEps (ratExpBound q) w
    + 8 * (2 : ℝ) ^ (ratExpBound q).toInt * (1 / 2 : ℝ) ^ cosWork (ratExpBound q) w
    + 24 * (1 / 2 : ℝ) ^ cosWork (ratExpBound q) w

/-- **`cosRatBracket` encloses `cos q`** at Ziv level `w ≥ 64`, with width at most
`cosRatEps q w`. -/
theorem cosRatBracket_spec (q : AzRat) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (cosRatBracket q w).1.toVal = some (lo : EReal) ∧
      (cosRatBracket q w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.cos (AzRat.toRat q : ℝ) ∧ Real.cos (AzRat.toRat q : ℝ) ≤ hi ∧
      hi - lo ≤ cosRatEps q w := by
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  set eq := ratExpBound q with heq
  have hW64 : 64 ≤ cosWork eq w := by unfold cosWork; omega
  have hexu := two_zpow_mul_half_pow_cosWork eq w
  have hεle := cosEps_le_one eq hw
  simp only [cosRatBracket]
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
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := cosBracket_spec hc hcabs hw
  have hz : |Real.cos qv - Real.cos cv| ≤ Ev := (Real.abs_cos_sub_cos_le _ _).trans hcd
  have hB : IsEnclW (cosBracket (if q.sign then (ofAzRatRound q W .Floor).1
      else (ofAzRatRound q W .Ceiling).1) eq w) (Real.cos cv) (cosEps eq w) :=
    ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩
  have hC := hB.widen0 (M := 2) (isEncl0W_exact hEv hEv0) hz
    ((Real.abs_cos_le_one _).trans (by norm_num)) (by linarith) hεle (by norm_num) hW64
  obtain ⟨lo', hi', hlo', hhi', h1', h2', hwid'⟩ := hC
  rw [← hu] at hwid'
  refine ⟨lo', hi', hlo', hhi', h1', h2', hwid'.trans ?_⟩
  unfold cosRatEps
  rw [← heq, ← hWdef, ← hu]
  linarith

/-- `cosRatEps q w → 0` as `w → ∞`. -/
theorem tendsto_cosRatEps (q : AzRat) :
    Filter.Tendsto (cosRatEps q) Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (cosWork (ratExpBound q)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by unfold cosWork; omega⟩
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp hc
  have h := (tendsto_cosEps (ratExpBound q)).add
    (h2.const_mul (8 * (2 : ℝ) ^ (ratExpBound q).toInt + 24))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun w => ?_
  simp only [Function.comp, cosRatEps]
  ring

/-- `cosRatApprox` as a pair of `Roundable`s bracketing `cos q`. -/
theorem cosRatApprox_spec (q : AzRat) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (cosRatApprox q w).1 lv ∧ Rounds (cosRatApprox q w).2 hv ∧
      lv ≤ Real.cos (AzRat.toRat q : ℝ) ∧ Real.cos (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ cosRatEps q w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := cosRatBracket_spec q hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [cosRatApprox]
  exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩

/-- `cos q` is irrational for a nonzero `AzRat`. -/
theorem irrational_cos_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.cos (AzRat.toRat q : ℝ)) :=
  irrational_cos_rat fun h => coe_toRat_ne_zero_of_num_ne_zero q h0 (by rw [h, Rat.cast_zero])

/-- The Ziv certificate for `cos q`, `q` a nonzero rational. -/
theorem cosRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cosRatApprox q (w₀ * 2 ^ f)).1 (cosRatApprox q (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (cosRatApprox q) (irrational_cos_toRat q h0)
    (cosRatEps q) (tendsto_cosRatEps q) 64 (fun _ hw => cosRatApprox_spec q hw) w₀ hw₀

end Azurite.AzFloat
