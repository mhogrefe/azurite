/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ramanujan
import Azurite.AzFloat.Equiv.Gelfond
import Azurite.AzFloat.Equiv.SqrtPiBracket

/-!
# Equivalence: Ramanujan's constant

`piSqrt163Bracket_spec` (a strict enclosure of `π √163` of width at most `1`),
`ramanujanBracket_spec`, `ramanujanApprox_spec`, and `ramanujanPrecRound_eq_or`:
`ramanujanPrecRound p mode` is the correctly rounded `e^(π √163)` unless the fuel runs out.
-/

namespace Azurite.AzFloat

theorem toVal_ofAzNat_163 : (ofAzNat (AzNat.ofNat 163)).toVal = some ((163 : ℝ) : EReal) := by
  rw [toVal_ofAzNat, AzNat.toNat_ofNat, Nat.cast_ofNat]

/-- `√163 < 13`. -/
theorem sqrt_163_lt : Real.sqrt 163 < 13 := by
  have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 163) (by norm_num : (163 : ℝ) < 13 ^ 2)
  rwa [Real.sqrt_sq (by norm_num)] at this

/-- `piSqrt163Bracket w` encloses `π √163` strictly from below, with width at most `1`. -/
theorem piSqrt163Bracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (piSqrt163Bracket w).1.toVal = some (lo : EReal) ∧
      (piSqrt163Bracket w).2.toVal = some (hi : EReal) ∧
      lo < Real.pi * Real.sqrt 163 ∧ Real.pi * Real.sqrt 163 ≤ hi ∧ hi - lo ≤ 1 := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lv, hv, hlv, hhv, hlv0, hlo, hhi, hwid⟩ := piBracket_spec hw
  have hε := piEps_le hw
  obtain ⟨ls, hs, hls, hhs, hls1, hlo', hhi', hwid'⟩ :=
    sqrtBracket_spec (B := (ofAzNat (AzNat.ofNat 163), ofAzNat (AzNat.ofNat 163)))
      (lo := 163) (hi := 163) (M := (163 : ℝ)) toVal_ofAzNat_163 toVal_ofAzNat_163 (by norm_num)
      le_rfl le_rfl hw
  have h13 := sqrt_163_lt
  have hu : (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 64 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
  have hu' : (1 / 2 : ℝ) ^ 64 ≤ 1 / 10 ^ 19 := by norm_num
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  simp only [piSqrt163Bracket]
  obtain ⟨lo, hlo'', hf⟩ := mulFloor_err hlv hls w (by positivity)
  obtain ⟨hi, hhi'', hc⟩ := mulCeiling_err hhv hhs w (by nlinarith)
  refine ⟨lo, hi, hlo'', hhi'', ?_, ?_, ?_⟩
  · calc lo ≤ lv * ls := hf.le
      _ < Real.pi * ls := mul_lt_mul_of_pos_right hlo (by linarith)
      _ ≤ Real.pi * Real.sqrt 163 := mul_le_mul_of_nonneg_left hlo' Real.pi_pos.le
  · calc Real.pi * Real.sqrt 163 ≤ hv * hs :=
        mul_le_mul hhi hhi' (Real.sqrt_nonneg _) (by linarith)
      _ ≤ hi := hc.ge
  · -- `hi − lo ≤ hv hs (1 + 2u) − lv ls (1 − 2u)`, with `hv ≤ 3.1`, `hs ≤ 13.1`
    have hhs13 : hs ≤ 14 := by linarith
    have hhv4 : hv ≤ 4 := by linarith
    have hf2 := hf.ge
    have hc2 := hc.le
    have hA : hv * hs - lv * ls = hv * (hs - ls) + ls * (hv - lv) := by ring
    have hB : hv * (hs - ls) ≤ 4 * (1 / 2 + 4 * 163 * (1 / 2 : ℝ) ^ w) := by
      have : hv * (hs - ls) ≤ 4 * (hs - ls) := mul_le_mul_of_nonneg_right hhv4 (by linarith)
      nlinarith
    have hC : ls * (hv - lv) ≤ 13 * (1 / 16) := by
      have : ls ≤ 13 := by linarith
      nlinarith [hwid, hε]
    have hD : 2 * (hv * hs) * (1 / 2 : ℝ) ^ w ≤ 2 * 56 * (1 / 2 : ℝ) ^ w := by
      have : hv * hs ≤ 4 * 14 := mul_le_mul hhv4 hhs13 (by linarith) (by norm_num)
      nlinarith
    have hE : 2 * (lv * ls) * (1 / 2 : ℝ) ^ w ≤ 2 * 56 * (1 / 2 : ℝ) ^ w := by
      have : lv * ls ≤ 4 * 14 := mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      nlinarith
    nlinarith

/-- `ramanujanBracket w` encloses `e^(π √163)`, strictly from below. -/
theorem ramanujanBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (ramanujanBracket w).1.toVal = some (lo : EReal) ∧
      (ramanujanBracket w).2.toVal = some (hi : EReal) ∧
      lo < Real.exp (Real.pi * Real.sqrt 163) ∧ Real.exp (Real.pi * Real.sqrt 163) ≤ hi := by
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := piSqrt163Bracket_spec hw
  exact expOfBracket_spec hlv hhv hlo hhi hwid hw

theorem ramanujanApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (ramanujanApprox w).1 lv ∧ Rounds (ramanujanApprox w).2 hv ∧
      lv < Real.exp (Real.pi * Real.sqrt 163) ∧ Real.exp (Real.pi * Real.sqrt 163) ≤ hv := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := ramanujanBracket_spec hw
  refine ⟨lo, hi, ?_, ?_, h1, h2⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR

/-- **`e^(π √163)` is correctly rounded unless the fuel runs out.** -/
theorem ramanujanPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ramanujanPrecRound p mode
        = liftVal₀ (some ((Real.exp (Real.pi * Real.sqrt 163) : ℝ) : EReal)) p mode ∨
      ramanujanPrecRound p mode = (nan, .eq) := by
  unfold ramanujanPrecRound liftVal₀
  rw [ite_eq_right (NeZero.ne p)]
  rcases eq_or_ne (zivLoop ramanujanApprox p mode (ramanujanFuel p) (p + zivGuardBits))
    (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_threshold p mode ramanujanApprox
      (Real.exp (Real.pi * Real.sqrt 163)) 64
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi⟩ := ramanujanApprox_spec hw
        exact ⟨lv, hv, hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
      _ _ (by unfold zivGuardBits; omega) hz

end Azurite.AzFloat
