/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Constants
import Azurite.AzFloat.Equiv.Pow2Bracket
import Azurite.AzFloat.GelfondSchneider

/-!
# Equivalence: the Gelfond–Schneider constant

`sqrt2Ln2Bracket_spec` (a strict enclosure of `√2 ln 2` of width at most `1`: the lower end is
strict since the float below `√2` is rational), `gelfondSchneiderBracket_spec` (a strict
enclosure of `2^√2`, from `expOfBracket_spec`), `gelfondSchneiderApprox_spec`, and
`gelfondSchneiderPrecRound_eq_or`: `gelfondSchneiderPrecRound p mode` is the correctly rounded
`2^√2` (`liftVal₀ (some (2^√2))`) unless the fuel runs out (`(nan, .eq)`).  A termination
certificate would need `Irrational (2^√2)` (the Gelfond–Schneider theorem), which is not
available.
-/

namespace Azurite.AzFloat

/-- `sqrt2Ln2Bracket w` encloses `√2 ln 2`, strictly from below, with width at most `1`. -/
theorem sqrt2Ln2Bracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (sqrt2Ln2Bracket w).1.toVal = some (lo : EReal) ∧
      (sqrt2Ln2Bracket w).2.toVal = some (hi : EReal) ∧
      lo < Real.sqrt 2 * Real.log 2 ∧ Real.sqrt 2 * Real.log 2 ≤ hi ∧ hi - lo ≤ 1 := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 / 10 ^ 18 := by rw [hδ]; exact half_pow_small hw
  have hs1 : (7 / 5 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hln1 := Real.log_two_gt_d9
  have hln2 := Real.log_two_lt_d9
  -- the floats around `√2`
  obtain ⟨a, ha, haF⟩ := sqrtFloor_err toVal_two (by norm_num) w
  obtain ⟨b, hb, hbC⟩ := sqrtCeiling_err toVal_two (by norm_num) w
  have ha0 := haF.nonneg
  have ha1 := haF.le
  have ha2 := haF.ge
  have hb1 := hbC.ge
  have hb2 := hbC.le
  rw [← hδ] at ha2 hb2
  have halt : a < Real.sqrt 2 := by
    refine lt_of_le_of_ne ha1 fun h => ?_
    obtain ⟨r, hr⟩ := exists_rat_of_toVal ha
    exact irrational_sqrt_two ⟨r, by rw [← h, hr]⟩
  -- the bracket of `ln 2`
  obtain ⟨lv, hv, hlv, hhv, hl, hh, hwid, -⟩ := ln2Bracket_spec w
  rw [← hδ] at hwid
  have hlv0 : 0 ≤ lv := by linarith
  have hhv0 : 0 ≤ hv := by linarith
  -- the products
  obtain ⟨lo, hlo, hloF⟩ := mulFloor_err ha hlv w (mul_nonneg ha0 hlv0)
  obtain ⟨hi, hhi, hhiC⟩ := mulCeiling_err hb hhv w (mul_nonneg (by linarith) hhv0)
  have hlo1 := hloF.le
  have hlo2 := hloF.ge
  have hhi1 := hhiC.ge
  have hhi2 := hhiC.le
  rw [← hδ] at hlo2 hhi2
  refine ⟨lo, hi, hlo, hhi, ?_, ?_, ?_⟩
  · calc lo ≤ a * lv := hlo1
      _ ≤ a * Real.log 2 := mul_le_mul_of_nonneg_left hl ha0
      _ < Real.sqrt 2 * Real.log 2 := mul_lt_mul_of_pos_right halt (by linarith)
  · calc Real.sqrt 2 * Real.log 2 ≤ b * hv := mul_le_mul hb1 hh (by linarith) (by linarith)
      _ ≤ hi := hhi1
  · -- numeric bounds on the ends
    have hsd : 2 * Real.sqrt 2 * δ ≤ 1 / 10 := by nlinarith
    have hb3 : b ≤ 8 / 5 := by linarith
    have ha3 : 13 / 10 ≤ a := by linarith
    have hhv2 : hv ≤ 7 / 10 := by linarith
    have hlv2 : 69 / 100 ≤ lv := by linarith
    have hbhv : b * hv ≤ 8 / 5 * (7 / 10) := mul_le_mul hb3 hhv2 hhv0 (by norm_num)
    have halv : 13 / 10 * (69 / 100) ≤ a * lv := mul_le_mul ha3 hlv2 (by norm_num) ha0
    have hbhvd : 2 * (b * hv) * δ ≤ 1 / 10 := by nlinarith
    have halvd : 2 * (a * lv) * δ ≤ 1 / 10 := by nlinarith
    linarith

/-- `gelfondSchneiderBracket w` encloses `2^√2`, strictly from below. -/
theorem gelfondSchneiderBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (gelfondSchneiderBracket w).1.toVal = some (lo : EReal) ∧
      (gelfondSchneiderBracket w).2.toVal = some (hi : EReal) ∧
      lo < (2 : ℝ) ^ Real.sqrt 2 ∧ (2 : ℝ) ^ Real.sqrt 2 ≤ hi := by
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := sqrt2Ln2Bracket_spec hw
  rw [two_rpow_eq_exp]
  exact expOfBracket_spec hlv hhv hlo hhi hwid hw

theorem gelfondSchneiderApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (gelfondSchneiderApprox w).1 lv ∧
      Rounds (gelfondSchneiderApprox w).2 hv ∧
      lv < (2 : ℝ) ^ Real.sqrt 2 ∧ (2 : ℝ) ^ Real.sqrt 2 ≤ hv := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := gelfondSchneiderBracket_spec hw
  refine ⟨lo, hi, ?_, ?_, h1, h2⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR

/-- **`2^√2` is correctly rounded unless the fuel runs out.** -/
theorem gelfondSchneiderPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gelfondSchneiderPrecRound p mode
        = liftVal₀ (some (((2 : ℝ) ^ Real.sqrt 2 : ℝ) : EReal)) p mode ∨
      gelfondSchneiderPrecRound p mode = (nan, .eq) := by
  unfold gelfondSchneiderPrecRound liftVal₀
  rw [ite_eq_right (NeZero.ne p)]
  rcases eq_or_ne (zivLoop gelfondSchneiderApprox p mode (gelfondSchneiderFuel p)
    (p + zivGuardBits)) (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_threshold p mode gelfondSchneiderApprox ((2 : ℝ) ^ Real.sqrt 2) 64
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi⟩ := gelfondSchneiderApprox_spec hw
        exact ⟨lv, hv, hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
      _ _ (by unfold zivGuardBits; omega) hz

end Azurite.AzFloat
