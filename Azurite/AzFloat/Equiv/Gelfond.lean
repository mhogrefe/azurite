/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gelfond
import Azurite.AzFloat.Equiv.ExpApprox
import Azurite.AzFloat.Equiv.PiBracket

/-!
# Equivalence: Gelfond's constant

`expOfBracket_spec` (the exponential of a bracket of width `≤ 1`), `gelfondBracket_spec` (a
strict enclosure of `e^π`), `gelfondApprox_spec`, and
`gelfondPrecRound_eq_or`: `gelfondPrecRound p mode` is the correctly rounded `e^π`
(`liftVal₀ (some (exp π))`) unless the fuel runs out (`(nan, .eq)`).  A termination certificate
would need `Irrational (exp π)` (Gelfond's theorem), which is not available.
-/

namespace Azurite.AzFloat

/-- `expOfBracket X w` encloses `exp v` for a bracket `X = [lo, hi]` of `v` with `hi − lo ≤ 1`,
strictly from below when `lo < v`. -/
theorem expOfBracket_spec {X : AzFloat × AzFloat} {lo hi v : ℝ}
    (hlo : X.1.toVal = some (lo : EReal)) (hhi : X.2.toVal = some (hi : EReal)) (h1 : lo < v)
    (h2 : v ≤ hi) (hw1 : hi - lo ≤ 1) {w : ℕ} (hw : 64 ≤ w) :
    ∃ a b : ℝ, (expOfBracket X w).1.toVal = some (a : EReal) ∧
      (expOfBracket X w).2.toVal = some (b : EReal) ∧ a < Real.exp v ∧ Real.exp v ≤ b := by
  have : NeZero (w + 8) := ⟨by omega⟩
  obtain ⟨a, b, ha, hb, ha1, hb1, -⟩ := expBracketAt_spec hlo hw
  simp only [expOfBracket]
  obtain ⟨dv, hd, hd1, -⟩ := subCeiling_abs hhi hlo (w + 8)
  have hd0 : 0 ≤ dv := by linarith
  have h2d : ((subPrecRound X.2 X.1 (w + 8) .Ceiling).1 <<< AzInt.ofInt 1).toVal
      = some ((2 * dv : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hd (AzInt.ofInt 1)
    rw [AzInt.toInt_ofInt, zpow_one, mul_comm] at h
    exact h
  have hb0 : 0 < b := lt_of_lt_of_le (Real.exp_pos lo) hb1
  obtain ⟨corr, hcorr, hc⟩ := mulCeiling_err hb h2d (w + 8) (by positivity)
  have hbd : 0 ≤ b * (2 * dv) := by positivity
  obtain ⟨hi', hhi', hh⟩ := addCeiling_err hb hcorr (w + 8) (by linarith [hc.ge])
  refine ⟨a, hi', ha, hhi', lt_of_le_of_lt ha1 (Real.exp_lt_exp.mpr h1), ?_⟩
  have e1 : Real.exp v ≤ Real.exp lo * (1 + 2 * (v - lo)) :=
    exp_le_exp_mul_one_add h1.le (by linarith)
  have e2 : Real.exp lo * (1 + 2 * (v - lo)) ≤ b * (1 + 2 * dv) :=
    mul_le_mul hb1 (by linarith) (by linarith) hb0.le
  have e3 := hc.ge
  have e4 := hh.ge
  nlinarith

/-- `gelfondBracket w` encloses `e^π`, strictly from below. -/
theorem gelfondBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (gelfondBracket w).1.toVal = some (lo : EReal) ∧
      (gelfondBracket w).2.toVal = some (hi : EReal) ∧
      lo < Real.exp Real.pi ∧ Real.exp Real.pi ≤ hi := by
  obtain ⟨lv, hv, hlv, hhv, -, hlo, hhi, hwid⟩ := piBracket_spec hw
  have hε := piEps_le hw
  exact expOfBracket_spec hlv hhv hlo hhi (by linarith) hw

theorem gelfondApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (gelfondApprox w).1 lv ∧ Rounds (gelfondApprox w).2 hv ∧
      lv < Real.exp Real.pi ∧ Real.exp Real.pi ≤ hv := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := gelfondBracket_spec hw
  refine ⟨lo, hi, ?_, ?_, h1, h2⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR

/-- **`e^π` is correctly rounded unless the fuel runs out.** -/
theorem gelfondPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gelfondPrecRound p mode = liftVal₀ (some ((Real.exp Real.pi : ℝ) : EReal)) p mode ∨
      gelfondPrecRound p mode = (nan, .eq) := by
  unfold gelfondPrecRound liftVal₀
  rw [ite_eq_right (NeZero.ne p)]
  rcases eq_or_ne (zivLoop gelfondApprox p mode (gelfondFuel p) (p + zivGuardBits)) (nan, .eq)
    with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_threshold p mode gelfondApprox (Real.exp Real.pi) 64
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi⟩ := gelfondApprox_spec hw
        exact ⟨lv, hv, hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
      _ _ (by unfold zivGuardBits; omega) hz

end Azurite.AzFloat
