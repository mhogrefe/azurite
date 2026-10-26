/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpConstants
import Azurite.AzFloat.Equiv.Exp

/-!
# Equivalence: `e`, `ln 10`, `log₁₀ e`, `log₂ 10` and `log₁₀ 2` are correctly rounded

Each `…PrecRound p mode` equals `liftVal₀ (some v) p mode` for its exact value `v`, for every
`p ≠ 0` and every mode; the `logb` forms are also given.
-/

namespace Azurite.AzFloat

/-- **`e` is correctly rounded.** -/
theorem ePrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ePrecRound p mode = liftVal₀ (some ((Real.exp 1 : ℝ) : EReal)) p mode := by
  unfold ePrecRound liftVal₀
  rw [ite_eq_right (NeZero.ne p), expPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_one', Option.bind_some, Spec.exp_coe]

/-- **`ln 10` is correctly rounded.** -/
theorem ln10PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ln10PrecRound p mode = liftVal₀ (some ((Real.log 10 : ℝ) : EReal)) p mode := by
  unfold ln10PrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq_threshold p mode ln10Approx (Real.log 10) (p + zivGuardBits)
    (by unfold zivGuardBits; omega)
  intro w hw
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
    ln10Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
  exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

/-- **`log₁₀ e` is correctly rounded.** -/
theorem log10EPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log10EPrecRound p mode = liftVal₀ (some (((Real.log 10)⁻¹ : ℝ) : EReal)) p mode := by
  unfold log10EPrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq_threshold p mode log10EApprox (Real.log 10)⁻¹ (p + zivGuardBits)
    (by unfold zivGuardBits; omega)
  intro w hw
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
    log10EApprox_spec (w := w) (by unfold zivGuardBits at hw; omega)
  exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

/-- `log₁₀ e = 1/ln 10`. -/
theorem logb_ten_exp_one : Real.logb 10 (Real.exp 1) = (Real.log 10)⁻¹ := by
  rw [Real.logb, Real.log_exp, one_div]

theorem log10EPrecRound_eq_liftVal₀' (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log10EPrecRound p mode
      = liftVal₀ (some ((Real.logb 10 (Real.exp 1) : ℝ) : EReal)) p mode := by
  rw [logb_ten_exp_one]; exact log10EPrecRound_eq_liftVal₀ p mode

/-- **`log₂ 10` is correctly rounded.** -/
theorem log2TenPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2TenPrecRound p mode
      = liftVal₀ (some ((Real.log 10 / Real.log 2 : ℝ) : EReal)) p mode := by
  unfold log2TenPrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq_threshold p mode log2TenApprox (Real.log 10 / Real.log 2)
    (p + zivGuardBits) (by unfold zivGuardBits; omega)
  intro w hw
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
    log2TenApprox_spec (w := w) (by unfold zivGuardBits at hw; omega)
  exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

theorem log2TenPrecRound_eq_liftVal₀' (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2TenPrecRound p mode = liftVal₀ (some ((Real.logb 2 10 : ℝ) : EReal)) p mode := by
  rw [Real.logb]; exact log2TenPrecRound_eq_liftVal₀ p mode

/-- **`log₁₀ 2` is correctly rounded.** -/
theorem log10TwoPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log10TwoPrecRound p mode
      = liftVal₀ (some ((Real.log 2 / Real.log 10 : ℝ) : EReal)) p mode := by
  unfold log10TwoPrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq_threshold p mode log10TwoApprox (Real.log 2 / Real.log 10)
    (p + zivGuardBits) (by unfold zivGuardBits; omega)
  intro w hw
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
    log10TwoApprox_spec (w := w) (by unfold zivGuardBits at hw; omega)
  exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

theorem log10TwoPrecRound_eq_liftVal₀' (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log10TwoPrecRound p mode = liftVal₀ (some ((Real.logb 10 2 : ℝ) : EReal)) p mode := by
  rw [Real.logb]; exact log10TwoPrecRound_eq_liftVal₀ p mode

end Azurite.AzFloat
