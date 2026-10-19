/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln2

/-!
# Equivalence: `ln2PrecRound` is the correctly rounded `ln 2`

`ln2PrecRound p mode = liftVal₀ (ln 2) p mode` for every `p ≠ 0` and every mode.
-/

namespace Azurite.AzFloat

/-- **`ln 2` is correctly rounded.** -/
theorem ln2PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ln2PrecRound p mode = liftVal₀ (some ((Real.log 2 : ℝ) : EReal)) p mode := by
  unfold ln2PrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq p mode ln2Approx (Real.log 2) ?_ (p + zivGuardBits)
    (by unfold zivGuardBits; omega)
  intro w hw
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -, -⟩ := ln2Approx_spec w
  exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

/-- **`log₂ e` is correctly rounded.** -/
theorem log2EPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2EPrecRound p mode = liftVal₀ (some (((Real.log 2)⁻¹ : ℝ) : EReal)) p mode := by
  unfold log2EPrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq_threshold p mode log2EApprox (Real.log 2)⁻¹ (p + zivGuardBits)
    (by unfold zivGuardBits; omega)
  intro w hw
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
    log2EApprox_spec (w := w) (by unfold zivGuardBits at hw; omega)
  exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

/-- `log₂ e = 1/ln 2`. -/
theorem logb_two_exp_one : Real.logb 2 (Real.exp 1) = (Real.log 2)⁻¹ := by
  rw [Real.logb, Real.log_exp, one_div]

theorem log2EPrecRound_eq_liftVal₀' (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2EPrecRound p mode = liftVal₀ (some ((Real.logb 2 (Real.exp 1) : ℝ) : EReal)) p mode := by
  rw [logb_two_exp_one]; exact log2EPrecRound_eq_liftVal₀ p mode

end Azurite.AzFloat
