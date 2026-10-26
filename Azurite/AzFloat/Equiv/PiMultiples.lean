/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PiMultiples
import Azurite.AzFloat.Equiv.Pi

/-!
# Equivalence: `τ`, `π/2`, `π/3`, `π/4`, `π/6`, `π/8` are correctly rounded

Each `…PrecRound p mode` equals `liftVal₀ (some v) p mode` for its exact value `v`, for every
`p ≠ 0` and every mode.  The shifted constants follow from `roundVal_mul_two_zpow`.
-/

namespace Azurite.AzFloat

/-- A correctly rounded constant shifted by `2^k` is the correctly rounded `v · 2^k`. -/
theorem shift_liftVal₀ {f : AzFloat × Ordering} {v : ℝ} (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hf : f = liftVal₀ (some (v : EReal)) p mode) (k : AzInt) :
    (f.1 <<< k, f.2) = liftVal₀ (some ((v * 2 ^ k.toInt : ℝ) : EReal)) p mode := by
  unfold liftVal₀ at hf ⊢
  rw [roundVal_mul_two_zpow, hf]

/-- **`τ = 2π` is correctly rounded.** -/
theorem tauPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    tauPrecRound p mode = liftVal₀ (some ((2 * Real.pi : ℝ) : EReal)) p mode := by
  have h := shift_liftVal₀ p mode (piPrecRound_eq_liftVal₀ p mode) (AzInt.ofInt 1)
  rw [AzInt.toInt_ofInt, zpow_one, mul_comm] at h
  exact h

/-- **`π/2` is correctly rounded.** -/
theorem piDiv2PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    piDiv2PrecRound p mode = liftVal₀ (some ((Real.pi / 2 : ℝ) : EReal)) p mode := by
  have h := shift_liftVal₀ p mode (piPrecRound_eq_liftVal₀ p mode) (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at h
  exact h

/-- **`π/4` is correctly rounded.** -/
theorem piDiv4PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    piDiv4PrecRound p mode = liftVal₀ (some ((Real.pi / 4 : ℝ) : EReal)) p mode := by
  have h := shift_liftVal₀ p mode (piPrecRound_eq_liftVal₀ p mode) (AzInt.ofInt (-2))
  rw [AzInt.toInt_ofInt, show ((2 : ℝ) ^ (-2 : ℤ)) = 1 / 4 by norm_num, mul_one_div] at h
  exact h

/-- **`π/8` is correctly rounded.** -/
theorem piDiv8PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    piDiv8PrecRound p mode = liftVal₀ (some ((Real.pi / 8 : ℝ) : EReal)) p mode := by
  have h := shift_liftVal₀ p mode (piPrecRound_eq_liftVal₀ p mode) (AzInt.ofInt (-3))
  rw [AzInt.toInt_ofInt, show ((2 : ℝ) ^ (-3 : ℤ)) = 1 / 8 by norm_num, mul_one_div] at h
  exact h

/-- **`π/3` is correctly rounded.** -/
theorem piDiv3PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    piDiv3PrecRound p mode = liftVal₀ (some ((Real.pi / 3 : ℝ) : EReal)) p mode := by
  unfold piDiv3PrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq_threshold p mode piDiv3Approx (Real.pi / 3) (p + zivGuardBits)
    (by unfold zivGuardBits; omega)
  intro w hw
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
    piDiv3Approx_spec (w := w) (by unfold zivGuardBits at hw; omega)
  exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

/-- **`π/6` is correctly rounded.** -/
theorem piDiv6PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    piDiv6PrecRound p mode = liftVal₀ (some ((Real.pi / 6 : ℝ) : EReal)) p mode := by
  have h := shift_liftVal₀ p mode (piDiv3PrecRound_eq_liftVal₀ p mode) (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv, div_div] at h
  norm_num at h
  exact h

end Azurite.AzFloat
