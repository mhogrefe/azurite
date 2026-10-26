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

`gelfondBracket_spec` (a strict enclosure of `e^π`, from `expOfBracket_spec`),
`gelfondApprox_spec`, and
`gelfondPrecRound_eq_or`: `gelfondPrecRound p mode` is the correctly rounded `e^π`
(`liftVal₀ (some (exp π))`) unless the fuel runs out (`(nan, .eq)`).  A termination certificate
would need `Irrational (exp π)` (Gelfond's theorem), which is not available.
-/

namespace Azurite.AzFloat

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
