/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gelfond
import Azurite.AzFloat.Equiv.ExpApprox
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.AzFloat.Equiv.GelfondBracket

/-!
# Equivalence: Gelfond's constant

`gelfondBracket_spec` (a strict enclosure of `e^π`, from `expOfBracket_spec`),
`gelfondApprox_spec`, and
**`gelfondPrecRound_eq_liftVal₀`**: `gelfondPrecRound p mode` is the correctly rounded `e^π`
(`liftVal₀ (some (exp π))`), unconditionally: `e^π` is irrational by Gelfond's theorem
(`Transcendental/GelfondSchneider.lean`) and the Ziv loop has a termination certificate
(`Equiv/GelfondBracket.lean`).
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

/-- **`e^π` is correctly rounded**: the value is irrational (Gelfond's theorem,
`Azurite.irrational_exp_pi`), and the Ziv loop has a termination certificate. -/
theorem gelfondPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gelfondPrecRound p mode = liftVal₀ (some ((Real.exp Real.pi : ℝ) : EReal)) p mode := by
  unfold gelfondPrecRound liftVal₀
  rw [dite_eq_right (NeZero.ne p)]
  exact zivLoopBacked_eq p mode gelfondApprox
    (not_mem_floatSet_of_irrational p irrational_exp_pi) 64
    (fun w hw => Or.inl (by
      obtain ⟨lv, hv, hl, hh, hlo, hhi⟩ := gelfondApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi⟩))
    _ _ (by unfold zivGuardBits; omega) (by unfold zivGuardBits; omega) _

/-- `e^π` is correctly rounded (the weaker form, kept for its users). -/
theorem gelfondPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gelfondPrecRound p mode = liftVal₀ (some ((Real.exp Real.pi : ℝ) : EReal)) p mode ∨
      gelfondPrecRound p mode = (nan, .eq) :=
  Or.inl (gelfondPrecRound_eq_liftVal₀ p mode)

end Azurite.AzFloat
