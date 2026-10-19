/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Lemniscate
import Azurite.AzFloat.Equiv.GaussConstant
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.BrentZimmermann.Chapter4.Lemniscate

/-!
# Equivalence: the lemniscate constant

`lemniscateConstantPrecRound p mode` is `liftVal₀ ϖ p mode` or the `NaN` fallback
(`lemniscateConstantPrecRound_eq_or`), with `ϖ = 2∫₀¹ dt/√(1 − t⁴)` (`BZ.lemniscate`): the
product of the brackets of `π` and `G` brackets `π · G = ϖ` (`lemniscate_eq_pi_mul_gauss`),
strictly from below.
-/

namespace Azurite.AzFloat

open Azurite.BZ

/-- The bracket encloses `ϖ`, with the lower end strictly below it. -/
theorem lemniscateApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (lemniscateApprox w).1 lv ∧ Rounds (lemniscateApprox w).2 hv ∧
      lv ≤ BZ.lemniscate ∧ BZ.lemniscate ≤ hv ∧ (lv = BZ.lemniscate → hv = BZ.lemniscate) := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lπ, hπ, hlπ, hhπ, hlπ0, hlπlt, hπle, -⟩ := piBracket_spec hw
  obtain ⟨lG, hG, hlG, hhG, hlG0, hlGlt, hGle⟩ := gaussBracket_spec w
  obtain ⟨lo, hlo, hlole⟩ := mulFloor_spec hlπ hlG w
  obtain ⟨hi, hhi, hhige⟩ := mulCeiling_spec hhπ hhG w
  have hGpos : 0 < (AGM 1 (Real.sqrt 2))⁻¹ := by linarith
  have hpi := Real.pi_pos
  have hlt : lo < BZ.lemniscate := by
    rw [lemniscate_eq_pi_mul_gauss]
    have h1 : lπ * lG ≤ Real.pi * lG := mul_le_mul_of_nonneg_right hlπlt.le hlG0
    have h2 : Real.pi * lG < Real.pi * (AGM 1 (Real.sqrt 2))⁻¹ :=
      mul_lt_mul_of_pos_left hlGlt hpi
    linarith
  have hge : BZ.lemniscate ≤ hi := by
    rw [lemniscate_eq_pi_mul_gauss]
    exact (mul_le_mul hπle hGle hGpos.le (by linarith)).trans hhige
  refine ⟨lo, hi, ?_, ?_, hlt.le, hge, fun h => absurd h hlt.ne⟩
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rwa [fval_of_toVal_coe hlo] at this
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rwa [fval_of_toVal_coe hhi] at this

/-- **The lemniscate constant is correctly rounded, unless the fuel runs out.** -/
theorem lemniscateConstantPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lemniscateConstantPrecRound p mode = liftVal₀ (some ((BZ.lemniscate : ℝ) : EReal)) p mode ∨
      lemniscateConstantPrecRound p mode = (nan, .eq) := by
  unfold lemniscateConstantPrecRound liftVal₀
  rcases eq_or_ne (zivLoop lemniscateApprox p mode (agmFuel p) (p + zivGuardBits)) (nan, .eq)
    with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_threshold p mode _ _ 64 (fun w hw => lemniscateApprox_spec hw) _ _
      (by unfold zivGuardBits; omega) hz

end Azurite.AzFloat
