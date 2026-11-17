/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGammaRat
import Azurite.AzFloat.Equiv.LnGamma
import Azurite.AzFloat.Equiv.AcoshBracket

/-!
# Equivalence: `ln Γ` of a rational

`lnGammaRatEncl_spec` (the two directed roundings enclose a positive rational, with a positive
lower end), `lnGammaRatBracket_spec`, and `lnGammaRatPrecRound_eq_or`:
`lnGammaRatPrecRound q p mode` is the correctly rounded `Spec.lnGamma q` unless the fuel runs
out (`(nan, .eq)`).
-/

namespace Azurite.AzFloat

/-- The directed roundings of a positive rational enclose it, with a positive lower end. -/
theorem lnGammaRatEncl_spec (q : AzRat) (hq : 0 < ((AzRat.toRat q : ℚ) : ℝ)) (w : ℕ) :
    IsEnclPos (lnGammaRatEncl q w) ((AzRat.toRat q : ℚ) : ℝ) := by
  have : NeZero (w + 32) := ⟨by omega⟩
  obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs q (w + 32)
  obtain ⟨h, hh, hh1, -⟩ := ofAzRatRound_ceiling_abs q (w + 32)
  refine ⟨l, h, hl, hh, ?_, hl1, hh1⟩
  have hpow : (1 / 2 : ℝ) ^ (w + 32) ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ (w + 32) ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  rw [abs_of_pos hq] at hl2
  nlinarith

/-- **`lnGammaRatBracket q w` encloses `ln Γ(q)`** for a rational `q > 0` (`w ≥ 64`). -/
theorem lnGammaRatBracket_spec (q : AzRat) (hq : 0 < ((AzRat.toRat q : ℚ) : ℝ)) {w : ℕ}
    (hw : 64 ≤ w) :
    IsEncl (lnGammaRatBracket q w) (Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ))) :=
  lnGammaBracketEncl_spec (lnGammaRatEncl_spec q hq w) _ hw

/-- **`ln Γ` of a rational is correctly rounded unless the fuel runs out.** -/
theorem lnGammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnGammaRatPrecRound q p mode
        = roundVal p mode (Spec.lnGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      lnGammaRatPrecRound q p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold lnGammaRatPrecRound
  by_cases h0 : q.num = 0
  · left
    rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, EReal.coe_zero,
      Spec.lnGamma_zero, roundVal_top]
  rw [ite_eq_right h0]
  by_cases hs : q.sign = false
  · left
    have hneg : ((AzRat.toRat q : ℚ) : ℝ) < 0 := by
      have hne : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
      refine lt_of_le_of_ne (not_lt.mp fun hpos => ?_) hne
      rw [(toRat_sign_iff q h0).mpr hpos] at hs
      exact Bool.noConfusion hs
    rw [ite_eq_left hs, Spec.lnGamma_coe_of_neg hneg, roundVal_none]
  rw [ite_eq_right hs]
  have hpos : 0 < ((AzRat.toRat q : ℚ) : ℝ) :=
    (toRat_sign_iff q h0).mp (by simpa using hs)
  rw [Spec.lnGamma_coe_of_pos hpos]
  by_cases h12 : (q - 1).num = 0 ∨ (q - 1 - 1).num = 0
  · left
    rw [ite_eq_left h12]
    have hval : ((AzRat.toRat q : ℚ) : ℝ) = 1 ∨ ((AzRat.toRat q : ℚ) : ℝ) = 2 := by
      rcases h12 with h | h
      · left
        have := (AzRat.toRat_eq_zero_iff (q - 1)).mpr h
        rw [AzRat.toRat_sub, AzRat.toRat_one] at this
        push_cast at this
        linarith
      · right
        have := (AzRat.toRat_eq_zero_iff (q - 1 - 1)).mpr h
        rw [AzRat.toRat_sub, AzRat.toRat_sub, AzRat.toRat_one] at this
        push_cast at this
        linarith
    have hz : Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)) = 0 := by
      rcases hval with h | h <;> rw [h]
      · rw [Real.Gamma_one, Real.log_one]
      · rw [Real.Gamma_two, Real.log_one]
    rw [hz, EReal.coe_zero, roundVal_zero]
  rw [ite_eq_right h12, ite_eq_right hp]
  rcases eq_or_ne (zivLoop (lnGammaRatApprox q) p mode lnGammaFuel
    (max 64 (p + 32 + lnGammaRatCancelBits q))) (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_threshold p mode _ _ 64
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi⟩ :=
          lnGammaApproxOf_spec (lnGammaRatBracket_spec q hpos hw) w
        exact ⟨lv, hv', hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
      _ _ (le_max_left _ _) hz

end Azurite.AzFloat
