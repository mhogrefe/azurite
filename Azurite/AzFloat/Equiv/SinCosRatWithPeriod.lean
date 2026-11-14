/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosRatWithPeriod
import Azurite.AzFloat.Equiv.SinRatWithPeriod
import Azurite.AzFloat.Equiv.CosRatWithPeriod

/-!
# Equivalence: `sin (2π q / u)` and `cos (2π q / u)` together for a rational `q`

* `sinCosRatWithPeriodPrecRound_eq : sinCosRatWithPeriodPrecRound q u p mode =
  (sinRatWithPeriodPrecRound q u p mode, cosRatWithPeriodPrecRound q u p mode)` for every `p`.
* `sinCosRatWithPeriodPrecRound_eq_roundVal`: both values are correctly rounded (`p ≠ 0`).
* `sinCosRatWithPeriod_eq`.
-/

namespace Azurite.AzFloat

/-- **The joint computation agrees with the separate ones.** -/
theorem sinCosRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) (mode : RoundingMode) :
    sinCosRatWithPeriodPrecRound q u p mode
      = (sinRatWithPeriodPrecRound q u p mode, cosRatWithPeriodPrecRound q u p mode) := by
  unfold sinCosRatWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu]
  rw [dite_eq_right hu]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0]
  rw [dite_eq_right h0]
  by_cases hp : p = 0
  · rw [dite_eq_left hp]
  rw [dite_eq_right hp]
  have : NeZero p := ⟨hp⟩
  have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
    rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
  split
  · next hsT hcT =>
    dsimp only
    split_ifs with h
    · obtain ⟨h1, h2, h3, h4, h6, h12⟩ := h
      obtain ⟨_, _, hr0, hr1⟩ := periodFracRat_spec q hun
      have hS : sinRatWithPeriodPrecRound q u p mode
          = zivLoopCertified (sinPeriodApprox (!q.sign) (periodFracRat q (AzNat.ofNat u.toNat)))
            p mode (p + zivGuardBits) (sinPeriodApprox_isSome_exists p mode (!q.sign) _ hr0 hr1
              h1 h2 h4 h12 (p + zivGuardBits) (by unfold zivGuardBits; omega)) := by
        simp only [sinRatWithPeriodPrecRound, dite_eq_right hu, dite_eq_right h0,
          dite_eq_right hp, hsT, dite_eq_right h1, dite_eq_right h2, dite_eq_right h4,
          dite_eq_right h12]
      have hC : cosRatWithPeriodPrecRound q u p mode
          = zivLoopCertified (cosPeriodApprox (periodFracRat q (AzNat.ofNat u.toNat)))
            p mode (p + zivGuardBits) (cosPeriodApprox_isSome_exists p mode _ hr0 hr1 h1 h2 h3
              h4 h6 (p + zivGuardBits) (by unfold zivGuardBits; omega)) := by
        simp only [cosRatWithPeriodPrecRound, dite_eq_right hu, dite_eq_right h0,
          dite_eq_right hp, hcT, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
          dite_eq_right h4, dite_eq_right h6]
      rw [hS, hC]
      exact zivLoopCertified₂_sinCosPeriodApprox p mode (!q.sign) _ hr0 hr1 h1 h2 h3 h4 h6 h12
        (p + zivGuardBits) (by unfold zivGuardBits; omega) _ _ _
    · rfl
  · rfl

/-- **`sin (2π q / u)` and `cos (2π q / u)` are both correctly rounded.** -/
theorem sinCosRatWithPeriodPrecRound_eq_roundVal (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    sinCosRatWithPeriodPrecRound q u p mode
      = (roundVal p mode (Spec.sinWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat),
        roundVal p mode (Spec.cosWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat)) := by
  rw [sinCosRatWithPeriodPrecRound_eq, sinRatWithPeriodPrecRound_eq,
    cosRatWithPeriodPrecRound_eq]

/-- `sinCosRatWithPeriod q u p = (sinRatWithPeriod q u p, cosRatWithPeriod q u p)`. -/
theorem sinCosRatWithPeriod_eq (q : AzRat) (u : UInt64) (p : ℕ) :
    sinCosRatWithPeriod q u p = (sinRatWithPeriod q u p, cosRatWithPeriod q u p) := by
  unfold sinCosRatWithPeriod sinRatWithPeriod cosRatWithPeriod
  rw [sinCosRatWithPeriodPrecRound_eq]

end Azurite.AzFloat
