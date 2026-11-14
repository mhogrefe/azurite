/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosWithPeriod
import Azurite.AzFloat.Equiv.SinWithPeriod
import Azurite.AzFloat.Equiv.CosWithPeriod

/-!
# Equivalence: `sin (2π x / u)` and `cos (2π x / u)` together

* `sinCosWithPeriodPrecRound_eq : sinCosWithPeriodPrecRound x u p mode =
  (sinWithPeriodPrecRound x u p mode, cosWithPeriodPrecRound x u p mode)` for every `p`.
* `sinCosWithPeriodPrecRound_eq_roundVal`: both values are correctly rounded (`p ≠ 0`).
* `sinCosWithPeriod_eq : sinCosWithPeriod x u = (sinWithPeriod x u, cosWithPeriod x u)`.
-/

namespace Azurite.AzFloat

/-- **The joint computation agrees with the separate ones.** -/
theorem sinCosWithPeriodPrecRound_eq (x : AzFloat) (u : UInt64) (p : ℕ) (mode : RoundingMode) :
    sinCosWithPeriodPrecRound x u p mode
      = (sinWithPeriodPrecRound x u p mode, cosWithPeriodPrecRound x u p mode) := by
  unfold sinCosWithPeriodPrecRound
  by_cases hu : u.toNat = 0
  · rw [dite_eq_left hu]
  rw [dite_eq_right hu]
  cases x with
  | nan => rfl
  | infinity s => rfl
  | zero => rfl
  | finite s e q m hv =>
    by_cases hp : p = 0
    · simp only [dite_eq_left hp]
    simp only [dite_eq_right hp]
    have : NeZero p := ⟨hp⟩
    have hun : AzNat.ofNat u.toNat ≠ 0 := fun h => hu (by
      rw [← AzNat.toNat_ofNat u.toNat, h, AzNat.toNat_zero])
    split
    · next hsT hcT =>
      split_ifs with h
      · obtain ⟨h1, h2, h3, h4, h6, h12⟩ := h
        obtain ⟨_, _, hr0, hr1⟩ := periodFrac_spec m (e - (AzNat.ofNat m.size).toAzInt) hun
        have hS : sinWithPeriodPrecRound (finite s e q m hv) u p mode
            = zivLoopCertified (sinPeriodApprox (!s)
                (periodFrac m (e - (AzNat.ofNat m.size).toAzInt) (AzNat.ofNat u.toNat))) p mode
              (p + zivGuardBits) (sinPeriodApprox_isSome_exists p mode (!s) _ hr0 hr1 h1 h2 h4
                h12 (p + zivGuardBits) (by unfold zivGuardBits; omega)) := by
          simp only [sinWithPeriodPrecRound, dite_eq_right hu, dite_eq_right hp, hsT,
            dite_eq_right h1, dite_eq_right h2, dite_eq_right h4, dite_eq_right h12]
        have hC : cosWithPeriodPrecRound (finite s e q m hv) u p mode
            = zivLoopCertified (cosPeriodApprox
                (periodFrac m (e - (AzNat.ofNat m.size).toAzInt) (AzNat.ofNat u.toNat))) p mode
              (p + zivGuardBits) (cosPeriodApprox_isSome_exists p mode _ hr0 hr1 h1 h2 h3 h4
                h6 (p + zivGuardBits) (by unfold zivGuardBits; omega)) := by
          simp only [cosWithPeriodPrecRound, dite_eq_right hu, dite_eq_right hp, hcT,
            dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, dite_eq_right h4,
            dite_eq_right h6]
        rw [hS, hC]
        exact zivLoopCertified₂_sinCosPeriodApprox p mode (!s) _ hr0 hr1 h1 h2 h3 h4 h6 h12
          (p + zivGuardBits) (by unfold zivGuardBits; omega) _ _ _
      · rfl
    · rfl

/-- **`sin (2π x / u)` and `cos (2π x / u)` are both correctly rounded.** -/
theorem sinCosWithPeriodPrecRound_eq_roundVal (x : AzFloat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    sinCosWithPeriodPrecRound x u p mode
      = (roundVal p mode (x.toVal.bind fun a => Spec.sinWithPeriod a u.toNat),
        roundVal p mode (x.toVal.bind fun a => Spec.cosWithPeriod a u.toNat)) := by
  rw [sinCosWithPeriodPrecRound_eq, sinWithPeriodPrecRound_eq, cosWithPeriodPrecRound_eq]

/-- `sinCosWithPeriod x u = (sinWithPeriod x u, cosWithPeriod x u)`. -/
theorem sinCosWithPeriod_eq (x : AzFloat) (u : UInt64) :
    sinCosWithPeriod x u = (sinWithPeriod x u, cosWithPeriod x u) := by
  unfold sinCosWithPeriod sinWithPeriod cosWithPeriod
  rw [sinCosWithPeriodPrecRound_eq]

end Azurite.AzFloat
