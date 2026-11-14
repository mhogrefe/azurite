/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosRat
import Azurite.AzFloat.Equiv.SinRat
import Azurite.AzFloat.Equiv.CosRat

/-!
# Equivalence: `sin q` and `cos q` together for a rational `q`

* `sinCosRatPrecRound_eq : sinCosRatPrecRound q p mode = (sinRatPrecRound q p mode,
  cosRatPrecRound q p mode)` for every `p`.
* `sinCosRatPrecRound_eq_roundVal`: both values are correctly rounded (`p ≠ 0`).
* `sinCosRat_eq : sinCosRat q p = (sinRat q p, cosRat q p)`.
-/

namespace Azurite.AzFloat

/-- **The joint computation agrees with the separate ones.** -/
theorem sinCosRatPrecRound_eq (q : AzRat) (p : ℕ) (mode : RoundingMode) :
    sinCosRatPrecRound q p mode = (sinRatPrecRound q p mode, cosRatPrecRound q p mode) := by
  unfold sinCosRatPrecRound
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0]
  rw [dite_eq_right h0]
  by_cases hp : p = 0
  · rw [dite_eq_left hp]
  rw [dite_eq_right hp]
  have : NeZero p := ⟨hp⟩
  split
  · rw [sinRatPrecRound_eq, cosRatPrecRound_eq, Spec.sin_coe, Spec.cos_coe]
    refine zivLoopCertified₂_eq p mode _ (Real.sin (AzRat.toRat q : ℝ))
      (Real.cos (AzRat.toRat q : ℝ))
      (not_mem_floatSet_of_irrational p (irrational_sin_toRat q h0))
      (not_mem_floatSet_of_irrational p (irrational_cos_toRat q h0))
      _ (by unfold zivGuardBits; omega) (fun w hw => ?_) _
    have hw64 : 64 ≤ w := by unfold zivGuardBits at hw; omega
    obtain ⟨l₁, h₁, hl₁, hh₁, a₁, b₁, -⟩ := sinRatApprox_spec q h0 hw64
    obtain ⟨l₂, h₂, hl₂, hh₂, a₂, b₂, -⟩ := cosRatApprox_spec q hw64
    rw [← sinCosRatApprox_fst] at hl₁ hh₁
    rw [← sinCosRatApprox_snd] at hl₂ hh₂
    exact ⟨l₁, h₁, l₂, h₂, hl₁, hh₁, a₁, b₁, hl₂, hh₂, a₂, b₂⟩
  · rfl

/-- **`sin q` and `cos q` are both correctly rounded.** -/
theorem sinCosRatPrecRound_eq_roundVal (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinCosRatPrecRound q p mode
      = (roundVal p mode (Spec.sin (((AzRat.toRat q : ℚ) : ℝ) : EReal)),
        roundVal p mode (Spec.cos (((AzRat.toRat q : ℚ) : ℝ) : EReal))) := by
  rw [sinCosRatPrecRound_eq, sinRatPrecRound_eq, cosRatPrecRound_eq]

/-- `sinCosRat q p = (sinRat q p, cosRat q p)`. -/
theorem sinCosRat_eq (q : AzRat) (p : ℕ) : sinCosRat q p = (sinRat q p, cosRat q p) := by
  unfold sinCosRat sinRat cosRat
  rw [sinCosRatPrecRound_eq]

end Azurite.AzFloat
