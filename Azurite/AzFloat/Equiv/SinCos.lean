/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCos
import Azurite.AzFloat.Equiv.Sin
import Azurite.AzFloat.Equiv.Cos

/-!
# Equivalence: `sin` and `cos` together

* `sinCosPrecRound_eq_liftVal : sinCosPrecRound x p mode = (liftVal Spec.sin x p mode,
  liftVal Spec.cos x p mode)` for `p ≠ 0`: both values are correctly rounded in every mode, with
  the exact comparisons, without fuel.
* `sinCosPrecRound_eq : sinCosPrecRound x p mode = (sinPrecRound x p mode, cosPrecRound x p
  mode)` for every `p`; `sinCos_eq : sinCos x = (sin x, cos x)`.
-/

namespace Azurite.AzFloat

/-- **The joint computation agrees with the separate ones.** -/
theorem sinCosPrecRound_eq (x : AzFloat) (p : ℕ) (mode : RoundingMode) :
    sinCosPrecRound x p mode = (sinPrecRound x p mode, cosPrecRound x p mode) := by
  cases x with
  | nan => rfl
  | infinity s => rfl
  | zero => rfl
  | finite s e q m hv =>
    by_cases hp : p = 0
    · subst hp
      simp [sinCosPrecRound, sinPrecRound, cosPrecRound]
    have : NeZero p := ⟨hp⟩
    simp only [sinCosPrecRound]
    rw [dite_eq_right hp]
    split
    · next hsT hcT =>
      have hx0 := finiteVal_ne_zero s e hv
      have hneg := finiteVal_neg_iff s e hv
      have hval := sin_eq_of_neg_iff hneg
      have hx := toVal_finite s e q m hv
      rw [sinPrecRound_eq_liftVal, cosPrecRound_eq_liftVal]
      unfold liftVal
      simp only [toVal_finite, Option.bind_some, Spec.sin_coe, Spec.cos_coe]
      refine zivLoopCertified₂_eq p mode _ (Real.sin (finiteVal s e m))
        (Real.cos (finiteVal s e m))
        (not_mem_floatSet_of_irrational p (irrational_sin_of_toVal hx hx0))
        (not_mem_floatSet_of_irrational p (irrational_cos_of_toVal hx hx0))
        _ (by unfold zivGuardBits; omega) (fun w hw => ?_) _
      have hw64 : 64 ≤ w := by unfold zivGuardBits at hw; omega
      obtain ⟨l₁, h₁, hl₁, hh₁, a₁, b₁, -⟩ := sinCosApprox_spec_sin (!s) hx
        (abs_finiteVal_bounds s e hv).2 hw64
      obtain ⟨l₂, h₂, hl₂, hh₂, a₂, b₂, -⟩ := sinCosApprox_spec_cos (!s) hx
        (abs_finiteVal_bounds s e hv).2 hw64
      rw [← hval] at a₁ b₁
      exact ⟨l₁, h₁, l₂, h₂, hl₁, hh₁, a₁, b₁, hl₂, hh₂, a₂, b₂⟩
    · rfl

/-- **`sin x` and `cos x` are both correctly rounded.** -/
theorem sinCosPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinCosPrecRound x p mode = (liftVal Spec.sin x p mode, liftVal Spec.cos x p mode) := by
  rw [sinCosPrecRound_eq, sinPrecRound_eq_liftVal, cosPrecRound_eq_liftVal]

/-- `sinCos x = (sin x, cos x)`. -/
theorem sinCos_eq (x : AzFloat) : sinCos x = (sin x, cos x) := by
  unfold sinCos sin cos
  rw [sinCosPrecRound_eq]

end Azurite.AzFloat
