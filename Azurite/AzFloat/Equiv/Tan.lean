/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Tan
import Azurite.AzFloat.Equiv.Exp

/-!
# Equivalence: `tan`

`Spec.tan : EReal → Option EReal` (undefined at `±∞`) and
`tanPrecRound_eq_liftVal : tanPrecRound x p mode = liftVal Spec.tan x p mode` for `p ≠ 0`:
`tan x` is correctly rounded in every mode, with the exact comparison, without fuel.  (A finite
float is never a pole, so the value of `Real.tan` at the poles plays no role.)
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real tangent: undefined (`NaN`) at `±∞`. -/
noncomputable def tan (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some ((Real.tan a.toReal : ℝ) : EReal)

theorem tan_coe (r : ℝ) : tan (r : EReal) = some ((Real.tan r : ℝ) : EReal) := by
  unfold tan
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem tan_top : tan ⊤ = none := by
  unfold tan
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem tan_bot : tan ⊥ = none := by
  unfold tan
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`tan x` is correctly rounded.** -/
theorem tanPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    tanPrecRound x p mode = liftVal Spec.tan x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    simp only [tanPrecRound, toVal_infinity, Option.bind_some]
    cases s <;> simp
  | zero =>
    simp only [tanPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.tan_coe, Real.tan_zero, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [tanPrecRound, toVal_finite, Option.bind_some, Spec.tan_coe]
    rw [dite_eq_right (NeZero.ne p)]
    split
    · next r hT => exact tanTiny?_eq hv p mode hT
    have hx0 := finiteVal_ne_zero s e hv
    have hneg := finiteVal_neg_iff s e hv
    have hval := tan_eq_of_neg_iff hneg
    refine zivLoopCertified_eq_or_none p mode _ (Real.tan (finiteVal s e m))
      (not_mem_floatSet_of_irrational p
        (irrational_tan_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega) (fun w hw => ?_) _
    rw [hval]
    exact tanApprox_valid_or_none (!s) (toVal_finite s e q m hv)
      (abs_finiteVal_bounds s e hv).2 (by unfold zivGuardBits at hw; omega) p mode

end Azurite.AzFloat
