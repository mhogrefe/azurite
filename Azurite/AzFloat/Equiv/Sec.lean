/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sec
import Azurite.AzFloat.Equiv.Exp

/-!
# Equivalence: `sec`

`Spec.sec : EReal → Option EReal` (`1 / cos`, undefined at `±∞`) and
`secPrecRound_eq_liftVal : secPrecRound x p mode = liftVal Spec.sec x p mode` for `p ≠ 0`:
`sec x` is correctly rounded in every mode, with the exact comparison, without fuel.  (A finite
float is never a pole, so the value of `1 / cos` at the poles plays no role.)
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real secant: undefined (`NaN`) at `±∞`. -/
noncomputable def sec (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some ((1 / Real.cos a.toReal : ℝ) : EReal)

theorem sec_coe (r : ℝ) : sec (r : EReal) = some ((1 / Real.cos r : ℝ) : EReal) := by
  unfold sec
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem sec_top : sec ⊤ = none := by
  unfold sec
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem sec_bot : sec ⊥ = none := by
  unfold sec
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`sec x` is correctly rounded.** -/
theorem secPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    secPrecRound x p mode = liftVal Spec.sec x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    simp only [secPrecRound, toVal_infinity, Option.bind_some]
    cases s <;> simp
  | zero =>
    simp only [secPrecRound, toVal_zero, Option.bind_some]
    rw [ite_eq_right (NeZero.ne p), ← EReal.coe_zero, Spec.sec_coe, Real.cos_zero, div_one,
      setPrecRound_eq_roundVal toVal_one']
  | finite s e q m hv =>
    simp only [secPrecRound, toVal_finite, Option.bind_some, Spec.sec_coe]
    rw [dite_eq_right (NeZero.ne p)]
    have hx := toVal_finite s e q m hv
    have hx0 := finiteVal_ne_zero s e hv
    split
    · next r hT =>
      exact secTiny?_eq (abs_finiteVal_bounds s e hv).2 (irrational_sec_of_toVal hx hx0) hT
    exact zivLoopCertified_eq_or_none p mode _ (1 / Real.cos (finiteVal s e m))
      (not_mem_floatSet_of_irrational p (irrational_sec_of_toVal hx hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => secApprox_valid_or_none hx (abs_finiteVal_bounds s e hv).2
        (by unfold zivGuardBits at hw; omega) p mode) _

end Azurite.AzFloat
