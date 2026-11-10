/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sin
import Azurite.AzFloat.Equiv.Exp

/-!
# Equivalence: `sin`

`Spec.sin : EReal → Option EReal` (undefined at `±∞`) and
`sinPrecRound_eq_liftVal : sinPrecRound x p mode = liftVal Spec.sin x p mode` for `p ≠ 0`:
`sin x` is correctly rounded in every mode, with the exact comparison, without fuel.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real sine: undefined (`NaN`) at `±∞`. -/
noncomputable def sin (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some ((Real.sin a.toReal : ℝ) : EReal)

theorem sin_coe (r : ℝ) : sin (r : EReal) = some ((Real.sin r : ℝ) : EReal) := by
  unfold sin
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem sin_top : sin ⊤ = none := by
  unfold sin
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem sin_bot : sin ⊥ = none := by
  unfold sin
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`sin x` is correctly rounded.** -/
theorem sinPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinPrecRound x p mode = liftVal Spec.sin x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    simp only [sinPrecRound, toVal_infinity, Option.bind_some]
    cases s <;> simp
  | zero =>
    simp only [sinPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.sin_coe, Real.sin_zero, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [sinPrecRound, toVal_finite, Option.bind_some, Spec.sin_coe]
    rw [dite_eq_right (NeZero.ne p)]
    split
    · next r hT => exact sinTiny?_eq hv p mode hT
    have hx0 := finiteVal_ne_zero s e hv
    have hneg := finiteVal_neg_iff s e hv
    have hval := sin_eq_of_neg_iff hneg
    exact zivLoopCertified_eq_threshold' p mode _ (Real.sin (finiteVal s e m))
      (not_mem_floatSet_of_irrational p
        (irrational_sin_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := sinApprox_spec (!s) (toVal_finite s e q m hv)
          (abs_finiteVal_bounds s e hv).2 (w := w) (by unfold zivGuardBits at hw; omega)
        rw [← hval] at hlo hhi
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
