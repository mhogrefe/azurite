/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cos
import Azurite.AzFloat.Equiv.Exp

/-!
# Equivalence: `cos`

`Spec.cos : EReal → Option EReal` (undefined at `±∞`) and
`cosPrecRound_eq_liftVal : cosPrecRound x p mode = liftVal Spec.cos x p mode` for `p ≠ 0`:
`cos x` is correctly rounded in every mode, with the exact comparison, without fuel.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real cosine: undefined (`NaN`) at `±∞`. -/
noncomputable def cos (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some ((Real.cos a.toReal : ℝ) : EReal)

theorem cos_coe (r : ℝ) : cos (r : EReal) = some ((Real.cos r : ℝ) : EReal) := by
  unfold cos
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem cos_top : cos ⊤ = none := by
  unfold cos
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem cos_bot : cos ⊥ = none := by
  unfold cos
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`cos x` is correctly rounded.** -/
theorem cosPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cosPrecRound x p mode = liftVal Spec.cos x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    simp only [cosPrecRound, toVal_infinity, Option.bind_some]
    cases s <;> simp
  | zero =>
    simp only [cosPrecRound, toVal_zero, Option.bind_some]
    rw [ite_eq_right (NeZero.ne p), ← EReal.coe_zero, Spec.cos_coe, Real.cos_zero,
      setPrecRound_eq_roundVal toVal_one']
  | finite s e q m hv =>
    simp only [cosPrecRound, toVal_finite, Option.bind_some, Spec.cos_coe]
    rw [dite_eq_right (NeZero.ne p)]
    split
    · next r hT =>
      exact cosTiny?_eq (abs_finiteVal_bounds s e hv).2
        (irrational_cos_of_toVal (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)) hT
    exact zivLoopCertified_eq_threshold' p mode _ (Real.cos (finiteVal s e m))
      (not_mem_floatSet_of_irrational p
        (irrational_cos_of_toVal (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := cosApprox_spec (toVal_finite s e q m hv)
          (abs_finiteVal_bounds s e hv).2 (w := w) (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
