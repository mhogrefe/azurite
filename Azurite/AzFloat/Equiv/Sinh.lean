/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sinh

/-!
# Equivalence: `sinh x`

`Spec.sinh a = sinh a` (`±∞` at `±∞`) and
`sinhPrecRound_eq_liftVal : sinhPrecRound x p mode = liftVal Spec.sinh x p mode` for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `sinh`: `±∞ ↦ ±∞`. -/
noncomputable def sinh (a : EReal) : Option EReal :=
  some (if a = ⊤ then ⊤ else if a = ⊥ then ⊥ else ((Real.sinh a.toReal : ℝ) : EReal))

theorem sinh_coe (r : ℝ) : sinh (r : EReal) = some ((Real.sinh r : ℝ) : EReal) := by
  unfold sinh
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem sinh_top : sinh ⊤ = some ⊤ := by
  unfold sinh
  rw [ite_eq_left rfl]

@[simp] theorem sinh_bot : sinh ⊥ = some ⊥ := by
  unfold sinh
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- **`sinh` is correctly rounded.** -/
theorem sinhPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinhPrecRound x p mode = liftVal Spec.sinh x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [sinhPrecRound]
  | zero =>
    simp only [sinhPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.sinh_coe, Real.sinh_zero, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [sinhPrecRound, toVal_finite, Option.bind_some, Spec.sinh_coe]
    rw [dite_eq_right (NeZero.ne p)]
    split
    · next r hT =>
      exact tanTiny?_eq_of Real.sinh_neg sinh_tiny_bounds hv p mode hT
    have hx0 := finiteVal_ne_zero s e hv
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_sinh_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := sinhApprox_spec (toVal_finite s e q m hv) hx0
          (abs_finiteVal_bounds s e hv).2 (finiteVal_neg_iff s e hv) (w := w)
          (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
