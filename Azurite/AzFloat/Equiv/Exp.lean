/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp

/-!
# Equivalence: the exponential function

* `Spec.exp`: the extended-real exponential (`exp ∞ = ∞`, `exp (−∞) = 0`).
* `expPrecRound_eq_liftVal : expPrecRound x p mode = liftVal Spec.exp x p mode`: `exp` is
  correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real exponential: `exp ∞ = ∞`, `exp (−∞) = 0`. -/
noncomputable def exp (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a = ⊥ then some 0 else some ((Real.exp a.toReal : ℝ) : EReal)

theorem exp_coe (r : ℝ) : exp (r : EReal) = some ((Real.exp r : ℝ) : EReal) := by
  unfold exp
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem exp_top : exp ⊤ = some ⊤ := by
  unfold exp
  rw [ite_eq_left rfl]

@[simp] theorem exp_bot : exp ⊥ = some 0 := by
  unfold exp
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-! ### The equivalence -/

/-- **`exp` is correctly rounded.** -/
theorem expPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    expPrecRound x p mode = liftVal Spec.exp x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [expPrecRound]
  | zero =>
    simp only [expPrecRound, toVal_zero, Option.bind_some]
    rw [ite_eq_right (NeZero.ne p), ← EReal.coe_zero, Spec.exp_coe, Real.exp_zero,
      setPrecRound_eq_roundVal toVal_one']
  | finite s e q m hv =>
    simp only [expPrecRound, toVal_finite, Option.bind_some, Spec.exp_coe]
    rw [dite_eq_right (NeZero.ne p)]
    exact zivLoopCertified_eq_threshold p mode _ (Real.exp (finiteVal s e m)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          expApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) s e hv
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
