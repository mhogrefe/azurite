/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan
import Azurite.AzFloat.Equiv.PiConstants
import Azurite.AzFloat.Equiv.Sin

/-!
# Equivalence: `atan`

`Spec.atan : EReal → Option EReal` (`±π/2` at `±∞`) and
`atanPrecRound_eq_liftVal : atanPrecRound x p mode = liftVal Spec.atan x p mode` for `p ≠ 0`:
`arctan x` is correctly rounded in every mode, with the exact comparison, without fuel.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real arctangent: `±π/2` at `±∞`. -/
noncomputable def atan (a : EReal) : Option EReal :=
  some (if a = ⊤ then ((Real.pi / 2 : ℝ) : EReal)
    else if a = ⊥ then ((-(Real.pi / 2) : ℝ) : EReal) else ((Real.arctan a.toReal : ℝ) : EReal))

theorem atan_coe (r : ℝ) : atan (r : EReal) = some ((Real.arctan r : ℝ) : EReal) := by
  unfold atan
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem atan_top : atan ⊤ = some ((Real.pi / 2 : ℝ) : EReal) := by
  unfold atan
  rw [ite_eq_left rfl]

@[simp] theorem atan_bot : atan ⊥ = some ((-(Real.pi / 2) : ℝ) : EReal) := by
  unfold atan
  rw [ite_eq_right (by simp), ite_eq_left rfl]

end Spec

/-- **`arctan x` is correctly rounded.** -/
theorem atanPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    atanPrecRound x p mode = liftVal Spec.atan x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s with
    | true =>
      simp only [atanPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte, Spec.atan_top]
      exact piDiv2PrecRound_eq_liftVal₀ p mode
    | false =>
      simp only [atanPrecRound, toVal_infinity, Option.bind_some, Bool.false_eq_true,
        ↓reduceIte, Spec.atan_bot]
      rw [roundVal_neg, piDiv2PrecRound_eq_liftVal₀ p (-mode)]
      rfl
  | zero =>
    simp only [atanPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.atan_coe, Real.arctan_zero, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [atanPrecRound, toVal_finite, Option.bind_some, Spec.atan_coe]
    rw [dite_eq_right (NeZero.ne p)]
    split
    · next r hT => exact atanTiny?_eq hv p mode hT
    have hx0 := finiteVal_ne_zero s e hv
    have hneg := finiteVal_neg_iff s e hv
    have hval := arctan_eq_of_neg_iff hneg
    exact zivLoopCertified_eq_threshold' p mode _ (Real.arctan (finiteVal s e m))
      (not_mem_floatSet_of_irrational p
        (irrational_arctan_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w _ => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := atanApprox_spec (!s) (toVal_finite s e q m hv)
          hx0 (abs_finiteVal_bounds s e hv).1 (abs_finiteVal_bounds s e hv).2 w
        rw [← hval] at hlo hhi
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
