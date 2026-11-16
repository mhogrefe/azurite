/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asinh
import Azurite.AzFloat.AsinhRat
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: `asinh x` and `asinh q`

`Spec.asinh a = arsinh a` (`±∞` at `±∞`),
`asinhPrecRound_eq_liftVal : asinhPrecRound x p mode = liftVal Spec.asinh x p mode` and
`asinhRatPrecRound_eq : asinhRatPrecRound q p mode = roundVal p mode (Spec.asinh q)`, for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `asinh`: `±∞ ↦ ±∞`. -/
noncomputable def asinh (a : EReal) : Option EReal :=
  some (if a = ⊤ then ⊤ else if a = ⊥ then ⊥ else ((Real.arsinh a.toReal : ℝ) : EReal))

theorem asinh_coe (r : ℝ) : asinh (r : EReal) = some ((Real.arsinh r : ℝ) : EReal) := by
  unfold asinh
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem asinh_top : asinh ⊤ = some ⊤ := by
  unfold asinh
  rw [ite_eq_left rfl]

@[simp] theorem asinh_bot : asinh ⊥ = some ⊥ := by
  unfold asinh
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- **`asinh` is correctly rounded.** -/
theorem asinhPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asinhPrecRound x p mode = liftVal Spec.asinh x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [asinhPrecRound]
  | zero =>
    simp only [asinhPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.asinh_coe, Real.arsinh_zero, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [asinhPrecRound, toVal_finite, Option.bind_some, Spec.asinh_coe]
    rw [dite_eq_right (NeZero.ne p)]
    have hx0 := finiteVal_ne_zero s e hv
    split
    · next r hT =>
      exact sinTiny?_eq_of Real.arsinh_neg (fun _ ha => arsinh_lt_self ha)
        (fun _ ha => sub_cube_le_arsinh ha) hv p mode hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_asinh_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := asinhApprox_spec (toVal_finite s e q m hv)
          (finiteVal_neg_iff s e hv) (w := w) (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

/-- **`asinh q` is correctly rounded.** -/
theorem asinhRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asinhRatPrecRound q p mode
      = roundVal p mode (Spec.asinh (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold asinhRatPrecRound
  rw [Spec.asinh_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.arsinh_zero,
      EReal.coe_zero, roundVal_zero]
  · rw [dite_eq_right h0, dite_eq_right hp]
    split
    · next r hT =>
      exact sinTinyRat?_eq_of Real.arsinh_neg (fun _ ha => arsinh_lt_self ha)
        (fun _ ha => sub_cube_le_arsinh ha) q h0 hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_asinh_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          asinhRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q h0
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
