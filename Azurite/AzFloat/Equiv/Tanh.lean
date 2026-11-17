/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Tanh
import Azurite.AzFloat.TanhRat
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: `tanh x` and `tanh q`

`Spec.tanh a = tanh a` (`±1` at `±∞`),
`tanhPrecRound_eq_liftVal : tanhPrecRound x p mode = liftVal Spec.tanh x p mode` and
`tanhRatPrecRound_eq : tanhRatPrecRound q p mode = roundVal p mode (Spec.tanh q)`, for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `tanh`: `±∞ ↦ ±1`. -/
noncomputable def tanh (a : EReal) : Option EReal :=
  some (if a = ⊤ then ((1 : ℝ) : EReal) else if a = ⊥ then ((-1 : ℝ) : EReal)
    else ((Real.tanh a.toReal : ℝ) : EReal))

theorem tanh_coe (r : ℝ) : tanh (r : EReal) = some ((Real.tanh r : ℝ) : EReal) := by
  unfold tanh
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem tanh_top : tanh ⊤ = some ((1 : ℝ) : EReal) := by
  unfold tanh
  rw [ite_eq_left rfl]

@[simp] theorem tanh_bot : tanh ⊥ = some ((-1 : ℝ) : EReal) := by
  unfold tanh
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- `x = sign · |x|`. -/
theorem sign_mul_abs_eq {s : Bool} {xv : ℝ} (hs : s = true ↔ 0 < xv) (hx0 : xv ≠ 0) :
    (if s then 1 else -1) * Real.tanh |xv| = Real.tanh xv := by
  cases s with
  | true =>
    simp only [↓reduceIte, one_mul]
    rw [abs_of_pos (hs.mp rfl)]
  | false =>
    have hlt : xv < 0 := by
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact h
      · exact absurd (hs.mpr h) (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [abs_of_neg hlt, Real.tanh_neg]
    ring

/-- **`tanh` is correctly rounded.** -/
theorem tanhPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    tanhPrecRound x p mode = liftVal Spec.tanh x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [tanhPrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.tanh_bot]
      rw [ite_eq_right (NeZero.ne p), setPrecRound_eq_roundVal toVal_neg_one_float]
    · simp only [tanhPrecRound, ↓reduceIte, toVal_infinity, Option.bind_some, Spec.tanh_top]
      rw [ite_eq_right (NeZero.ne p), setPrecRound_eq_roundVal toVal_one']
  | zero =>
    simp only [tanhPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.tanh_coe, Real.tanh_zero, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [tanhPrecRound, toVal_finite, Option.bind_some, Spec.tanh_coe]
    rw [dite_eq_right (NeZero.ne p)]
    have hx0 := finiteVal_ne_zero s e hv
    split
    · next r hT =>
      exact sinTiny?_eq_of Real.tanh_neg (fun _ ha => tanh_lt_self ha)
        (fun _ ha => sub_cube_le_tanh ha) hv p mode hT
    split
    · next r hT =>
      rw [tanhNearOne?_eq (tanhFloatN_le (toVal_finite s e q m hv)
          (abs_finiteVal_bounds s e hv).1) hT,
        sign_mul_abs_eq (finiteVal_sign_iff s e hv) hx0]
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_tanh_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := tanhApprox_spec (toVal_finite s e q m hv) hx0
          (abs_finiteVal_bounds s e hv).2 (finiteVal_neg_iff s e hv) (w := w)
          (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

/-- **`tanh q` is correctly rounded.** -/
theorem tanhRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    tanhRatPrecRound q p mode
      = roundVal p mode (Spec.tanh (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold tanhRatPrecRound
  rw [Spec.tanh_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.tanh_zero, EReal.coe_zero,
      roundVal_zero]
  · rw [dite_eq_right h0, dite_eq_right hp]
    have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
    split
    · next r hT =>
      exact sinTinyRat?_eq_of Real.tanh_neg (fun _ ha => tanh_lt_self ha)
        (fun _ ha => sub_cube_le_tanh ha) q h0 hT
    split
    · next r hT =>
      rw [tanhNearOne?_eq (tanhRatN_le q) hT, sign_mul_abs_eq (toRat_sign_iff q h0) hq0]
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_tanh_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          tanhRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q h0
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
