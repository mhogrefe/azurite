/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Csch
import Azurite.AzFloat.CschRat
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: `csch x` and `csch q`

`Spec.csch a = 1 / sinh a` (`0` at `±∞`, `+∞` at `0`),
`cschPrecRound_eq_liftVal : cschPrecRound x p mode = liftVal Spec.csch x p mode` and
`cschRatPrecRound_eq : cschRatPrecRound q p mode = roundVal p mode (Spec.csch q)`, for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `csch`: `±∞ ↦ 0`, `0 ↦ +∞` (there is one zero only). -/
noncomputable def csch (a : EReal) : Option EReal :=
  some (if a = ⊤ ∨ a = ⊥ then ((0 : ℝ) : EReal) else if a.toReal = 0 then ⊤
    else (((Real.sinh a.toReal)⁻¹ : ℝ) : EReal))

theorem csch_coe {r : ℝ} (hr : r ≠ 0) :
    csch (r : EReal) = some (((Real.sinh r)⁻¹ : ℝ) : EReal) := by
  unfold csch
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_right hr]

theorem csch_zero : csch ((0 : ℝ) : EReal) = some ⊤ := by
  unfold csch
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top 0, EReal.coe_ne_bot 0⟩), EReal.toReal_coe,
    ite_eq_left rfl]

@[simp] theorem csch_top : csch ⊤ = some ((0 : ℝ) : EReal) := by
  unfold csch
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem csch_bot : csch ⊥ = some ((0 : ℝ) : EReal) := by
  unfold csch
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`csch` is correctly rounded.** -/
theorem cschPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cschPrecRound x p mode = liftVal Spec.csch x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [cschPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.csch_top, Spec.csch_bot] <;>
      rw [EReal.coe_zero, roundVal_zero]
  | zero =>
    simp only [cschPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.csch_zero, roundVal_top]
  | finite s e q m hv =>
    have hx0 := finiteVal_ne_zero s e hv
    simp only [cschPrecRound, toVal_finite, Option.bind_some]
    rw [Spec.csch_coe hx0, dite_eq_right (NeZero.ne p)]
    split
    · next r hT => exact cschTiny?_eq hv p mode hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_csch_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := cschApprox_spec (toVal_finite s e q m hv) hx0
          (abs_finiteVal_bounds s e hv).2 (finiteVal_neg_iff s e hv) (w := w)
          (by unfold zivGuardBits at hw; omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

/-- **`csch q` is correctly rounded.** -/
theorem cschRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cschRatPrecRound q p mode
      = roundVal p mode (Spec.csch (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold cschRatPrecRound
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.csch_zero, roundVal_top]
  · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
    rw [dite_eq_right h0, dite_eq_right hp, Spec.csch_coe hq0]
    split
    · next r hT => exact cschTinyRat?_eq q h0 hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_csch_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          cschRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q h0
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
