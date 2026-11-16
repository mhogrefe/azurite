/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acsch
import Azurite.AzFloat.AcschRat
import Azurite.AzFloat.Equiv.Asinh
import Azurite.AzFloat.Equiv.AsecRat
import Azurite.AzFloat.Equiv.AcosWithPeriod

/-!
# Equivalence: `acsch x` and `acsch q`

`Spec.acsch a = arsinh (1/a)` for a finite `a ≠ 0` (`+∞` at `0`, `0` at `±∞`),
`acschPrecRound_eq_liftVal : acschPrecRound x p mode = liftVal Spec.acsch x p mode` and
`acschRatPrecRound_eq : acschRatPrecRound q p mode = roundVal p mode (Spec.acsch q)`, for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `acsch`: `arsinh (1/a)` for a finite `a ≠ 0`, `+∞` at `0` (there is one zero
only), `0` at `±∞`. -/
noncomputable def acsch (a : EReal) : Option EReal :=
  some (if a = ⊤ ∨ a = ⊥ then ((0 : ℝ) : EReal) else if a.toReal = 0 then ⊤
    else ((Real.arsinh a.toReal⁻¹ : ℝ) : EReal))

theorem acsch_coe {r : ℝ} (hr : r ≠ 0) :
    acsch (r : EReal) = some ((Real.arsinh r⁻¹ : ℝ) : EReal) := by
  unfold acsch
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_right hr]

theorem acsch_zero : acsch ((0 : ℝ) : EReal) = some ⊤ := by
  unfold acsch
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top 0, EReal.coe_ne_bot 0⟩), EReal.toReal_coe,
    ite_eq_left rfl]

@[simp] theorem acsch_top : acsch ⊤ = some ((0 : ℝ) : EReal) := by
  unfold acsch
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem acsch_bot : acsch ⊥ = some ((0 : ℝ) : EReal) := by
  unfold acsch
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`acsch` is correctly rounded.** -/
theorem acschPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acschPrecRound x p mode = liftVal Spec.acsch x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [acschPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.acsch_top, Spec.acsch_bot] <;>
      rw [EReal.coe_zero, roundVal_zero]
  | zero =>
    simp only [acschPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.acsch_zero, roundVal_top]
  | finite s e q m hv =>
    simp only [acschPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hsgn : s = true ↔ 0 < xv := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hb
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    rw [dite_eq_right (NeZero.ne p), Spec.acsch_coe hx0]
    have hirr : Irrational (-Real.arsinh |xv|⁻¹) :=
      (irrational_acsch_of_toVal habs (abs_ne_zero.mpr hx0)).neg
    have key : ∀ m' : RoundingMode,
        zivLoopCertified (acschApprox (finite s e q m hv) e) p m'
          (p + zivGuardBits + acschExtra e p)
          (acschApprox_isSome_exists p m' (toVal_finite s e q m hv) hx0 hb.1 _
            (by unfold zivGuardBits; omega))
        = roundVal p m' (some ((-Real.arsinh |xv|⁻¹ : ℝ) : EReal)) :=
      fun m' =>
      zivLoopCertified_eq_threshold' p m' _ _ (not_mem_floatSet_of_irrational p hirr) _
        (by unfold zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ := acschApprox_spec
            (toVal_finite s e q m hv) hx0 hb.1 (w := w)
            (by unfold zivGuardBits at hw; omega)
          exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _
    rw [key, acsch_abs_eq hsgn hx0]
    exact orient_roundVal s p mode (Real.arsinh xv⁻¹)

/-- **`acsch q` is correctly rounded.** -/
theorem acschRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acschRatPrecRound q p mode
      = roundVal p mode (Spec.acsch (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold acschRatPrecRound
  by_cases h0 : q.num = 0
  · rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.acsch_zero, roundVal_top]
  · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
    rw [ite_eq_right h0, asinhRatPrecRound_eq, coe_toRat_inv, Spec.asinh_coe,
      Spec.acsch_coe hq0]

end Azurite.AzFloat
