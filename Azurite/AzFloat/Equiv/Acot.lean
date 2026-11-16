/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acot
import Azurite.AzFloat.Equiv.AcosWithPeriod

/-!
# Equivalence: `arccot x`

`Spec.acot a = arctan (1/a)` for `a ≠ 0`, `π/2` at `0`, `0` at `±∞`, and
`acotPrecRound_eq_liftVal : acotPrecRound x p mode = liftVal Spec.acot x p mode` for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real odd arccotangent: `arctan (1/a)` for `a ≠ 0`, `π/2` at `0` (the limit from
the right), `0` at `±∞`. -/
noncomputable def acot (a : EReal) : Option EReal :=
  some (if a = ⊤ ∨ a = ⊥ then ((0 : ℝ) : EReal)
    else if a.toReal = 0 then ((π / 2 : ℝ) : EReal) else ((arctan a.toReal⁻¹ : ℝ) : EReal))

theorem acot_coe {r : ℝ} (hr : r ≠ 0) :
    acot (r : EReal) = some ((arctan r⁻¹ : ℝ) : EReal) := by
  unfold acot
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_right hr]

theorem acot_zero : acot ((0 : ℝ) : EReal) = some ((π / 2 : ℝ) : EReal) := by
  unfold acot
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top 0, EReal.coe_ne_bot 0⟩), EReal.toReal_coe,
    ite_eq_left rfl]

@[simp] theorem acot_top : acot ⊤ = some ((0 : ℝ) : EReal) := by
  unfold acot
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem acot_bot : acot ⊥ = some ((0 : ℝ) : EReal) := by
  unfold acot
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`arccot x` is correctly rounded.** -/
theorem acotPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acotPrecRound x p mode = liftVal Spec.acot x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [acotPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.acot_top, Spec.acot_bot] <;>
      rw [EReal.coe_zero, roundVal_zero]
  | zero =>
    simp only [acotPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.acot_zero, piDiv2PrecRound_eq_liftVal₀]
    rfl
  | finite s e q m hv =>
    simp only [acotPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hsgn : s = true ↔ 0 < xv := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hb
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    rw [dite_eq_right (NeZero.ne p), Spec.acot_coe hx0]
    have hirr : Irrational (-arctan |xv|⁻¹) :=
      (irrational_acot_of_toVal habs (abs_ne_zero.mpr hx0)).neg
    have key : ∀ m' : RoundingMode,
        zivLoopCertified (acotApprox (finite s e q m hv) e) p m' (p + zivGuardBits)
          (acotApprox_isSome_exists p m' (toVal_finite s e q m hv) hx0 hb.1 hb.2
            (p + zivGuardBits) (by unfold zivGuardBits; omega))
        = roundVal p m' (some ((-arctan |xv|⁻¹ : ℝ) : EReal)) :=
      fun m' =>
      zivLoopCertified_eq_threshold' p m' _ _ (not_mem_floatSet_of_irrational p hirr) _
        (by unfold zivGuardBits; omega)
        (fun w _ => by
          obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ := acotApprox_spec
            (toVal_finite s e q m hv) hx0 hb.1 hb.2 w
          exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _
    rw [key, acot_abs_eq hsgn hx0]
    exact orient_roundVal s p mode (arctan xv⁻¹)

end Azurite.AzFloat
