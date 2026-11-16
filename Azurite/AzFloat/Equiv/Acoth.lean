/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acoth
import Azurite.AzFloat.AcothRat
import Azurite.AzFloat.Equiv.Atanh
import Azurite.AzFloat.Equiv.AsecRat
import Azurite.AzFloat.Equiv.AcosWithPeriod

/-!
# Equivalence: `acoth x` and `acoth q`

`Spec.acoth a = atanh (1/a)` for a finite `a ≠ 0` (so `±∞` at `±1`, undefined for `|a| < 1`),
undefined at `0`, `0` at `±∞`;
`acothPrecRound_eq_liftVal : acothPrecRound x p mode = liftVal Spec.acoth x p mode` and
`acothRatPrecRound_eq : acothRatPrecRound q p mode = roundVal p mode (Spec.acoth q)`, for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `acoth`: `atanh (1/a)` for a finite `a ≠ 0` (`artanh (1/a)` for `|a| > 1`,
`±∞` at `±1`, undefined for `0 < |a| < 1`), undefined at `0`, `0` at `±∞`. -/
noncomputable def acoth (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then some ((0 : ℝ) : EReal)
  else if a.toReal = 0 then none else atanh ((a.toReal⁻¹ : ℝ) : EReal)

theorem acoth_coe {r : ℝ} (hr : r ≠ 0) : acoth (r : EReal) = atanh ((r⁻¹ : ℝ) : EReal) := by
  unfold acoth
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_right hr]

theorem acoth_zero : acoth ((0 : ℝ) : EReal) = none := by
  unfold acoth
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top 0, EReal.coe_ne_bot 0⟩), EReal.toReal_coe,
    ite_eq_left rfl]

@[simp] theorem acoth_top : acoth ⊤ = some ((0 : ℝ) : EReal) := by
  unfold acoth
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem acoth_bot : acoth ⊥ = some ((0 : ℝ) : EReal) := by
  unfold acoth
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`acoth` is correctly rounded.** -/
theorem acothPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acothPrecRound x p mode = liftVal Spec.acoth x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [acothPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.acoth_top, Spec.acoth_bot] <;>
      rw [EReal.coe_zero, roundVal_zero]
  | zero =>
    simp only [acothPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.acoth_zero, roundVal_none]
  | finite s e q m hv =>
    simp only [acothPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hsgn : s = true ↔ 0 < xv := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hb
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    rw [Spec.acoth_coe hx0]
    by_cases h1 : eqIEEE (finite s e q m hv).abs one = true
    · rw [dite_eq_left h1]
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
      rw [habs] at hv1
      rw [toVal_one'] at hv2
      have habs1 : |xv| = 1 := by
        have := hv1.trans hv2.symm
        exact_mod_cast Option.some.inj this
      refine atanh_spec_abs_one (xv := xv⁻¹) ?_ (by rw [abs_inv, habs1, inv_one]) p mode
      rw [hsgn, inv_pos]
    · rw [dite_eq_right h1]
      have hne : |xv| ≠ 1 := fun h =>
        h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)
      by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
      · rw [dite_eq_left he, dite_eq_right (NeZero.ne p)]
        have hgt : 1 < |xv| := one_lt_abs_of_exponent hb.1 he hne
        have hlt : |xv⁻¹| < 1 := by
          rw [abs_inv]
          exact inv_lt_one_of_one_lt₀ hgt
        rw [Spec.atanh_coe hlt]
        have hirr : Irrational (Real.artanh |xv|⁻¹) :=
          irrational_acoth_of_toVal habs (by rwa [abs_abs])
        have key : ∀ m' : RoundingMode,
            zivLoopCertified (acothApprox (finite s e q m hv) e) p m'
              (p + zivGuardBits + acschExtra e p)
              (acothApprox_isSome_exists p m' (toVal_finite s e q m hv) hgt he hb.1 _
                (by unfold zivGuardBits; omega))
            = roundVal p m' (some ((Real.artanh |xv|⁻¹ : ℝ) : EReal)) :=
          fun m' =>
          zivLoopCertified_eq_threshold' p m' _ _ (not_mem_floatSet_of_irrational p hirr) _
            (by unfold zivGuardBits; omega)
            (fun w hw => by
              obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ := acothApprox_spec
                (toVal_finite s e q m hv) hgt he hb.1 (w := w)
                (by unfold zivGuardBits at hw; omega)
              exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _
        rw [key, acoth_abs_eq (finiteVal_neg_iff s e hv)]
        exact orient_roundVal (!s) p mode (Real.artanh xv⁻¹)
      · rw [dite_eq_right he]
        have hlt : |xv| < 1 := abs_lt_one_of_exponent hb.2 he
        have hgt : 1 < |xv⁻¹| := by
          rw [abs_inv]
          exact (one_lt_inv₀ (abs_pos.mpr hx0)).mpr hlt
        rw [Spec.atanh_coe_of_one_lt hgt, roundVal_none]

/-- **`acoth q` is correctly rounded.** -/
theorem acothRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acothRatPrecRound q p mode
      = roundVal p mode (Spec.acoth (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold acothRatPrecRound
  by_cases h0 : q.num = 0
  · rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.acoth_zero, roundVal_none]
  · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
    rw [ite_eq_right h0, atanhRatPrecRound_eq, coe_toRat_inv, Spec.acoth_coe hq0]

end Azurite.AzFloat
