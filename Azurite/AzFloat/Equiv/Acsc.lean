/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acsc
import Azurite.AzFloat.Equiv.Atan2
import Azurite.AzFloat.Equiv.AcosWithPeriod

/-!
# Equivalence: `arccsc x`

`Spec.acsc a = arcsin (1/a)` for `|a| ≥ 1`, `0` at `±∞`, undefined inside `(−1, 1)`, and
`acscPrecRound_eq_liftVal : acscPrecRound x p mode = liftVal Spec.acsc x p mode` for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real arccosecant: `arcsin (1/a)` for `|a| ≥ 1`, `0` at `±∞`, undefined inside
`(−1, 1)`. -/
noncomputable def acsc (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then some ((0 : ℝ) : EReal)
  else if |a.toReal| < 1 then none else some ((arcsin a.toReal⁻¹ : ℝ) : EReal)

theorem acsc_coe {r : ℝ} (hr : 1 ≤ |r|) :
    acsc (r : EReal) = some ((arcsin r⁻¹ : ℝ) : EReal) := by
  unfold acsc
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_right (not_lt.mpr hr)]

theorem acsc_coe_of_lt_one {r : ℝ} (hr : |r| < 1) : acsc (r : EReal) = none := by
  unfold acsc
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_left hr]

@[simp] theorem acsc_top : acsc ⊤ = some ((0 : ℝ) : EReal) := by
  unfold acsc
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem acsc_bot : acsc ⊥ = some ((0 : ℝ) : EReal) := by
  unfold acsc
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`arccsc x` is correctly rounded.** -/
theorem acscPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acscPrecRound x p mode = liftVal Spec.acsc x p mode := by
  unfold liftVal
  have hpi2 := fun (p : ℕ) [NeZero p] (m : RoundingMode) => piDiv2PrecRound_eq_liftVal₀ p m
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [acscPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.acsc_top, Spec.acsc_bot] <;>
      rw [EReal.coe_zero, roundVal_zero]
  | zero =>
    simp only [acscPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.acsc_coe_of_lt_one (by simp), roundVal_none]
  | finite s e q m hv =>
    simp only [acscPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hneg : (!s) = true ↔ xv < 0 := finiteVal_neg_iff s e hv
    have hsgn : s = true ↔ 0 < xv := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hb
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    by_cases h1 : eqIEEE (finite s e q m hv).abs one = true
    · rw [dite_eq_left h1, signedRound_eq hpi2]
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
      rw [habs] at hv1
      rw [toVal_one'] at hv2
      have habs1 : |xv| = 1 := by
        have := hv1.trans hv2.symm
        exact_mod_cast Option.some.inj this
      rw [Spec.acsc_coe habs1.ge]
      cases s with
      | true =>
        have hx1 : xv = 1 := by rw [← habs1, abs_of_pos (hsgn.mp rfl)]
        simp only [↓reduceIte]
        rw [hx1, inv_one, arcsin_one]
      | false =>
        have hlt : xv < 0 := hneg.mp rfl
        have hx1 : xv = -1 := by
          rw [abs_of_neg hlt] at habs1
          linarith
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hx1, inv_neg, inv_one, arcsin_neg_one]
    · rw [dite_eq_right h1]
      have hne1 : |xv| ≠ 1 := fun h =>
        h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)
      by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
      · rw [dite_eq_left he, dite_eq_right (NeZero.ne p)]
        have hgt : 1 < |xv| := one_lt_abs_of_exponent hb.1 he hne1
        have hen := two_pow_le_of_exponent hb.1 he
        rw [Spec.acsc_coe hgt.le]
        have hirr : Irrational (arcsin |xv|⁻¹) :=
          irrational_acsc_of_toVal habs (by rw [abs_abs]; exact hgt.le)
        have key : ∀ m' : RoundingMode,
            zivLoopCertified (acscApprox (finite s e q m hv) e.abs.toNat) p m'
              (p + zivGuardBits)
              (acscApprox_isSome_exists p m' (toVal_finite s e q m hv) hgt hen
                (p + zivGuardBits) (by unfold zivGuardBits; omega))
            = roundVal p m' (some ((arcsin |xv|⁻¹ : ℝ) : EReal)) :=
          fun m' =>
          zivLoopCertified_eq_threshold' p m' _ _ (not_mem_floatSet_of_irrational p hirr) _
            (by unfold zivGuardBits; omega)
            (fun w _ => by
              obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ := acscApprox_spec
                (toVal_finite s e q m hv) hgt hen w
              exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _
        rw [key, acsc_abs_eq hneg]
        exact orient_roundVal (!s) p mode (arcsin xv⁻¹)
      · rw [dite_eq_right he]
        have hlt1 : |xv| < 1 := abs_lt_one_of_exponent hb.2 he
        rw [Spec.acsc_coe_of_lt_one hlt1, roundVal_none]

end Azurite.AzFloat
