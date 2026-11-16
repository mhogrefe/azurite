/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asec
import Azurite.AzFloat.Equiv.Acos

/-!
# Equivalence: `arcsec x`

`Spec.asec : EReal → Option EReal` (`arccos (1/a)` for `|a| ≥ 1`, `π/2` at `±∞`, undefined
inside `(−1, 1)`) and
`asecPrecRound_eq_liftVal : asecPrecRound x p mode = liftVal Spec.asec x p mode` for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real arcsecant: `arccos (1/a)` for `|a| ≥ 1`, `π/2` at `±∞`, undefined inside
`(−1, 1)`. -/
noncomputable def asec (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then some ((π / 2 : ℝ) : EReal)
  else if |a.toReal| < 1 then none else some ((arccos a.toReal⁻¹ : ℝ) : EReal)

theorem asec_coe {r : ℝ} (hr : 1 ≤ |r|) :
    asec (r : EReal) = some ((arccos r⁻¹ : ℝ) : EReal) := by
  unfold asec
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_right (not_lt.mpr hr)]

theorem asec_coe_of_lt_one {r : ℝ} (hr : |r| < 1) : asec (r : EReal) = none := by
  unfold asec
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_left hr]

@[simp] theorem asec_top : asec ⊤ = some ((π / 2 : ℝ) : EReal) := by
  unfold asec
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem asec_bot : asec ⊥ = some ((π / 2 : ℝ) : EReal) := by
  unfold asec
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`arcsec x` is correctly rounded.** -/
theorem asecPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asecPrecRound x p mode = liftVal Spec.asec x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;>
      simp only [asecPrecRound, toVal_infinity, Option.bind_some, ↓reduceIte,
        Bool.false_eq_true, Spec.asec_top, Spec.asec_bot] <;>
      exact piDiv2PrecRound_eq_liftVal₀ p mode
  | zero =>
    simp only [asecPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.asec_coe_of_lt_one (by simp), roundVal_none]
  | finite s e q m hv =>
    simp only [asecPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hneg : (!s) = true ↔ xv < 0 := finiteVal_neg_iff s e hv
    have hsgn : s = true ↔ 0 < xv := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hb
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    by_cases h1 : eqIEEE (finite s e q m hv).abs one = true
    · rw [dite_eq_left h1]
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
      rw [habs] at hv1
      rw [toVal_one'] at hv2
      have habs1 : |xv| = 1 := by
        have := hv1.trans hv2.symm
        exact_mod_cast Option.some.inj this
      rw [Spec.asec_coe habs1.ge, eq_signed_of_abs_eq hsgn hx0 habs1]
      cases s with
      | true =>
        simp only [↓reduceIte]
        rw [inv_one, arccos_one, EReal.coe_zero, roundVal_zero]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [inv_neg, inv_one, arccos_neg_one, piPrecRound_eq_liftVal₀]
        rfl
    · rw [dite_eq_right h1]
      have hne1 : |xv| ≠ 1 := fun h =>
        h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)
      by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
      · rw [dite_eq_left he, dite_eq_right (NeZero.ne p)]
        have hgt : 1 < |xv| := one_lt_abs_of_exponent hb.1 he hne1
        rw [Spec.asec_coe hgt.le]
        exact zivLoopCertified_eq_threshold' p mode _ (arccos xv⁻¹)
          (not_mem_floatSet_of_irrational p
            (irrational_asec_of_toVal (toVal_finite s e q m hv) hgt))
          _ (by unfold zivGuardBits; omega)
          (fun w _ => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := asecApprox_spec
              (toVal_finite s e q m hv) hgt hneg w
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
      · rw [dite_eq_right he]
        have hlt1 : |xv| < 1 := abs_lt_one_of_exponent hb.2 he
        rw [Spec.asec_coe_of_lt_one hlt1, roundVal_none]

end Azurite.AzFloat
