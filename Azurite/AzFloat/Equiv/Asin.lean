/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asin
import Azurite.AzFloat.Equiv.Atan2

/-!
# Equivalence: `arcsin x`

`Spec.asin : EReal → Option EReal` (undefined, i.e. `NaN`, outside `[−1, 1]`) and
`asinPrecRound_eq_liftVal : asinPrecRound x p mode = liftVal Spec.asin x p mode` for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real arcsine: undefined outside `[−1, 1]`. -/
noncomputable def asin (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ ∨ 1 < |a.toReal| then none else some ((arcsin a.toReal : ℝ) : EReal)

theorem asin_coe {r : ℝ} (hr : |r| ≤ 1) : asin (r : EReal) = some ((arcsin r : ℝ) : EReal) := by
  unfold asin
  rw [ite_eq_right (by
    rw [EReal.toReal_coe]
    exact not_or.mpr ⟨EReal.coe_ne_top r, not_or.mpr ⟨EReal.coe_ne_bot r, not_lt.mpr hr⟩⟩),
    EReal.toReal_coe]

theorem asin_coe_of_one_lt {r : ℝ} (hr : 1 < |r|) : asin (r : EReal) = none := by
  unfold asin
  rw [ite_eq_left (by
    rw [EReal.toReal_coe]
    exact Or.inr (Or.inr hr))]

@[simp] theorem asin_top : asin ⊤ = none := by
  unfold asin
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem asin_bot : asin ⊥ = none := by
  unfold asin
  rw [ite_eq_left (Or.inr (Or.inl rfl))]

end Spec

/-- **`arcsin x` is correctly rounded.** -/
theorem asinPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asinPrecRound x p mode = liftVal Spec.asin x p mode := by
  unfold liftVal
  have hpi2 := fun (p : ℕ) [NeZero p] (m : RoundingMode) => piDiv2PrecRound_eq_liftVal₀ p m
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [asinPrecRound]
  | zero =>
    simp only [asinPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.asin_coe (by simp), arcsin_zero, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [asinPrecRound, toVal_finite, Option.bind_some]
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
    · rw [ite_eq_left h1, signedRound_eq hpi2]
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
      rw [habs] at hv1
      rw [toVal_one'] at hv2
      have habs1 : |xv| = 1 := by
        have := hv1.trans hv2.symm
        exact_mod_cast Option.some.inj this
      rw [Spec.asin_coe habs1.le]
      cases s with
      | true =>
        have hx1 : xv = 1 := by rw [← habs1, abs_of_pos (hsgn.mp rfl)]
        simp only [↓reduceIte]
        rw [hx1, arcsin_one]
      | false =>
        have hlt : xv < 0 := hneg.mp rfl
        have hx1 : xv = -1 := by
          rw [abs_of_neg hlt] at habs1
          linarith
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hx1, arcsin_neg_one]
    · rw [ite_eq_right h1]
      have hne1 : |xv| ≠ 1 := fun h =>
        h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)
      by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
      · rw [dite_eq_left he]
        have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
        have h1e : 1 ≤ e.toInt := by
          rw [htoInt, he.1]
          simp only [↓reduceIte]
          have := he.2
          omega
        have hge : 1 ≤ |xv| := le_trans (one_le_zpow₀ (by norm_num) (by omega)) hb.1
        rw [Spec.asin_coe_of_one_lt (lt_of_le_of_ne hge (Ne.symm hne1)), roundVal_none]
      · rw [dite_eq_right he, dite_eq_right (NeZero.ne p)]
        have hlt1 : |xv| < 1 := abs_lt_one_of_exponent hb.2 he
        rw [Spec.asin_coe hlt1.le]
        split
        · next r hT => exact asinTiny?_eq hv p mode hT
        have hval := arcsin_eq_of_neg_iff hneg
        exact zivLoopCertified_eq_threshold' p mode _ (arcsin xv)
          (not_mem_floatSet_of_irrational p
            (irrational_arcsin_of_toVal (toVal_finite s e q m hv) hx0 hlt1.le))
          _ (by unfold zivGuardBits; omega)
          (fun w _ => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := asinApprox_spec (!s)
              (toVal_finite s e q m hv) hx0 hlt1 e w
            rw [← hval] at hlo hhi
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
