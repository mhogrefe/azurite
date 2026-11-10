/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowRat
import Azurite.AzFloat.Equiv.Pow
import Azurite.AzFloat.Equiv.RatPow

/-!
# Equivalence: `x^q` for a rational exponent

`powRatPrecRound_eq : powRatPrecRound x q p mode = roundVal p mode (Spec.pow x.toVal (some q))`
for `p ≠ 0`: `x^q` is correctly rounded in every mode, with the exact comparison, and without
fuel (`Spec.pow` of `Equiv/Pow.lean`).
-/

namespace Azurite.AzFloat

/-- An `AzRat` with `den = 1` is the integer `± num`. -/
theorem coe_toRat_eq_mkNorm_of_den_one (q : AzRat) (hd : q.den = 1) :
    (AzRat.toRat q : ℝ) = ((AzInt.mkNorm q.sign q.num).toInt : ℝ) := by
  rw [coe_toRat_eq_mkNorm_div, hd, AzNat.toNat_one, Nat.cast_one, div_one]

/-- An `AzRat` with `den ≠ 1` is not an integer. -/
theorem not_exists_int_of_den_ne_one (q : AzRat) (hd : q.den ≠ 1) :
    ¬ ∃ n : ℤ, (AzRat.toRat q : ℝ) = n := by
  rintro ⟨n, hn⟩
  have hq : AzRat.toRat q = (n : ℚ) := by exact_mod_cast hn
  have hden := congrArg Rat.den hq
  rw [Rat.den_intCast] at hden
  have : q.den.toNat = 1 := hden
  exact hd (AzNat.toNat_injective (by rw [this, AzNat.toNat_one]))

/-- `q` is an odd integer iff `den = 1` and `num` is odd. -/
theorem den_one_and_odd_iff (q : AzRat) :
    (q.den = 1 ∧ q.num.isOdd = true) ↔ ∃ n : ℤ, Odd n ∧ (AzRat.toRat q : ℝ) = n := by
  constructor
  · rintro ⟨hd, ho⟩
    refine ⟨(AzInt.mkNorm q.sign q.num).toInt, ?_, coe_toRat_eq_mkNorm_of_den_one q hd⟩
    rw [AzNat.isOdd_iff] at ho
    by_cases h0 : q.num = 0
    · rw [h0, AzNat.toNat_zero] at ho; simp at ho
    cases q.sign
    · rw [AzInt.toInt_mkNorm_false _ h0]; exact (by exact_mod_cast ho : Odd _).neg
    · rw [AzInt.toInt_mkNorm_true]; exact_mod_cast ho
  · rintro ⟨n, hodd, hn⟩
    have hd : q.den = 1 := by
      by_contra hd
      exact not_exists_int_of_den_ne_one q hd ⟨n, hn⟩
    refine ⟨hd, ?_⟩
    rw [coe_toRat_eq_mkNorm_of_den_one q hd] at hn
    have hn' : (AzInt.mkNorm q.sign q.num).toInt = n := by exact_mod_cast hn
    rw [AzNat.isOdd_iff]
    by_cases h0 : q.num = 0
    · exfalso
      rw [h0] at hn'
      have : (AzInt.mkNorm q.sign 0).toInt = 0 := by cases q.sign <;> rfl
      rw [this] at hn'
      rw [← hn'] at hodd
      exact (Int.not_even_iff_odd.mpr hodd) ⟨0, rfl⟩
    cases hs : q.sign
    · rw [hs, AzInt.toInt_mkNorm_false _ h0] at hn'
      have h' : Odd (-(q.num.toNat : ℤ)) := hn' ▸ hodd
      have h'' := h'.neg
      rw [neg_neg] at h''
      exact_mod_cast h''
    · rw [hs, AzInt.toInt_mkNorm_true] at hn'
      exact_mod_cast hn' ▸ hodd

/-- **`x^q` is correctly rounded.** -/
theorem powRatPrecRound_eq (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    powRatPrecRound x q p mode
      = roundVal p mode (Spec.pow x.toVal (some ((AzRat.toRat q : ℝ) : EReal))) := by
  have hp := NeZero.ne p
  set qv := (AzRat.toRat q : ℝ) with hqv
  by_cases hq0 : q.num = 0
  · have hqv0 : qv = 0 := by
      have : |qv| = 0 := by rw [hqv, abs_coe_toRat, hq0, AzNat.toNat_zero]; simp
      exact abs_eq_zero.mp this
    simp only [powRatPrecRound, dite_eq_left hq0]
    rw [hqv0, EReal.coe_zero, Spec.pow_some_zero, ite_eq_right hp, setPrecRound_one_eq]
  · have hqne : qv ≠ 0 := by
      intro h
      have := abs_coe_toRat q
      rw [← hqv, h, abs_zero] at this
      have hden := den_pos_real q
      have hnum : (q.num.toNat : ℝ) = 0 := by
        have := this.symm
        rwa [div_eq_zero_iff, or_iff_left hden.ne'] at this
      exact hq0 (AzNat.toNat_injective (by exact_mod_cast hnum))
    have hqv0' : ((qv : ℝ) : EReal) ≠ 0 := by rw [← EReal.coe_zero]; exact_mod_cast hqne
    have hsq : q.sign = true ↔ 0 < qv := by
      constructor
      · intro hs; rw [hqv]; exact_mod_cast toRat_pos_of_sign q hs hq0
      · intro hpos
        by_contra hs
        have hs' : q.sign = false := by cases h : q.sign <;> simp_all
        have := toRat_neg_of_sign q hs' hq0
        have : qv < 0 := by rw [hqv]; exact_mod_cast this
        linarith
    simp only [powRatPrecRound, dite_eq_right hq0]
    cases x with
    | nan =>
      simp only [toVal_nan]
      rw [Spec.pow_none_left (by simpa using hqv0'), roundVal_none]
    | zero =>
      simp only [toVal_zero]
      rw [Spec.pow_some_some hqv0' (by simp), Spec.powVal_coe]
      simp only [EReal.zero_ne_top, EReal.zero_ne_bot, ↓reduceIte]
      cases hs : q.sign
      · have : ¬ 0 < qv := fun h => Bool.false_ne_true (hs.symm.trans (hsq.mpr h))
        rw [ite_eq_right this]; simp
      · rw [ite_eq_left (hsq.mp hs)]; simp
    | infinity sx =>
      simp only [toVal_infinity]
      rw [Spec.pow_some_some hqv0' (ereal_ite_ne_one sx), Spec.powVal_coe]
      cases sx
      · simp only [Bool.false_eq_true, ↓reduceIte, bot_ne_top]
        cases hs : q.sign
        · have : ¬ 0 < qv := fun h => Bool.false_ne_true (hs.symm.trans (hsq.mpr h))
          simp only [Bool.false_eq_true, ↓reduceIte, this]
          simp
        · have hpos : 0 < qv := hsq.mp hs
          simp only [↓reduceIte, hpos]
          by_cases hodd : q.den = 1 ∧ q.num.isOdd = true
          · rw [ite_eq_left hodd, ite_eq_left ((den_one_and_odd_iff q).mp hodd)]; simp
          · rw [ite_eq_right hodd, ite_eq_right (fun h => hodd ((den_one_and_odd_iff q).mpr h))]
            simp
      · simp only [↓reduceIte]
        cases hs : q.sign
        · have : ¬ 0 < qv := fun h => Bool.false_ne_true (hs.symm.trans (hsq.mpr h))
          simp only [Bool.false_eq_true, ↓reduceIte, this]
          simp
        · have hpos : 0 < qv := hsq.mp hs
          simp only [↓reduceIte, hpos]
          simp
    | finite sx ex qx mx hvx =>
      set xv := finiteVal sx ex mx with hxv
      have hx0 : xv ≠ 0 := finiteVal_ne_zero sx ex hvx
      simp only [toVal_finite]
      rw [dite_eq_right hp]
      by_cases h1 : eqIEEE (finite sx ex qx mx hvx) one = true
      · rw [ite_eq_left h1, setPrecRound_one_eq]
        have := (eqIEEE_one_iff _).mp h1
        rw [toVal_finite, ← hxv] at this
        rw [this, Spec.pow_one_left]
      · rw [ite_eq_right h1]
        have hx1 : ((xv : ℝ) : EReal) ≠ 1 :=
          fun h => h1 ((eqIEEE_one_iff _).mpr (by rw [toVal_finite, ← hxv, h]))
        rw [Spec.pow_some_some hqv0' hx1, Spec.powVal_coe, ite_eq_right (EReal.coe_ne_top _),
          ite_eq_right (EReal.coe_ne_bot _),
          ite_eq_right (by rw [← EReal.coe_zero]; exact_mod_cast hx0), EReal.toReal_coe]
        have hxpos : (0 : EReal) < (xv : EReal) ↔ 0 < xv := by
          rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]
        by_cases hd : q.den = 1
        · rw [dite_eq_left hd, powIntOrZiv_eq]
          have hint := coe_toRat_eq_mkNorm_of_den_one q hd
          rw [← hqv] at hint
          rw [ite_eq_left (Or.inr ⟨_, hint⟩), hint, Real.rpow_intCast]
        · rw [dite_eq_right hd]
          have hni : ¬ ∃ n : ℤ, qv = n := by rw [hqv]; exact not_exists_int_of_den_ne_one q hd
          by_cases hsx : sx = false
          · rw [dite_eq_left hsx]
            have hneg : ¬ (0 < xv) := by
              rw [hxv, hsx]; exact not_lt.mpr (finiteVal_false_neg ex hvx).le
            rw [ite_eq_right (by rintro (h | h); exact hneg (hxpos.mp h); exact hni h),
              roundVal_none]
          · rw [dite_eq_right hsx]
            have hsx' : sx = true := by cases sx <;> simp_all
            subst hsx'
            have hxp : 0 < xv := finiteVal_true_pos ex hvx
            rw [ite_eq_left (Or.inl (hxpos.mpr hxp))]
            split
            · next r hT =>
              refine expNearOne?_rpow_eq hxp (fun h => hx1 (by rw [h]; rfl))
                ((abs_log_finiteVal_le ex hvx).trans
                  (by rw [abs_toInt_cast]; push_cast; exact le_rfl))
                (abs_toRat_lt_ratTinyExp q)
                (fun h => hq0 ((AzRat.toRat_eq_zero_iff q).mp h)) (toRat_sign_iff q hq0)
                (lt_eq_true_iff toVal_one' (toVal_finite true ex qx mx hvx)) hT
            split
            · rename_i z N hex
              obtain ⟨zv, hzv, hzpos, hval, hN0⟩ := powRatExact?_some ex hvx q hq0 hex
              obtain ⟨ez, qz, mz, hvz, rfl, hzval⟩ := eq_finite_true_of_toVal_pos hzv hzpos
              simp only []
              rw [dite_eq_right (fun h => hN0 (by rw [h, AzInt.toInt_zero])), powIntOrZiv_eq, hzval,
                ← hval]
            · rename_i hex
              exact zivLoopCertified_eq_threshold' p mode _ _
                (by
                  have := not_mem_floatSet_of_irrational p
                    (irrational_of_powRatExact?_none ex hvx q hq0 hd hex)
                  rwa [← hxv, ← hqv] at this)
                _ (by unfold powRatStart zivGuardBits; omega)
                (fun w hw => by
                  obtain ⟨lv, hv, h1', h2', h3', h4', -⟩ :=
                    powRatApprox_spec false ex hvx q (w := w) (by unfold powRatStart at hw; omega)
                  simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul] at h3' h4'
                  rw [← hxv, ← hqv] at h3' h4'
                  exact ⟨lv, hv, h1', h2', h3', h4'⟩) _

end Azurite.AzFloat
