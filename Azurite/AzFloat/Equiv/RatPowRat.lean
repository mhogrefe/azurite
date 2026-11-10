/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RatPowRat
import Azurite.AzFloat.Equiv.PowRat
import Azurite.AzFloat.Equiv.RatPow

/-!
# Equivalence: `q^r` for rationals `q` and `r`

`ratPowRatPrecRound_eq : ratPowRatPrecRound q r p mode
  = roundVal p mode (Spec.pow (some q) (some r))` for `p ≠ 0`: `q^r` is correctly rounded in every
mode, with the exact comparison, and without fuel (`Spec.pow` of `Equiv/Pow.lean`).
-/

namespace Azurite.AzFloat

/-- An `AzRat` is nonzero iff its numerator is. -/
theorem coe_toRat_ne_zero_of_num_ne_zero (q : AzRat) (h0 : q.num ≠ 0) :
    (AzRat.toRat q : ℝ) ≠ 0 := by
  intro h
  have := abs_coe_toRat q
  rw [h, abs_zero] at this
  have hden := den_pos_real q
  have hnum : (q.num.toNat : ℝ) = 0 := by
    have := this.symm
    rwa [div_eq_zero_iff, or_iff_left hden.ne'] at this
  exact h0 (AzNat.toNat_injective (by exact_mod_cast hnum))

/-- An `AzRat` with zero numerator is `0`. -/
theorem coe_toRat_eq_zero_of_num_eq_zero (q : AzRat) (h0 : q.num = 0) :
    (AzRat.toRat q : ℝ) = 0 := by
  have : |(AzRat.toRat q : ℝ)| = 0 := by rw [abs_coe_toRat, h0, AzNat.toNat_zero]; simp
  exact abs_eq_zero.mp this

/-- A nonzero `AzRat` is positive iff its sign is `true`. -/
theorem sign_true_iff_toRat_pos (q : AzRat) (h0 : q.num ≠ 0) :
    q.sign = true ↔ 0 < (AzRat.toRat q : ℝ) := by
  constructor
  · intro hs; exact_mod_cast toRat_pos_of_sign q hs h0
  · intro hpos
    by_contra hs
    have hs' : q.sign = false := by cases h : q.sign <;> simp_all
    have := toRat_neg_of_sign q hs' h0
    have : (AzRat.toRat q : ℝ) < 0 := by exact_mod_cast this
    linarith

/-- **`q^r` is correctly rounded.** -/
theorem ratPowRatPrecRound_eq (q r : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ratPowRatPrecRound q r p mode
      = roundVal p mode
        (Spec.pow (some ((AzRat.toRat q : ℝ) : EReal)) (some ((AzRat.toRat r : ℝ) : EReal))) := by
  have hp := NeZero.ne p
  have h1iff := coe_toRat_eq_one_iff q
  set qv := (AzRat.toRat q : ℝ) with hqv
  set rv := (AzRat.toRat r : ℝ) with hrv
  by_cases hr0 : r.num = 0
  · have hrv0 : rv = 0 := coe_toRat_eq_zero_of_num_eq_zero r hr0
    simp only [ratPowRatPrecRound, dite_eq_left hr0]
    rw [hrv0, EReal.coe_zero, Spec.pow_some_zero, ite_eq_right hp, setPrecRound_one_eq]
  · have hrne : rv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero r hr0
    have hrv0' : ((rv : ℝ) : EReal) ≠ 0 := by rw [← EReal.coe_zero]; exact_mod_cast hrne
    have hsr : r.sign = true ↔ 0 < rv := sign_true_iff_toRat_pos r hr0
    simp only [ratPowRatPrecRound, dite_eq_right hr0]
    by_cases hq0 : q.num = 0
    · rw [dite_eq_left hq0]
      have hqv0 : qv = 0 := coe_toRat_eq_zero_of_num_eq_zero q hq0
      rw [hqv0, EReal.coe_zero, Spec.pow_some_some hrv0' (by simp), Spec.powVal_coe]
      simp only [EReal.zero_ne_top, EReal.zero_ne_bot, ↓reduceIte]
      cases hs : r.sign
      · have : ¬ 0 < rv := fun h => Bool.false_ne_true (hs.symm.trans (hsr.mpr h))
        rw [ite_eq_right this]; simp
      · rw [ite_eq_left (hsr.mp hs)]; simp
    · rw [dite_eq_right hq0, dite_eq_right hp]
      have hqne : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q hq0
      by_cases h1 : q.sign = true ∧ q.num = q.den
      · rw [ite_eq_left h1, setPrecRound_one_eq, h1iff.mpr h1, Spec.pow_one_left]
      · rw [ite_eq_right h1]
        have hx1 : (qv : EReal) ≠ 1 := fun h => h1 (h1iff.mp h)
        rw [Spec.pow_some_some hrv0' hx1, Spec.powVal_coe, ite_eq_right (EReal.coe_ne_top _),
          ite_eq_right (EReal.coe_ne_bot _),
          ite_eq_right (by rw [← EReal.coe_zero]; exact_mod_cast hqne), EReal.toReal_coe]
        have hxpos : (0 : EReal) < (qv : EReal) ↔ 0 < qv := by
          rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]
        by_cases hd : r.den = 1
        · rw [dite_eq_left hd, ratPowIntOrZiv_eq]
          have hint := coe_toRat_eq_mkNorm_of_den_one r hd
          rw [← hrv] at hint
          rw [ite_eq_left (Or.inr ⟨_, hint⟩), hint, Real.rpow_intCast, hqv,
            coe_toRat_zpow_eq_sign_mul]
        · rw [dite_eq_right hd]
          have hni : ¬ ∃ n : ℤ, rv = n := by rw [hrv]; exact not_exists_int_of_den_ne_one r hd
          by_cases hsq : q.sign = false
          · rw [dite_eq_left hsq]
            have hneg : ¬ (0 < qv) := by
              have := toRat_neg_of_sign q hsq hq0
              have : qv < 0 := by rw [hqv]; exact_mod_cast this
              exact not_lt.mpr this.le
            rw [ite_eq_right (by rintro (h | h); exact hneg (hxpos.mp h); exact hni h),
              roundVal_none]
          · rw [dite_eq_right hsq]
            have hs : q.sign = true := by revert hsq; cases q.sign <;> simp
            have hqpos : 0 < qv := by
              rw [hqv]; exact_mod_cast toRat_pos_of_sign q hs hq0
            rw [ite_eq_left (Or.inl (hxpos.mpr hqpos))]
            have hqdiv : qv = (q.num.toNat : ℝ) / q.den.toNat := by
              rw [hqv]; exact coe_toRat_eq_div_pos q hs
            split
            · next r' hT =>
              have hnum1 : 1 ≤ q.num.toNat := AzRat.num_toNat_pos q hq0
              have hden1 : 1 ≤ q.den.toNat := AzRat.den_toNat_pos q
              have hdenR : (0 : ℝ) < q.den.toNat := by exact_mod_cast hden1
              have hlogb : |Real.log qv| ≤ ((q.num.size + q.den.size : ℕ) : ℝ) := by
                rw [hqdiv]
                have := abs_log_div_le hnum1 hden1
                rw [AzNat.size_toNat, AzNat.size_toNat] at this
                exact_mod_cast this
              have hgt : decide (q.den.toNat < q.num.toNat) = true ↔ 1 < qv := by
                rw [decide_eq_true_iff, hqdiv, one_lt_div hdenR]
                exact Nat.cast_lt.symm
              refine expNearOne?_rpow_eq hqpos (fun h => hx1 (by rw [h]; rfl)) hlogb
                (abs_toRat_lt_ratTinyExp r) (fun h => hr0 ((AzRat.toRat_eq_zero_iff r).mp h))
                (toRat_sign_iff r hr0) hgt hT
            split
            · rename_i u v N hex
              have h := ratPowRatExact?_some hq0 q.den_nz
                ((AzNat.coprime_iff _ _).mp q.reduced) r hr0 hex
              rw [ratPowIntOrZiv_eq, ← h.2.2.2.2, ← hqdiv]
              simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul]
              rw [← hrv]
            · rename_i hex
              exact zivLoopCertified_eq_threshold' p mode _ _
                (by
                  have := not_mem_floatSet_of_irrational p
                    (irrational_of_ratPowRatExact?_none hq0 q.den_nz
                      ((AzNat.coprime_iff _ _).mp q.reduced) r hr0 hd hex)
                  rwa [← hqdiv] at this)
                _ (by unfold ratPowRatStart zivGuardBits; omega)
                (fun w hw => by
                  obtain ⟨lv, hv, h1', h2', h3', h4', -⟩ :=
                    ratPowRatApprox_spec false q hs hq0 r (w := w)
                      (by unfold ratPowRatStart at hw; omega)
                  simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul] at h3' h4'
                  exact ⟨lv, hv, h1', h2', h3', h4'⟩) _

end Azurite.AzFloat
