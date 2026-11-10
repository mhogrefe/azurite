/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RatPow
import Azurite.AzFloat.Equiv.Pow

/-!
# Equivalence: `q^y` for a rational `q`

`ratPowPrecRound_eq : ratPowPrecRound q y p mode = roundVal p mode (Spec.pow (some q) y.toVal)`
for `p ≠ 0`: `q^y` is correctly rounded in every mode, with the exact comparison, and without
fuel (`Spec.pow` of `Equiv/Pow.lean`).
-/

namespace Azurite.AzFloat

/-- The value of an `AzRat`: `± num / den`. -/
theorem coe_toRat_eq_sign_mul (q : AzRat) :
    (AzRat.toRat q : ℝ) = (if q.sign then 1 else -1) * ((q.num.toNat : ℝ) / q.den.toNat) := by
  rw [AzRat.toRat_cast_eq]
  cases q.sign <;> simp [div_eq_mul_inv]

/-- `|q| = num / den`. -/
theorem abs_coe_toRat (q : AzRat) : |(AzRat.toRat q : ℝ)| = (q.num.toNat : ℝ) / q.den.toNat := by
  rw [coe_toRat_eq_sign_mul, abs_mul]
  have : (0 : ℝ) ≤ (q.num.toNat : ℝ) / q.den.toNat := by positivity
  rw [abs_of_nonneg this]
  cases q.sign <;> simp

theorem den_pos_real (q : AzRat) : (0 : ℝ) < q.den.toNat := by
  exact_mod_cast AzRat.den_toNat_pos q

/-- `q = 1` iff `q` is positive with `num = den`. -/
theorem coe_toRat_eq_one_iff (q : AzRat) :
    ((AzRat.toRat q : ℝ) : EReal) = 1 ↔ (q.sign = true ∧ q.num = q.den) := by
  rw [← EReal.coe_one, EReal.coe_eq_coe_iff]
  constructor
  · intro h
    have hs : q.sign = true := by
      by_contra hs
      have hs' : q.sign = false := by cases hq : q.sign <;> simp_all
      have h0 : q.num ≠ 0 := fun h0 => by rw [q.zero_sign h0] at hs'; cases hs'
      have := toRat_neg_of_sign q hs' h0
      have : (AzRat.toRat q : ℝ) < 0 := by exact_mod_cast this
      linarith
    refine ⟨hs, ?_⟩
    by_contra hne
    exact toRat_ne_one_of_num_ne_den q hs hne (by exact_mod_cast h)
  · rintro ⟨hs, h⟩
    exact_mod_cast toRat_eq_one_of_num_eq_den q hs h

/-- `q ^ n = ± |q|^n` with the sign `(−1)^n` for a negative `q`. -/
theorem coe_toRat_zpow_eq_sign_mul (q : AzRat) (n : AzInt) :
    (AzRat.toRat q : ℝ) ^ n.toInt
      = powSign (!q.sign && n.abs.isOdd) * ((q.num.toNat : ℝ) / q.den.toNat) ^ n.toInt := by
  rw [coe_toRat_eq_sign_mul, mul_zpow]
  cases hs : q.sign with
  | true => simp [powSign]
  | false =>
    simp only [Bool.not_false, Bool.true_and, powSign, Bool.false_eq_true, ↓reduceIte]
    have hodd : n.abs.isOdd = true ↔ Odd n.toInt := by
      rw [abs_isOdd_iff, toNat_abs_eq_natAbs, Int.natAbs_odd]
    cases h : n.abs.isOdd
    · have : Even n.toInt := by
        rw [← Int.not_odd_iff_even]
        intro ho
        have := hodd.mpr ho
        rw [h] at this
        exact Bool.false_ne_true this
      rw [this.neg_one_zpow]
      simp
    · rw [(hodd.mp h).neg_one_zpow]
      simp

/-! ### The integer-power path -/

/-- `ratPowIntOrZiv` is the correctly rounded `± (a/b)^n`. -/
theorem ratPowIntOrZiv_eq (neg : Bool) (a b : AzNat) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a.toNat b.toNat) {n : AzInt} (hn : n ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ratPowIntOrZiv neg a b ha hb hcop n hn p mode
      = roundVal p mode
        (some ((powSign neg * ((a.toNat : ℝ) / b.toNat) ^ n.toInt : ℝ) : EReal)) := by
  unfold ratPowIntOrZiv
  by_cases hc : ratPowIntCheap a b n p = true
  · rw [dite_eq_left hc]
    dsimp only
    -- the numerator and denominator by the sign of `n`
    obtain ⟨A, B, hA, hB, hval⟩ : ∃ A B : AzNat, A = (if n.sign then a else b) ∧
        B = (if n.sign then b else a) ∧
        ((a.toNat : ℝ) / b.toNat) ^ n.toInt = ((A.toNat : ℝ) / B.toNat) ^ (n.abs.toNat) := by
      refine ⟨_, _, rfl, rfl, ?_⟩
      rw [toNat_abs_eq_natAbs]
      cases hs : n.sign
      · have hneg : n.toInt < 0 := by
          have := (sign_true_iff n).not.mp (by simp [hs])
          push Not at this
          exact this
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← zpow_natCast, Int.ofNat_natAbs_of_nonpos hneg.le, zpow_neg, ← inv_zpow, inv_div]
      · have hpos : 0 ≤ n.toInt := (sign_true_iff n).mp hs
        simp only [↓reduceIte]
        rw [← zpow_natCast, Int.natAbs_of_nonneg hpos]
    rw [← hA, ← hB]
    have hA0 : A ≠ 0 := by rw [hA]; split_ifs <;> assumption
    have hB0 : B ≠ 0 := by rw [hB]; split_ifs <;> assumption
    obtain ⟨hAdec, hAodd⟩ := splitOdd_spec A hA0
    obtain ⟨hBdec, hBodd⟩ := splitOdd_spec B hB0
    have hB'pos : (0 : ℝ) < (splitOdd B).1.toNat := by
      exact_mod_cast Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hBodd; simp at hBodd)
    -- the exact floats
    have hnum : (ofAzNat ((splitOdd A).1.pow n.abs.toNat) <<<
        ((AzNat.ofNat (splitOdd A).2).toAzInt * n.abs.toAzInt
          - (AzNat.ofNat (splitOdd B).2).toAzInt * n.abs.toAzInt)).toVal
        = some ((((splitOdd A).1.toNat : ℝ) ^ n.abs.toNat
          * (2 : ℝ) ^ (((splitOdd A).2 : ℤ) * n.abs.toNat - ((splitOdd B).2 : ℤ) * n.abs.toNat) :
            ℝ) : EReal) := by
      rw [toVal_shiftLeft_of_toVal (toVal_ofAzNat _), AzNat.toNat_pow, AzInt.toInt_sub,
        AzInt.toInt_mul, AzInt.toInt_mul, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt,
        AzNat.toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
      push_cast
      rfl
    have hden : (ofAzNat ((splitOdd B).1.pow n.abs.toNat)).toVal
        = some ((((splitOdd B).1.toNat : ℝ) ^ n.abs.toNat : ℝ) : EReal) := by
      rw [toVal_ofAzNat, AzNat.toNat_pow]; push_cast; rfl
    have hvalue : powSign neg * ((A.toNat : ℝ) / B.toNat) ^ n.abs.toNat
        = powSign neg * (((splitOdd A).1.toNat : ℝ) ^ n.abs.toNat
            * (2 : ℝ) ^ (((splitOdd A).2 : ℤ) * n.abs.toNat - ((splitOdd B).2 : ℤ) * n.abs.toNat))
          / ((splitOdd B).1.toNat : ℝ) ^ n.abs.toNat := by
      rw [hAdec, hBdec]
      push_cast
      have h2 : (2 : ℝ) ^ (((splitOdd A).2 : ℤ) * n.abs.toNat - ((splitOdd B).2 : ℤ) * n.abs.toNat)
          = (2 : ℝ) ^ ((splitOdd A).2 * n.abs.toNat)
            / (2 : ℝ) ^ ((splitOdd B).2 * n.abs.toNat) := by
        rw [zpow_sub₀ (by norm_num), ← zpow_natCast, ← zpow_natCast]
        push_cast
        rfl
      rw [h2, div_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      have hB'0 : ((splitOdd B).1.toNat : ℝ) ^ n.abs.toNat ≠ 0 := by positivity
      have h20 : (2 : ℝ) ^ ((splitOdd B).2 * n.abs.toNat) ≠ 0 := by positivity
      field_simp
    rw [hval, hvalue, divPrecRound_eq_liftVal₂, liftVal₂]
    cases neg with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, powSign, one_mul]
      rw [hnum, hden, Option.bind_some, Option.bind_some, Spec.div_coe_coe _ _ (by positivity)]
    | true =>
      simp only [↓reduceIte, powSign, neg_one_mul]
      rw [toVal_neg, hnum, Option.map_some, hden, Option.bind_some, Option.bind_some,
        ← EReal.coe_neg, Spec.div_coe_coe _ _ (by positivity)]
  · rw [dite_eq_right hc]
    dsimp only
    rw [← Real.rpow_intCast]
    exact zivLoopCertified_eq_threshold' p mode _ _
      (by
        rw [Real.rpow_intCast]
        exact not_mem_floatSet_ratPow_of_not_cheap p ha hb hcop hn (Bool.eq_false_iff.mpr hc)
          (abs_powSign _))
      _ (by unfold ratPowStart zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv, h1, h2, h3, h4, -⟩ :=
          ratPowApprox_spec neg (mkPosRat a b hb hcop) rfl ha (toVal_ofAzInt n) _
            (abs_toInt_lt_two_pow_size n) (w := w) (by unfold ratPowStart at hw; omega)
        rw [coe_toRat_eq_div_pos _ rfl] at h3 h4
        exact ⟨lv, hv, h1, h2, h3, h4⟩) _

/-! ### The main theorem -/

/-- **`q^y` is correctly rounded.** -/
theorem ratPowPrecRound_eq (q : AzRat) (y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ratPowPrecRound q y p mode
      = roundVal p mode (Spec.pow (some ((AzRat.toRat q : ℝ) : EReal)) y.toVal) := by
  have hp := NeZero.ne p
  have hden := den_pos_real q
  have h1iff := coe_toRat_eq_one_iff q
  cases y with
  | zero =>
    simp only [ratPowPrecRound, toVal_zero, Spec.pow_some_zero]
    rw [ite_eq_right hp, setPrecRound_one_eq]
  | nan =>
    simp only [ratPowPrecRound, toVal_nan]
    by_cases h1 : q.sign = true ∧ q.num = q.den
    · rw [ite_eq_left h1, ite_eq_right hp, setPrecRound_one_eq, h1iff.mpr h1, Spec.pow_one_left]
    · rw [ite_eq_right h1, Spec.pow_none_right (fun h => h1 (h1iff.mp (Option.some.inj h))),
        roundVal_none]
  | infinity sy =>
    simp only [ratPowPrecRound, toVal_infinity]
    set qv := (AzRat.toRat q : ℝ) with hqv
    have habs : |qv| = (q.num.toNat : ℝ) / q.den.toNat := abs_coe_toRat q
    by_cases h1 : q.num = q.den
    · rw [ite_eq_left h1, ite_eq_right hp, setPrecRound_one_eq]
      have habs1 : |qv| = 1 := by rw [habs, h1, div_self hden.ne']
      rcases abs_eq zero_le_one |>.mp habs1 with h | h
      · rw [h, EReal.coe_one, Spec.pow_one_left]
      · rw [h, Spec.pow_some_some (ereal_ite_ne_zero sy)
          (by rw [← EReal.coe_one, Ne, EReal.coe_eq_coe_iff]; norm_num)]
        cases sy
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [Spec.powVal_bot]
          simp [ereal_not_one_lt_neg_one]
        · simp only [↓reduceIte]
          rw [Spec.powVal_top]
          simp [ereal_not_one_lt_neg_one]
    · rw [ite_eq_right h1]
      have hne : |qv| ≠ 1 := by
        rw [habs]
        intro h
        rw [div_eq_one_iff_eq hden.ne'] at h
        exact h1 (AzNat.toNat_injective (by exact_mod_cast h))
      have hx1 : (qv : EReal) ≠ 1 := by
        intro h
        rw [← EReal.coe_one, EReal.coe_eq_coe_iff] at h
        exact hne (by rw [h, abs_one])
      rw [Spec.pow_some_some (ereal_ite_ne_zero sy) hx1]
      by_cases hgt : q.den < q.num
      · rw [ite_eq_left hgt]
        have hgt' : 1 < |qv| := by
          rw [habs, one_lt_div hden]
          exact_mod_cast (AzNat.lt_iff_toNat_lt _ _).mp hgt
        have hcase : (qv : EReal) < -1 ∨ 1 < (qv : EReal) := by
          rcases lt_abs.mp hgt' with h | h
          · right; exact_mod_cast h
          · left
            rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_lt_coe_iff]; linarith
        cases sy
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [Spec.powVal_bot, ite_eq_left hcase]; simp
        · simp only [↓reduceIte]
          rw [Spec.powVal_top, ite_eq_left hcase]; simp
      · rw [ite_eq_right hgt]
        have hle : q.num.toNat ≤ q.den.toNat := by
          have := (AzNat.lt_iff_toNat_lt q.den q.num).not.mp hgt
          omega
        have hlt : |qv| < 1 := by
          rw [habs, div_lt_one hden]
          have hne' : q.num.toNat ≠ q.den.toNat := fun h => h1 (AzNat.toNat_injective h)
          exact_mod_cast lt_of_le_of_ne hle hne'
        have hnot : ¬ ((qv : EReal) < -1 ∨ 1 < (qv : EReal)) := by
          rintro (h | h)
          · rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_lt_coe_iff] at h
            linarith [neg_abs_le qv]
          · rw [← EReal.coe_one, EReal.coe_lt_coe_iff] at h
            linarith [le_abs_self qv]
        have hin : -1 < (qv : EReal) ∧ (qv : EReal) < 1 := by
          obtain ⟨h1', h2'⟩ := abs_lt.mp hlt
          exact ⟨by rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_lt_coe_iff]; exact h1',
            by rw [← EReal.coe_one, EReal.coe_lt_coe_iff]; exact h2'⟩
        cases sy
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [Spec.powVal_bot, ite_eq_right hnot, ite_eq_left hin]; simp
        · simp only [↓reduceIte]
          rw [Spec.powVal_top, ite_eq_right hnot, ite_eq_left hin]; simp
  | finite sy ey qy my hvy =>
    set yv := finiteVal sy ey my with hyv
    have hy0 : yv ≠ 0 := finiteVal_ne_zero sy ey hvy
    have hy0' : ((yv : ℝ) : EReal) ≠ 0 := by rw [← EReal.coe_zero]; exact_mod_cast hy0
    have hsy : sy = true ↔ 0 < yv := by
      cases sy
      · simp only [Bool.false_eq_true, false_iff, not_lt]
        exact (finiteVal_false_neg ey hvy).le
      · simp only [true_iff]
        exact finiteVal_true_pos ey hvy
    set qv := (AzRat.toRat q : ℝ) with hqv
    simp only [ratPowPrecRound, toVal_finite]
    by_cases hq0 : q.num = 0
    · rw [dite_eq_left hq0]
      have habs0 : |qv| = 0 := by
        rw [hqv, abs_coe_toRat, hq0, AzNat.toNat_zero]; simp
      have hqv0 : qv = 0 := abs_eq_zero.mp habs0
      rw [hqv0, EReal.coe_zero, Spec.pow_some_some hy0' (by simp), Spec.powVal_coe]
      simp only [EReal.zero_ne_top, EReal.zero_ne_bot, ↓reduceIte]
      cases sy
      · have : ¬ 0 < yv := fun h => Bool.false_ne_true (hsy.mpr h)
        rw [ite_eq_right this]; simp
      · rw [ite_eq_left (hsy.mp rfl)]; simp
    · rw [dite_eq_right hq0, dite_eq_right hp]
      have hqne : qv ≠ 0 := by
        intro h
        have := abs_coe_toRat q
        rw [← hqv, h, abs_zero] at this
        have hnum : (q.num.toNat : ℝ) = 0 := by
          have := this.symm
          rwa [div_eq_zero_iff, or_iff_left hden.ne'] at this
        exact hq0 (AzNat.toNat_injective (by exact_mod_cast hnum))
      by_cases h1 : q.sign = true ∧ q.num = q.den
      · rw [ite_eq_left h1, setPrecRound_one_eq, h1iff.mpr h1, Spec.pow_one_left]
      · rw [ite_eq_right h1]
        have hx1 : (qv : EReal) ≠ 1 := fun h => h1 (h1iff.mp h)
        rw [Spec.pow_some_some hy0' hx1, Spec.powVal_coe, ite_eq_right (EReal.coe_ne_top _),
          ite_eq_right (EReal.coe_ne_bot _),
          ite_eq_right (by rw [← EReal.coe_zero]; exact_mod_cast hqne),
          EReal.toReal_coe]
        have hxpos : (0 : EReal) < (qv : EReal) ↔ 0 < qv := by
          rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]
        by_cases hi : isInteger (finite sy ey qy my hvy) = true
        · rw [dite_eq_left hi, ratPowIntOrZiv_eq]
          have ht := truncToAzInt_of_isInteger sy ey hvy hi
          rw [← hyv] at ht
          rw [ite_eq_left (Or.inr ⟨_, ht.symm⟩), ← ht, Real.rpow_intCast, hqv,
            coe_toRat_zpow_eq_sign_mul]
        · rw [dite_eq_right hi]
          have hni : ¬ ∃ n : ℤ, yv = n := fun h => hi ((isInteger_finite sy ey hvy).mpr h)
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
                (abs_finiteVal_bounds sy ey hvy).2 (finiteVal_ne_zero sy ey hvy)
                (finiteVal_sign_iff sy ey hvy) hgt hT
            split
            · rename_i u v N hex
              have h := ratPowExact?_some hq0 q.den_nz
                ((AzNat.coprime_iff _ _).mp q.reduced) sy ey hvy (Bool.eq_false_iff.mpr hi) hex
              rw [ratPowIntOrZiv_eq, ← h.2.2.2.2, ← hqdiv]
              simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul]
              rw [← hyv]
            · rename_i hex
              exact zivLoopCertified_eq_threshold' p mode _ _
                (by
                  have := not_mem_floatSet_of_irrational p
                    (irrational_of_ratPowExact?_none hq0 q.den_nz
                      ((AzNat.coprime_iff _ _).mp q.reduced) sy ey hvy
                      (Bool.eq_false_iff.mpr hi) hex)
                  rwa [← hqdiv, ← hyv] at this)
                _ (by unfold ratPowStart zivGuardBits; omega)
                (fun w hw => by
                  obtain ⟨lv, hv, h1', h2', h3', h4', -⟩ :=
                    ratPowApprox_spec false q hs hq0 (toVal_finite sy ey qy my hvy) ey
                      (abs_finiteVal_bounds sy ey hvy).2 (w := w)
                      (by unfold ratPowStart at hw; omega)
                  simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul] at h3' h4'
                  rw [← hqv, ← hyv] at h3' h4'
                  exact ⟨lv, hv, h1', h2', h3', h4'⟩) _

end Azurite.AzFloat
