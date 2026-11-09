/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pow
import Azurite.AzFloat.Equiv.PowInt

/-!
# Equivalence: `x^y`

`Spec.pow a b` is the specification value of `x^y` on `Option EReal` (`none` is `NaN`): `x^0 = 1`
and `1^y = 1` even for `NaN`, otherwise `NaN` propagates and `Spec.powVal` follows IEEE 754 for
the infinities, `0^y`, the sign of `y` and the integrality of `y` for `(−∞)^y`, the real power
`a^b` for `a > 0` or an integer `b`, and `NaN` for a negative `a` and a non-integer `b`.
`powPrecRound_eq : powPrecRound x y p mode = roundVal p mode (Spec.pow x.toVal y.toVal)` for
`p ≠ 0`: `x^y` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `a^b` for `b ≠ 0`, `a ≠ 1`, neither `NaN`. -/
noncomputable def powVal (a b : EReal) : Option EReal :=
  if b = ⊤ then (if a < -1 ∨ 1 < a then some ⊤ else if -1 < a ∧ a < 1 then some 0 else some 1)
  else if b = ⊥ then (if a < -1 ∨ 1 < a then some 0 else if -1 < a ∧ a < 1 then some ⊤ else some 1)
  else if a = ⊤ then (if 0 < b then some ⊤ else some 0)
  else if a = ⊥ then
    (if 0 < b then (if ∃ n : ℤ, Odd n ∧ b = ((n : ℝ) : EReal) then some ⊥ else some ⊤) else some 0)
  else if a = 0 then (if 0 < b then some 0 else some ⊤)
  else if 0 < a ∨ ∃ n : ℤ, b = ((n : ℝ) : EReal) then some ((a.toReal ^ b.toReal : ℝ) : EReal)
  else none

open Classical in
/-- The specification of `x^y`: `x^0 = 1` and `1^y = 1` for every `x`, `y`, even `NaN`;
otherwise `NaN` propagates and `powVal` applies. -/
noncomputable def pow (a b : Option EReal) : Option EReal :=
  if b = some 0 then some 1
  else if a = some 1 then some 1
  else match a, b with
    | some a, some b => powVal a b
    | _, _ => none

theorem pow_some_zero (a : Option EReal) : pow a (some 0) = some 1 := by
  unfold pow; rw [ite_eq_left rfl]

theorem pow_one_left (b : Option EReal) : pow (some 1) b = some 1 := by
  unfold pow; by_cases hb : b = some 0 <;> simp [hb]

theorem pow_none_right {a : Option EReal} (ha : a ≠ some 1) : pow a none = none := by
  unfold pow
  rw [ite_eq_right (by simp), ite_eq_right ha]
  try (cases a <;> rfl)

theorem pow_none_left {b : Option EReal} (hb : b ≠ some 0) : pow none b = none := by
  unfold pow
  rw [ite_eq_right hb, ite_eq_right (by simp)]

theorem pow_some_some {a b : EReal} (hb : b ≠ 0) (ha : a ≠ 1) :
    pow (some a) (some b) = powVal a b := by
  unfold pow
  rw [ite_eq_right (by simpa using hb), ite_eq_right (by simpa using ha)]

theorem powVal_top (a : EReal) :
    powVal a ⊤ = if a < -1 ∨ 1 < a then some ⊤ else if -1 < a ∧ a < 1 then some 0 else some 1 := by
  unfold powVal; rw [ite_eq_left rfl]

theorem powVal_bot (a : EReal) :
    powVal a ⊥ = if a < -1 ∨ 1 < a then some 0 else if -1 < a ∧ a < 1 then some ⊤ else some 1 := by
  unfold powVal; rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

open Classical in
theorem powVal_coe (a : EReal) (r : ℝ) :
    powVal a (r : EReal)
      = if a = ⊤ then (if 0 < r then some ⊤ else some 0)
        else if a = ⊥ then
          (if 0 < r then (if ∃ n : ℤ, Odd n ∧ r = n then some ⊥ else some ⊤) else some 0)
        else if a = 0 then (if 0 < r then some 0 else some ⊤)
        else if 0 < a ∨ ∃ n : ℤ, r = n then some ((a.toReal ^ r : ℝ) : EReal)
        else none := by
  unfold powVal
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]
  have h0 : (0 : EReal) < (r : EReal) ↔ 0 < r := by rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]
  have hn : (∃ n : ℤ, Odd n ∧ (r : EReal) = ((n : ℝ) : EReal)) ↔ ∃ n : ℤ, Odd n ∧ r = n := by
    constructor <;> rintro ⟨n, hn, h⟩ <;> exact ⟨n, hn, by exact_mod_cast h⟩
  have hn' : (∃ n : ℤ, (r : EReal) = ((n : ℝ) : EReal)) ↔ ∃ n : ℤ, r = n := by
    constructor <;> rintro ⟨n, h⟩ <;> exact ⟨n, by exact_mod_cast h⟩
  simp only [h0, hn, hn']

end Spec

/-! ### Numerals in `EReal` -/

theorem ereal_not_one_lt_zero : ¬ ((1 : EReal) < 0) := by
  rw [← EReal.coe_one, ← EReal.coe_zero, EReal.coe_lt_coe_iff]; norm_num

theorem ereal_not_zero_lt_neg_one : ¬ ((0 : EReal) < -1) := by
  rw [← EReal.coe_one, ← EReal.coe_neg, ← EReal.coe_zero, EReal.coe_lt_coe_iff]; norm_num

theorem ereal_neg_one_lt_zero : (-1 : EReal) < 0 := by
  rw [← EReal.coe_one, ← EReal.coe_neg, ← EReal.coe_zero, EReal.coe_lt_coe_iff]; norm_num

theorem ereal_zero_lt_one : (0 : EReal) < 1 := by
  rw [← EReal.coe_one, ← EReal.coe_zero, EReal.coe_lt_coe_iff]; norm_num

theorem ereal_bot_lt_neg_one : (⊥ : EReal) < -1 := by
  rw [← EReal.coe_one, ← EReal.coe_neg]; exact EReal.bot_lt_coe _

theorem ereal_one_lt_top : (1 : EReal) < ⊤ := by
  rw [← EReal.coe_one]; exact EReal.coe_lt_top _

theorem ereal_not_one_lt_neg_one : ¬ ((1 : EReal) < -1) := by
  rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_lt_coe_iff]; norm_num

theorem ereal_not_top_lt_neg_one : ¬ ((⊤ : EReal) < -1) := not_lt.mpr le_top

theorem ereal_not_one_lt_bot : ¬ ((1 : EReal) < ⊥) := not_lt.mpr bot_le

theorem ereal_bot_ne_one : (⊥ : EReal) ≠ 1 := by rw [← EReal.coe_one]; exact EReal.bot_ne_coe 1

theorem ereal_top_ne_one : (⊤ : EReal) ≠ 1 := by rw [← EReal.coe_one]; exact EReal.top_ne_coe 1

theorem ereal_bot_ne_zero : (⊥ : EReal) ≠ 0 := EReal.bot_ne_zero

theorem ereal_top_ne_zero : (⊤ : EReal) ≠ 0 := EReal.top_ne_zero

theorem ereal_ite_ne_zero (b : Bool) : (if b then (⊤ : EReal) else ⊥) ≠ 0 := by
  cases b
  · exact ereal_bot_ne_zero
  · exact ereal_top_ne_zero

theorem ereal_ite_ne_one (b : Bool) : (if b then (⊤ : EReal) else ⊥) ≠ 1 := by
  cases b
  · exact ereal_bot_ne_one
  · exact ereal_top_ne_one

namespace Spec

end Spec

/-! ### Helpers -/

theorem eqIEEE_one_iff (x : AzFloat) : eqIEEE x one = true ↔ x.toVal = some 1 := by
  rw [eqIEEE_iff, toVal_one', EReal.coe_one]
  constructor
  · rintro ⟨v, hx, hv⟩; rw [hx, ← Option.some.inj hv]
  · intro h; exact ⟨1, h, rfl⟩

/-- `|x| = 1` for a finite float. -/
theorem eqIEEE_abs_one_iff (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    eqIEEE (finite s e q m hv).abs one = true ↔ |finiteVal s e m| = 1 := by
  rw [eqIEEE_iff, toVal_one', toVal_abs, toVal_finite, Option.map_some]
  have hmax : max (finiteVal s e m : EReal) (-(finiteVal s e m : EReal))
      = ((|finiteVal s e m| : ℝ) : EReal) := by
    rw [← EReal.coe_neg, ← EReal.coe_strictMono.monotone.map_max, abs_eq_max_neg]
  rw [hmax]
  constructor
  · rintro ⟨v, h1, h2⟩
    rw [Option.some.injEq] at h1 h2
    exact EReal.coe_eq_coe_iff.mp (h1.trans h2.symm)
  · intro h
    exact ⟨_, rfl, by rw [h]⟩

theorem sign_true_iff (n : AzInt) : n.sign = true ↔ 0 ≤ n.toInt := by
  rw [show n.toInt = if n.sign then (n.abs.toNat : ℤ) else -(n.abs.toNat : ℤ) from rfl]
  cases h : n.sign
  · simp only [Bool.false_eq_true, ↓reduceIte, false_iff, not_le, Left.neg_neg_iff, Nat.cast_pos]
    rcases Nat.eq_zero_or_pos n.abs.toNat with h0 | h0
    · exfalso
      have hz : n.abs = 0 := AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])
      have := n.zero_sign hz
      rw [h] at this
      exact Bool.false_ne_true this
    · exact h0
  · simp

/-- `ex.sign && ex != 0` says `0 < ex`. -/
theorem sign_and_ne_zero_iff (n : AzInt) : (n.sign && n != 0) = true ↔ 0 < n.toInt := by
  rw [Bool.and_eq_true, sign_true_iff, bne_iff_ne]
  constructor
  · rintro ⟨h0, hne⟩
    exact lt_of_le_of_ne h0 (fun h => toInt_ne_zero_of_ne_zero hne h.symm)
  · intro h
    refine ⟨h.le, fun h0 => ?_⟩
    rw [h0, AzInt.toInt_zero] at h
    exact lt_irrefl _ h

/-- The value of a finite float of exponent `e`: `|x| < 1` for `e ≤ 0`, `|x| ≥ 1` for `e ≥ 1`. -/
theorem abs_finiteVal_lt_one_iff (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) : |finiteVal s e m| < 1 ↔ e.toInt ≤ 0 := by
  obtain ⟨h1, h2⟩ := abs_finiteVal_bounds s e hv
  constructor
  · intro h
    by_contra hpos
    push Not at hpos
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (e.toInt - 1) := one_le_zpow₀ (by norm_num) (by omega)
    linarith
  · intro h
    have : (2 : ℝ) ^ e.toInt ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) h
    linarith

theorem finiteVal_false_eq_neg (e : AzInt) (m : AzNat) :
    finiteVal false e m = -finiteVal true e m := by
  show (-1 : ℝ) * (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size)
    = -((1 : ℝ) * (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size))
  ring

theorem finiteVal_false_neg (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    finiteVal false e m < 0 := by
  rw [finiteVal_false_eq_neg]; linarith [finiteVal_true_pos e hv]

/-- `x^n = ± |x|^n` with the sign `(−1)^n` for a negative `x`. -/
theorem finiteVal_zpow_eq_sign_mul (s : Bool) (e : AzInt) (m : AzNat) (n : AzInt) :
    finiteVal s e m ^ n.toInt
      = powSign (!s && n.abs.isOdd) * finiteVal true e m ^ n.toInt := by
  cases s with
  | true => simp [powSign]
  | false =>
    rw [finiteVal_false_eq_neg, neg_eq_neg_one_mul, mul_zpow]
    simp only [Bool.not_false, Bool.true_and, powSign]
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

/-- `isInteger y && odd (trunc y)` says `y` is an odd integer. -/
theorem isInteger_and_odd_iff (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    (isInteger (finite s e q m hv) && (truncToAzInt (finite s e q m hv)).abs.isOdd) = true
      ↔ ∃ n : ℤ, Odd n ∧ finiteVal s e m = n := by
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hi, ho⟩
    have ht := truncToAzInt_of_isInteger s e hv hi
    refine ⟨(truncToAzInt (finite s e q m hv)).toInt, ?_, ht.symm⟩
    rwa [abs_isOdd_iff, toNat_abs_eq_natAbs, Int.natAbs_odd] at ho
  · rintro ⟨n, hodd, hn⟩
    have hi : isInteger (finite s e q m hv) = true := (isInteger_finite s e hv).mpr ⟨n, hn⟩
    refine ⟨hi, ?_⟩
    have ht := truncToAzInt_of_isInteger s e hv hi
    rw [hn] at ht
    have : (truncToAzInt (finite s e q m hv)).toInt = n := by exact_mod_cast ht
    rw [abs_isOdd_iff, toNat_abs_eq_natAbs, Int.natAbs_odd, this]
    exact hodd

/-! ### The integer-power path -/

/-- `powIntOrZiv` is the correctly rounded `x^n`. -/
theorem powIntOrZiv_eq (sx : Bool) (ex : AzInt) (qx : ℕ) (mx : AzNat) (hvx : FiniteValid qx mx)
    {n : AzInt} (hn : n ≠ 0) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    powIntOrZiv sx ex qx mx hvx n hn p mode
      = roundVal p mode (some ((finiteVal sx ex mx ^ n.toInt : ℝ) : EReal)) := by
  unfold powIntOrZiv
  split_ifs with hc
  · rw [powIntPrecRound_eq_liftVal, liftVal, toVal_finite, Option.bind_some, Spec.powInt_coe,
      ite_eq_right (toInt_ne_zero_of_ne_zero hn),
      ite_eq_right (fun h => finiteVal_ne_zero sx ex hvx h.1)]
  · dsimp only
    rw [finiteVal_zpow_eq_sign_mul, ← Real.rpow_intCast]
    exact zivLoopCertified_eq_threshold' p mode _ _
      (by
        rw [Real.rpow_intCast]
        exact not_mem_floatSet_of_not_cheap p ex hvx hn (Bool.eq_false_iff.mpr hc)
          (abs_powSign _))
      _ (by unfold powStart zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv, h1, h2, h3, h4, -⟩ :=
          powApprox_spec _ ex hvx (toVal_ofAzInt n) _ (abs_toInt_lt_two_pow_size n) (w := w)
            (by unfold powStart at hw; omega)
        exact ⟨lv, hv, h1, h2, h3, h4⟩) _

/-- `natPowOrZiv r n` is the correctly rounded `r^n` for `r ≥ 1`. -/
theorem natPowOrZiv_eq {r : AzNat} (hr : r ≠ 0) (n : AzInt) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    natPowOrZiv r n p mode = roundVal p mode (some (((r.toNat : ℝ) ^ n.toInt : ℝ) : EReal)) := by
  unfold natPowOrZiv
  split_ifs with hn
  · rw [hn, AzInt.toInt_zero, zpow_zero, setPrecRound_one_eq, EReal.coe_one]
  · have hpos : (0 : ℝ) < r.toNat := by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun h => hr (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero])))
    obtain ⟨ez, qz, mz, hvz, heq, hval⟩ := eq_finite_true_of_toVal_pos (toVal_ofAzNat r) hpos
    rw [heq]
    simp only []
    rw [powIntOrZiv_eq, hval]

/-! ### The main theorem -/

/-- **`x^y` is correctly rounded.** -/
theorem powPrecRound_eq (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    powPrecRound x y p mode = roundVal p mode (Spec.pow x.toVal y.toVal) := by
  have hp := NeZero.ne p
  cases y with
  | zero =>
    simp only [powPrecRound, toVal_zero, Spec.pow_some_zero]
    rw [ite_eq_right hp, setPrecRound_one_eq]
  | nan =>
    simp only [powPrecRound, toVal_nan]
    by_cases h1 : eqIEEE x one = true
    · rw [ite_eq_left h1, ite_eq_right hp, setPrecRound_one_eq, (eqIEEE_one_iff x).mp h1,
        Spec.pow_one_left]
    · rw [ite_eq_right h1, Spec.pow_none_right (fun h => h1 ((eqIEEE_one_iff x).mpr h)),
        roundVal_none]
  | infinity sy =>
    cases x with
    | nan =>
      simp only [powPrecRound, toVal_nan]
      rw [Spec.pow_none_left
        (by rw [toVal_infinity]; exact fun h => ereal_ite_ne_zero sy (Option.some.inj h))]
      rfl
    | zero =>
      simp only [powPrecRound, toVal_zero, toVal_infinity]
      rw [Spec.pow_some_some (ereal_ite_ne_zero sy)
        (by simp)]
      cases sy
      · simp [Spec.powVal_bot, ereal_not_one_lt_zero]
      · simp [Spec.powVal_top, ereal_not_one_lt_zero]
    | infinity sx =>
      simp only [powPrecRound, toVal_infinity]
      rw [Spec.pow_some_some (ereal_ite_ne_zero sy)
        (ereal_ite_ne_one sx)]
      cases sy <;> cases sx <;> simp [Spec.powVal_bot, Spec.powVal_top, ereal_bot_lt_neg_one,
        ereal_one_lt_top]
    | finite sx ex qx mx hvx =>
      simp only [powPrecRound, toVal_finite, toVal_infinity]
      set xv := finiteVal sx ex mx with hxv
      by_cases h1 : eqIEEE (finite sx ex qx mx hvx).abs one = true
      · rw [ite_eq_left h1, ite_eq_right hp, setPrecRound_one_eq]
        have habs := (eqIEEE_abs_one_iff sx ex hvx).mp h1
        rw [← hxv] at habs
        rcases abs_eq (zero_le_one) |>.mp habs with h | h
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
        have hne : |xv| ≠ 1 :=
          fun h => h1 ((eqIEEE_abs_one_iff sx ex hvx).mpr (by rw [← hxv]; exact h))
        have hx1 : (xv : EReal) ≠ 1 := by
          intro h
          rw [← EReal.coe_one, EReal.coe_eq_coe_iff] at h
          exact hne (by rw [h, abs_one])
        rw [Spec.pow_some_some (ereal_ite_ne_zero sy) hx1]
        by_cases hpos : (ex.sign && ex != 0) = true
        · rw [ite_eq_left hpos]
          have hgt : 1 < |xv| := by
            have h0 := (sign_and_ne_zero_iff ex).mp hpos
            have := (abs_finiteVal_lt_one_iff sx ex hvx).not.mpr (by omega)
            rw [← hxv] at this
            exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hne)
          have hcase : (xv : EReal) < -1 ∨ 1 < (xv : EReal) := by
            rcases lt_abs.mp hgt with h | h
            · right; exact_mod_cast h
            · left
              rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_lt_coe_iff]; linarith
          cases sy
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [Spec.powVal_bot, ite_eq_left hcase]; simp
          · simp only [↓reduceIte]
            rw [Spec.powVal_top, ite_eq_left hcase]; simp
        · rw [ite_eq_right hpos]
          have hlt : |xv| < 1 := by
            have h0 : ¬ 0 < ex.toInt := fun h => hpos ((sign_and_ne_zero_iff ex).mpr h)
            have := (abs_finiteVal_lt_one_iff sx ex hvx).mpr (by omega)
            rwa [← hxv] at this
          have hnot : ¬ ((xv : EReal) < -1 ∨ 1 < (xv : EReal)) := by
            rintro (h | h)
            · rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_lt_coe_iff] at h
              linarith [neg_abs_le xv]
            · rw [← EReal.coe_one, EReal.coe_lt_coe_iff] at h
              linarith [le_abs_self xv]
          have hin : -1 < (xv : EReal) ∧ (xv : EReal) < 1 := by
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
    have hyb : ((yv : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
    have hyt : ((yv : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    have hsy : sy = true ↔ 0 < yv := by
      cases sy
      · simp only [Bool.false_eq_true, false_iff, not_lt]
        exact (finiteVal_false_neg ey hvy).le
      · simp only [true_iff]
        exact finiteVal_true_pos ey hvy
    cases x with
    | nan =>
      simp only [powPrecRound, toVal_nan, toVal_finite]
      rw [Spec.pow_none_left (by simpa using hy0'), roundVal_none]
    | zero =>
      simp only [powPrecRound, toVal_zero, toVal_finite]
      rw [Spec.pow_some_some hy0' (by simp), Spec.powVal_coe]
      simp only [EReal.zero_ne_top, EReal.zero_ne_bot, ↓reduceIte]
      cases sy
      · have : ¬ 0 < yv := fun h => Bool.false_ne_true (hsy.mpr h)
        rw [ite_eq_right this]; simp
      · rw [ite_eq_left (hsy.mp rfl)]; simp
    | infinity sx =>
      simp only [powPrecRound, toVal_infinity, toVal_finite]
      rw [Spec.pow_some_some hy0' (ereal_ite_ne_one sx),
        Spec.powVal_coe]
      cases sx
      · simp only [Bool.false_eq_true, ↓reduceIte, bot_ne_top]
        cases sy
        · have : ¬ 0 < yv := fun h => Bool.false_ne_true (hsy.mpr h)
          simp only [Bool.false_eq_true, ↓reduceIte, this]
          simp
        · have hpos : 0 < yv := hsy.mp rfl
          simp only [↓reduceIte, hpos]
          by_cases hodd : (isInteger (finite true ey qy my hvy)
              && (truncToAzInt (finite true ey qy my hvy)).abs.isOdd) = true
          · rw [ite_eq_left hodd, ite_eq_left ((isInteger_and_odd_iff true ey hvy).mp hodd)]; simp
          · rw [ite_eq_right hodd,
              ite_eq_right (fun h => hodd ((isInteger_and_odd_iff true ey hvy).mpr h))]
            simp
      · simp only [↓reduceIte]
        cases sy
        · have : ¬ 0 < yv := fun h => Bool.false_ne_true (hsy.mpr h)
          simp only [Bool.false_eq_true, ↓reduceIte, this]
          simp
        · have hpos : 0 < yv := hsy.mp rfl
          simp only [↓reduceIte, hpos]
          simp
    | finite sx ex qx mx hvx =>
      set xv := finiteVal sx ex mx with hxv
      have hx0 : xv ≠ 0 := finiteVal_ne_zero sx ex hvx
      simp only [powPrecRound, toVal_finite]
      rw [dite_eq_right hp]
      by_cases h1 : eqIEEE (finite sx ex qx mx hvx) one = true
      · rw [ite_eq_left h1, setPrecRound_one_eq]
        have := (eqIEEE_one_iff _).mp h1
        rw [toVal_finite, ← hxv] at this
        rw [this, Spec.pow_one_left]
      · rw [ite_eq_right h1]
        have hx1 : ((xv : ℝ) : EReal) ≠ 1 :=
          fun h => h1 ((eqIEEE_one_iff _).mpr (by rw [toVal_finite, ← hxv, h]))
        rw [Spec.pow_some_some hy0' hx1, Spec.powVal_coe, ite_eq_right (EReal.coe_ne_top _),
          ite_eq_right (EReal.coe_ne_bot _),
          ite_eq_right (by rw [← EReal.coe_zero]; exact_mod_cast hx0),
          EReal.toReal_coe]
        have hxpos : (0 : EReal) < (xv : EReal) ↔ 0 < xv := by
          rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]
        by_cases hi : isInteger (finite sy ey qy my hvy) = true
        · rw [dite_eq_left hi, powIntOrZiv_eq]
          have ht := truncToAzInt_of_isInteger sy ey hvy hi
          rw [← hyv] at ht
          rw [ite_eq_left (Or.inr ⟨_, ht.symm⟩), ← ht, Real.rpow_intCast]
        · rw [dite_eq_right hi]
          have hni : ¬ ∃ n : ℤ, yv = n := fun h => hi ((isInteger_finite sy ey hvy).mpr h)
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
            · rename_i z N hex
              obtain ⟨zv, hzv, hzpos, hval, hN0⟩ :=
                powExact?_some ex hvx sy ey hvy (Bool.eq_false_iff.mpr hi) hex
              obtain ⟨ez, qz, mz, hvz, rfl, hzval⟩ := eq_finite_true_of_toVal_pos hzv hzpos
              simp only []
              rw [dite_eq_right (fun h => hN0 (by rw [h, AzInt.toInt_zero])), powIntOrZiv_eq, hzval,
                ← hval]
            · rename_i hex
              exact zivLoopCertified_eq_threshold' p mode _ _
                (by
                  have := not_mem_floatSet_of_irrational p
                    (irrational_of_powExact?_none ex hvx sy ey hvy (Bool.eq_false_iff.mpr hi)
                      hex)
                  rwa [← hxv, ← hyv] at this)
                _ (by unfold powStart zivGuardBits; omega)
                (fun w hw => by
                  obtain ⟨lv, hv, h1', h2', h3', h4', -⟩ :=
                    powApprox_spec false ex hvx (toVal_finite sy ey qy my hvy) ey
                      (abs_finiteVal_bounds sy ey hvy).2 (w := w) (by unfold powStart at hw; omega)
                  simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul] at h3' h4'
                  exact ⟨lv, hv, h1', h2', h3', h4'⟩) _

end Azurite.AzFloat
