/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp2Bracket
import Azurite.AzFloat.Equiv.ExpApprox
import Azurite.AzFloat.Equiv.RoundToInteger
import Azurite.AzFloat.Equiv.LogBaseFloatBracket
import Azurite.AzRat.Equiv.Unary

/-!
# Equivalence: the brackets of `2^x` and `2^q`

`ln2MulBracket_spec` (an enclosure of `x ln 2` of width at most `2^(−w)`), `exp2Bracket_spec`
(width `exp2Eps x w`, `tendsto_exp2Eps`), the irrationality of `2^x` for a dyadic non-integer `x`
(`irrational_two_rpow_of_dyadic`: `2^x = 2^⌊x⌋ · 2^f` with `(2^f)^(2^J)` an integer and
`1 < 2^f < 2`, by `irrational_nrt_of_notint_nrt`), `exp2Approx_spec` and the Ziv certificate
`exp2Approx_isSome_exists`; the rational versions `ln2MulRatBracket_spec`, `exp2RatBracket_spec`,
`irrational_two_rpow_toRat`, `exp2RatApprox_spec`, `exp2RatApprox_isSome_exists`.
-/

namespace Azurite.AzFloat

/-! ### Irrationality -/

/-- `2^x` is irrational for a rational `x = N / D` that is not an integer. -/
theorem irrational_two_rpow_of_rat {xv : ℝ} {N : ℤ} {D : ℕ} (hD : 0 < D) (hd : xv * D = N)
    (hni : ¬ ∃ n : ℤ, xv = n) : Irrational ((2 : ℝ) ^ xv) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hxv : xv = (N : ℝ) / (D : ℝ) := by
    rw [eq_div_iff hDr.ne']
    exact hd
  have hf0 : 0 ≤ Int.fract xv := Int.fract_nonneg xv
  have hf1 : Int.fract xv < 1 := Int.fract_lt_one xv
  have hfne : Int.fract xv ≠ 0 := by
    intro h0
    apply hni
    refine ⟨⌊xv⌋, ?_⟩
    have := Int.fract_add_floor xv
    rw [h0, zero_add] at this
    exact this.symm
  have hfpos : 0 < Int.fract xv := lt_of_le_of_ne hf0 (Ne.symm hfne)
  have hfrac : Int.fract xv = ((N % D : ℤ) : ℝ) / (D : ℝ) := by
    rw [hxv, Int.fract_div_intCast_eq_div_intCast_mod]
  have hm0 : 0 ≤ N % D := Int.emod_nonneg _ (by exact_mod_cast hD.ne')
  have hy1 : 1 < (2 : ℝ) ^ Int.fract xv := Real.one_lt_rpow (by norm_num) hfpos
  have hy2 : (2 : ℝ) ^ Int.fract xv < 2 := by
    have := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hf1
    rwa [Real.rpow_one] at this
  have hmt : ((N % D : ℤ) : ℝ) = (((N % D).toNat : ℕ) : ℝ) := by
    have := Int.toNat_of_nonneg hm0
    exact_mod_cast this.symm
  have hyn : ((2 : ℝ) ^ Int.fract xv) ^ D = ((2 ^ (N % D).toNat : ℤ) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hfrac]
    have e1 : ((N % D : ℤ) : ℝ) / (D : ℝ) * (D : ℝ) = ((N % D : ℤ) : ℝ) := by
      field_simp
    rw [e1, hmt, Real.rpow_natCast]
    push_cast
    ring
  have hirr : Irrational ((2 : ℝ) ^ Int.fract xv) := by
    refine irrational_nrt_of_notint_nrt D (2 ^ (N % D).toNat) hyn ?_ hD
    rintro ⟨z, hz⟩
    rw [hz] at hy1 hy2
    have h1 : (1 : ℤ) < z := by exact_mod_cast hy1
    have h2 : z < 2 := by exact_mod_cast hy2
    omega
  have hsplit : (2 : ℝ) ^ xv = (((2 : ℚ) ^ ⌊xv⌋ : ℚ) : ℝ) * (2 : ℝ) ^ Int.fract xv := by
    conv_lhs => rw [← Int.floor_add_fract xv]
    rw [Real.rpow_add (by norm_num), Real.rpow_intCast, Rat.cast_zpow, Rat.cast_ofNat]
  rw [hsplit]
  exact hirr.ratCast_mul (zpow_ne_zero _ (by norm_num))

/-- `2^x` is irrational for a dyadic rational `x = N / 2^J` that is not an integer. -/
theorem irrational_two_rpow_of_dyadic {xv : ℝ} {N : ℤ} {J : ℕ} (hd : xv * 2 ^ J = N)
    (hni : ¬ ∃ n : ℤ, xv = n) : Irrational ((2 : ℝ) ^ xv) :=
  irrational_two_rpow_of_rat (D := 2 ^ J) (by positivity) (by push_cast; exact hd) hni

/-- A finite float is a dyadic rational: `x · 2^J` is an integer for some `J`. -/
theorem exists_dyadic_of_finiteVal (s : Bool) (e : AzInt) (m : AzNat) :
    ∃ (N : ℤ) (J : ℕ), finiteVal s e m * 2 ^ J = N := by
  refine ⟨(if s then 1 else -1) * m.toNat * 2 ^ (e.toInt + e.abs.toNat).toNat,
    m.size + e.abs.toNat, ?_⟩
  have hnn : 0 ≤ e.toInt + e.abs.toNat := by
    have := AzInt.abs_toNat_eq e
    rw [this]
    linarith [neg_abs_le e.toInt]
  have hcast : ((e.toInt + e.abs.toNat).toNat : ℤ) = e.toInt + e.abs.toNat :=
    Int.toNat_of_nonneg hnn
  have hz : (2 : ℝ) ^ (e.toInt - m.size) * (2 : ℝ) ^ (m.size + e.abs.toNat : ℕ)
      = (2 : ℝ) ^ ((e.toInt + e.abs.toNat).toNat : ℕ) := by
    rw [← zpow_natCast (2 : ℝ) (m.size + e.abs.toNat), ← zpow_natCast (2 : ℝ),
      ← zpow_add₀ (by norm_num), hcast]
    congr 1
    push_cast
    ring
  unfold finiteVal
  push_cast
  rw [← hz]
  ring

/-! ### The bracket of `x ln 2` -/

/-- `ln2MulBracket x e w` encloses `x ln 2` with width at most `2^(−w)`, for `|x| < 2^e`. -/
theorem ln2MulBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (e : AzInt)
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (w : ℕ) (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (ln2MulBracket x e w).1.toVal = some (lo : EReal) ∧
      (ln2MulBracket x e w).2.toVal = some (hi : EReal) ∧
      lo ≤ xv * Real.log 2 ∧ xv * Real.log 2 ≤ hi ∧ hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  -- the working precision and the scale (as in `expReduce_spec`)
  obtain ⟨emax, hemax⟩ : ∃ n : ℕ, n = if e.sign then e.abs.toNat else 0 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = expWork e w := ⟨_, rfl⟩
  have hWv : W = w + 16 + emax := by rw [hW, hemax]; rfl
  have hemaxZ : e.toInt ≤ (emax : ℤ) := by
    rw [hemax]
    split_ifs with hs
    · rw [AzInt.abs_toNat_eq e, abs_of_nonneg ((AzInt.sign_eq_true_iff e).mp hs)]
    · have := (AzInt.sign_eq_true_iff e).not.mp hs
      push Not at this
      push_cast
      exact this.le
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ emax := ⟨_, rfl⟩
  have hxE : |xv| < E := by
    calc |xv| < (2 : ℝ) ^ e.toInt := hxe
      _ ≤ (2 : ℝ) ^ (emax : ℤ) := zpow_le_zpow_right₀ (by norm_num) hemaxZ
      _ = E := by rw [hE, zpow_natCast]
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have : NeZero W := ⟨by omega⟩
  have hδ : (1 / 2 : ℝ) ^ W = u * (1 / 65536) * (1 / 2 : ℝ) ^ emax := by
    rw [hWv, pow_add, pow_add, hu, show ((1 : ℝ) / 2) ^ 16 = 1 / 65536 by norm_num]
  have hEu : E * (1 / 2 : ℝ) ^ emax = 1 := by
    rw [hE, one_div_pow, mul_one_div, div_self (by positivity)]
  have hhalf0 : 0 ≤ (1 / 2 : ℝ) ^ emax := by positivity
  have hX : |xv| * (1 / 2 : ℝ) ^ W ≤ u / 65536 := by
    rw [hδ]
    have : |xv| * (1 / 2 : ℝ) ^ emax ≤ E * (1 / 2 : ℝ) ^ emax :=
      mul_le_mul_of_nonneg_right hxE.le hhalf0
    rw [hEu] at this
    calc |xv| * (u * (1 / 65536) * (1 / 2 : ℝ) ^ emax)
        = u / 65536 * (|xv| * (1 / 2 : ℝ) ^ emax) := by ring
      _ ≤ u / 65536 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = u / 65536 := mul_one _
  have hδ0 : 0 ≤ (1 / 2 : ℝ) ^ W := by positivity
  -- the bracket of `ln 2` and the products with `|x|`
  obtain ⟨lv, hv', hlv, hhv, hl, hh, hwid, h5⟩ := ln2Bracket_spec W
  have hlv5 : 1 / 5 ≤ lv := h5 (by omega)
  have hW64 : (1 / 2 : ℝ) ^ W ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  have hln2lo := Real.log_two_gt_d9
  have hln2hi := Real.log_two_lt_d9
  have hlv0 : 0 ≤ lv := by linarith
  have hhv1 : hv' ≤ 1 := by linarith
  have hlv1 : lv ≤ 1 := by linarith
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hka0 : 0 ≤ |xv| := abs_nonneg _
  obtain ⟨plo, hplo, hplo1⟩ := mulFloor_err habs hlv W (mul_nonneg hka0 hlv0)
  obtain ⟨phi, hphi, hphi1⟩ := mulCeiling_err habs hhv W (mul_nonneg hka0 (by linarith))
  have hP1 : plo ≤ |xv| * Real.log 2 := hplo1.le.trans (mul_le_mul_of_nonneg_left hl hka0)
  have hP2 : |xv| * Real.log 2 ≤ phi := (mul_le_mul_of_nonneg_left hh hka0).trans hphi1.ge
  have hpwid : phi - plo ≤ u := by
    have h1 := hplo1.ge
    have h2 := hphi1.le
    have h3 : |xv| * (hv' - lv) ≤ |xv| * (8 * (1 / 2 : ℝ) ^ W) :=
      mul_le_mul_of_nonneg_left hwid hka0
    have h4 : 2 * (|xv| * hv') * (1 / 2 : ℝ) ^ W ≤ 2 * |xv| * (1 / 2 : ℝ) ^ W := by
      have : |xv| * hv' ≤ |xv| * 1 := mul_le_mul_of_nonneg_left hhv1 hka0
      have := mul_le_mul_of_nonneg_right this hδ0
      linarith
    have h5 : 2 * (|xv| * lv) * (1 / 2 : ℝ) ^ W ≤ 2 * |xv| * (1 / 2 : ℝ) ^ W := by
      have : |xv| * lv ≤ |xv| * 1 := mul_le_mul_of_nonneg_left hlv1 hka0
      have := mul_le_mul_of_nonneg_right this hδ0
      linarith
    nlinarith
  -- the sign of `x`
  simp only [ln2MulBracket, absLn2Bracket]
  rw [← hW]
  split_ifs with hneg
  · have hxneg : xv < 0 := (toVal_sign_of_isNegative hx).1 hneg
    have hax : |xv| = -xv := abs_of_neg hxneg
    have hnphi : (-(mulPrecRound x.abs (ln2Bracket W).2 W .Ceiling).1).toVal
        = some ((-phi : ℝ) : EReal) := by rw [toVal_neg, hphi, Option.map_some, EReal.coe_neg]
    have hnplo : (-(mulPrecRound x.abs (ln2Bracket W).1 W .Floor).1).toVal
        = some ((-plo : ℝ) : EReal) := by rw [toVal_neg, hplo, Option.map_some, EReal.coe_neg]
    refine ⟨-phi, -plo, hnphi, hnplo, ?_, ?_, ?_⟩
    · rw [hax] at hP2; linarith
    · rw [hax] at hP1; linarith
    · rw [hu] at hpwid; linarith
  · have hxpos : 0 ≤ xv := (toVal_sign_of_isNegative hx).2 (by simpa using hneg)
    have hax : |xv| = xv := abs_of_nonneg hxpos
    refine ⟨plo, phi, hplo, hphi, ?_, ?_, ?_⟩
    · rw [hax] at hP1; exact hP1
    · rw [hax] at hP2; exact hP2
    · rw [hu] at hpwid; exact hpwid

/-! ### The bracket of `2^x` -/

/-- The width bound of `exp2Bracket`. -/
noncomputable def exp2Eps (xv : ℝ) (w : ℕ) : ℝ :=
  expOfBracketEps (xv * Real.log 2) ((1 / 2 : ℝ) ^ w) w

theorem tendsto_exp2Eps (xv : ℝ) : Filter.Tendsto (exp2Eps xv) Filter.atTop (nhds 0) := by
  unfold exp2Eps expOfBracketEps
  have h1 := tendsto_expEps (xv * Real.log 2)
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 := ((hu.const_mul 24).add (hu.div_const 4)).const_mul (Real.exp (xv * Real.log 2))
  simp only [mul_zero, zero_div, add_zero] at h2
  have := h1.add h2
  rwa [add_zero] at this

/-- `2^x = exp (x ln 2)`. -/
theorem two_rpow_eq_exp (xv : ℝ) : (2 : ℝ) ^ xv = Real.exp (xv * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num), mul_comm]

/-- `exp2Bracket x e w` encloses `2^x` for a float `x` with `|x| < 2^e`, with width at most
`exp2Eps x w`. -/
theorem exp2Bracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (e : AzInt)
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (exp2Bracket x e w).1.toVal = some (lo : EReal) ∧
      (exp2Bracket x e w).2.toVal = some (hi : EReal) ∧
      lo ≤ (2 : ℝ) ^ xv ∧ (2 : ℝ) ^ xv ≤ hi ∧ hi - lo ≤ exp2Eps xv w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := ln2MulBracket_spec hx e hxe w hw
  have hw1 : hi - lo ≤ 1 := by
    have := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := w)
    linarith
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw
  rw [two_rpow_eq_exp]
  refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
  unfold exp2Eps
  refine hab.trans ?_
  unfold expOfBracketEps
  have := Real.exp_pos (xv * Real.log 2)
  nlinarith

/-- `exp2Approx` is a strict enclosure of `2^x` for a non-integer finite `x`, with width at
most `exp2Eps x w`. -/
theorem exp2Approx_spec {w : ℕ} (hw : 64 ≤ w) (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hni : ¬ isInteger (finite s e q m hv) = true) :
    ∃ lv hv' : ℝ, Rounds (exp2Approx (finite s e q m hv) e w).1 lv ∧
      Rounds (exp2Approx (finite s e q m hv) e w).2 hv' ∧
      lv < (2 : ℝ) ^ finiteVal s e m ∧ (2 : ℝ) ^ finiteVal s e m < hv' ∧
      hv' - lv ≤ exp2Eps (finiteVal s e m) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ :=
    exp2Bracket_spec (toVal_finite s e q m hv) e (abs_finiteVal_bounds s e hv).2 hw
  have hni' : ¬ ∃ n : ℤ, finiteVal s e m = n := fun h => hni ((isInteger_finite s e hv).mpr h)
  obtain ⟨N, J, hd⟩ := exists_dyadic_of_finiteVal s e m
  have hirr := irrational_two_rpow_of_dyadic hd hni'
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 hirr
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `2^x`. -/
theorem exp2Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (s : Bool) (e : AzInt)
    {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (hni : ¬ isInteger (finite s e q m hv) = true)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (exp2Approx (finite s e q m hv) e (w₀ * 2 ^ f)).1
      (exp2Approx (finite s e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  have hni' : ¬ ∃ n : ℤ, finiteVal s e m = n := fun h => hni ((isInteger_finite s e hv).mpr h)
  have hirr := irrational_two_rpow_of_dyadic
    (exists_dyadic_of_finiteVal s e m).choose_spec.choose_spec hni'
  exists_isSome_of_irrational_threshold p mode (exp2Approx (finite s e q m hv) e) hirr
    (exp2Eps (finiteVal s e m)) (tendsto_exp2Eps _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := exp2Approx_spec hw s e hv hni
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-! ### The bracket of `q ln 2` for a rational `q` -/

/-- A nonnegative-sign rational is nonnegative; a negative-sign one is negative. -/
theorem toRat_nonneg_of_sign (q : AzRat) (hs : q.sign = true) : 0 ≤ (AzRat.toRat q : ℝ) := by
  by_cases h0 : q.num = 0
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0]
  · exact_mod_cast (toRat_pos_of_sign q hs h0).le

theorem toRat_neg_of_sign' (q : AzRat) (hs : q.sign = false) : (AzRat.toRat q : ℝ) < 0 :=
  toRat_neg_of_sign q hs (fun h0 => by have := q.zero_sign h0; rw [this] at hs; cases hs)

/-- `ln2MulRatBracket q w` encloses `q ln 2` with width at most `2^(−w)`. -/
theorem ln2MulRatBracket_spec (q : AzRat) (w : ℕ) (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (ln2MulRatBracket q w).1.toVal = some (lo : EReal) ∧
      (ln2MulRatBracket q w).2.toVal = some (hi : EReal) ∧
      lo ≤ (AzRat.toRat q : ℝ) * Real.log 2 ∧ (AzRat.toRat q : ℝ) * Real.log 2 ≤ hi ∧
      hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = w + 16 + q.num.size := ⟨_, rfl⟩
  have : NeZero W := ⟨by omega⟩
  obtain ⟨qv, hqv⟩ : ∃ qv : ℝ, qv = (AzRat.toRat q : ℝ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hqs : |qv| < (2 : ℝ) ^ q.num.size := by
    have h := abs_toRat_lt q
    rw [zpow_natCast, ← hqv] at h
    exact h
  have hs0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ q.num.size := by positivity
  have hs1 : (2 : ℝ) ^ q.num.size * (1 / 2 : ℝ) ^ q.num.size = 1 := by
    rw [one_div_pow, mul_one_div, div_self (by positivity)]
  have hδ : (1 / 2 : ℝ) ^ W = u * (1 / 65536) * (1 / 2 : ℝ) ^ q.num.size := by
    rw [hW, pow_add, pow_add, hu, show ((1 : ℝ) / 2) ^ 16 = 1 / 65536 by norm_num]
  have hX : |qv| * (1 / 2 : ℝ) ^ W ≤ u / 65536 := by
    rw [hδ]
    have := mul_le_mul_of_nonneg_right hqs.le hs0
    rw [hs1] at this
    calc |qv| * (u * (1 / 65536) * (1 / 2 : ℝ) ^ q.num.size)
        = u / 65536 * (|qv| * (1 / 2 : ℝ) ^ q.num.size) := by ring
      _ ≤ u / 65536 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = u / 65536 := mul_one _
  have hδ0 : 0 ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hW64 : (1 / 2 : ℝ) ^ W ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  -- the bracket of `ln 2` and the floats around `|q|`
  obtain ⟨lv, hv', hlv, hhv, hl, hh, hwid, h5⟩ := ln2Bracket_spec W
  have hlv5 : 1 / 5 ≤ lv := h5 (by omega)
  have hln2lo := Real.log_two_gt_d9
  have hln2hi := Real.log_two_lt_d9
  have hlv0 : 0 ≤ lv := by linarith
  have hhv1 : hv' ≤ 1 := by linarith
  have hlv1 : lv ≤ 1 := by linarith
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |qv| := by
    rw [AzRat.toRat_abs, Rat.cast_abs, hqv]
  obtain ⟨a, ha, ha1, ha2⟩ := ofAzRatRound_floor_abs q.abs W
  obtain ⟨b, hb, hb1, hb2⟩ := ofAzRatRound_ceiling_abs q.abs W
  rw [habs] at ha1 ha2 hb1 hb2
  simp only [abs_abs] at ha2 hb2
  have hka0 : 0 ≤ |qv| := abs_nonneg _
  have ha0 : 0 ≤ a := by
    have : 2 * |qv| * (1 / 2 : ℝ) ^ W ≤ 2 * |qv| * (1 / 64) :=
      mul_le_mul_of_nonneg_left hW64 (by positivity)
    linarith
  have hb0 : 0 ≤ b := by linarith
  obtain ⟨plo, hplo, hplo1⟩ := mulFloor_err ha hlv W (mul_nonneg ha0 hlv0)
  obtain ⟨phi, hphi, hphi1⟩ := mulCeiling_err hb hhv W (mul_nonneg hb0 (by linarith))
  have hln0 : 0 < Real.log 2 := by linarith
  have hP1 : plo ≤ |qv| * Real.log 2 :=
    hplo1.le.trans (mul_le_mul ha1 hl hlv0 hka0)
  have hP2 : |qv| * Real.log 2 ≤ phi :=
    (mul_le_mul hb1 hh hln0.le hb0).trans hphi1.ge
  have hpwid : phi - plo ≤ u := by
    have h1 := hplo1.ge
    have h2 := hphi1.le
    have hb2' : b ≤ 2 * |qv| := by
      have : 2 * |qv| * (1 / 2 : ℝ) ^ W ≤ 2 * |qv| * (1 / 64) :=
        mul_le_mul_of_nonneg_left hW64 (by positivity)
      linarith
    have hba : b - a ≤ 4 * |qv| * (1 / 2 : ℝ) ^ W := by linarith
    -- `b hi − a lo = b (hi − lo) + (b − a) lo ≤ 16 |q| δ + 4 |q| δ`
    have h3 : b * (hv' - lv) ≤ 2 * |qv| * (8 * (1 / 2 : ℝ) ^ W) :=
      mul_le_mul hb2' hwid (by linarith) (by positivity)
    have h4 : (b - a) * lv ≤ 4 * |qv| * (1 / 2 : ℝ) ^ W * 1 :=
      mul_le_mul hba hlv1 hlv0 (by positivity)
    have h5' : 2 * (b * hv') * (1 / 2 : ℝ) ^ W ≤ 2 * (2 * |qv|) * (1 / 2 : ℝ) ^ W := by
      have : b * hv' ≤ 2 * |qv| * 1 := mul_le_mul hb2' hhv1 (by linarith) (by positivity)
      have := mul_le_mul_of_nonneg_right this hδ0
      linarith
    have h6 : 2 * (a * lv) * (1 / 2 : ℝ) ^ W ≤ 2 * (2 * |qv|) * (1 / 2 : ℝ) ^ W := by
      have : a * lv ≤ 2 * |qv| * 1 := mul_le_mul (by linarith) hlv1 hlv0 (by positivity)
      have := mul_le_mul_of_nonneg_right this hδ0
      linarith
    have hid : b * hv' - a * lv = b * (hv' - lv) + (b - a) * lv := by ring
    nlinarith
  -- the sign of `q`
  simp only [ln2MulRatBracket, absLn2RatBracket]
  rw [← hW, ← hqv]
  split_ifs with hs
  · have hq0 : 0 ≤ qv := by rw [hqv]; exact toRat_nonneg_of_sign q hs
    have hax : |qv| = qv := abs_of_nonneg hq0
    refine ⟨plo, phi, hplo, hphi, ?_, ?_, ?_⟩
    · rw [hax] at hP1; exact hP1
    · rw [hax] at hP2; exact hP2
    · rw [hu] at hpwid; exact hpwid
  · have hqneg : qv < 0 := by rw [hqv]; exact toRat_neg_of_sign' q (by simpa using hs)
    have hax : |qv| = -qv := abs_of_neg hqneg
    have hnphi : (-(mulPrecRound (ofAzRatRound q.abs W .Ceiling).1 (ln2Bracket W).2 W
        .Ceiling).1).toVal = some ((-phi : ℝ) : EReal) := by
      rw [toVal_neg, hphi, Option.map_some, EReal.coe_neg]
    have hnplo : (-(mulPrecRound (ofAzRatRound q.abs W .Floor).1 (ln2Bracket W).1 W
        .Floor).1).toVal = some ((-plo : ℝ) : EReal) := by
      rw [toVal_neg, hplo, Option.map_some, EReal.coe_neg]
    refine ⟨-phi, -plo, hnphi, hnplo, ?_, ?_, ?_⟩
    · rw [hax] at hP2; linarith
    · rw [hax] at hP1; linarith
    · rw [hu] at hpwid; linarith

/-- `exp2RatBracket q w` encloses `2^q` with width at most `exp2Eps q w`. -/
theorem exp2RatBracket_spec (q : AzRat) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (exp2RatBracket q w).1.toVal = some (lo : EReal) ∧
      (exp2RatBracket q w).2.toVal = some (hi : EReal) ∧
      lo ≤ (2 : ℝ) ^ (AzRat.toRat q : ℝ) ∧ (2 : ℝ) ^ (AzRat.toRat q : ℝ) ≤ hi ∧
      hi - lo ≤ exp2Eps (AzRat.toRat q : ℝ) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := ln2MulRatBracket_spec q w hw
  have hw1 : hi - lo ≤ 1 := by
    have := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := w)
    linarith
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw
  rw [two_rpow_eq_exp]
  refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
  unfold exp2Eps
  refine hab.trans ?_
  unfold expOfBracketEps
  have := Real.exp_pos ((AzRat.toRat q : ℝ) * Real.log 2)
  nlinarith

/-- `2^q` is irrational for a rational `q` that is not an integer (`den ≠ 1`). -/
theorem irrational_two_rpow_toRat (q : AzRat) (hd : q.den.toNat ≠ 1) :
    Irrational ((2 : ℝ) ^ (AzRat.toRat q : ℝ)) := by
  have hD : 0 < q.den.toNat := AzRat.den_toNat_pos q
  have hcast := AzRat.toRat_cast_eq q
  refine irrational_two_rpow_of_rat (N := if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ))
    (D := q.den.toNat) hD ?_ ?_
  · rw [hcast]
    have : (q.den.toNat : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
  · rintro ⟨n, hn⟩
    apply hd
    have hq : AzRat.toRat q = (n : ℚ) := by exact_mod_cast hn
    have := congrArg Rat.den hq
    rw [Rat.den_intCast] at this
    rw [← this]
    rfl

/-- `exp2RatApprox` is a strict enclosure of `2^q` for a non-integer rational `q`, with width at
most `exp2Eps q w`. -/
theorem exp2RatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (hd : q.den.toNat ≠ 1) :
    ∃ lv hv : ℝ, Rounds (exp2RatApprox q w).1 lv ∧ Rounds (exp2RatApprox q w).2 hv ∧
      lv < (2 : ℝ) ^ (AzRat.toRat q : ℝ) ∧ (2 : ℝ) ^ (AzRat.toRat q : ℝ) < hv ∧
      hv - lv ≤ exp2Eps (AzRat.toRat q : ℝ) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := exp2RatBracket_spec q hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 (irrational_two_rpow_toRat q hd)
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `2^q`. -/
theorem exp2RatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (hd : q.den.toNat ≠ 1) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (exp2RatApprox q (w₀ * 2 ^ f)).1 (exp2RatApprox q (w₀ * 2 ^ f)).2
      p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (exp2RatApprox q) (irrational_two_rpow_toRat q hd)
    (exp2Eps (AzRat.toRat q : ℝ)) (tendsto_exp2Eps _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := exp2RatApprox_spec hw q hd
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

end Azurite.AzFloat
