/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.ExpApprox
import Azurite.AzFloat.Equiv.LogBaseFloatBracket
import Azurite.AzFloat.Equiv.RoundToInteger
import Azurite.AzFloat.Pow2Bracket
import Azurite.AzRat.Equiv.Unary

/-!
# Equivalence: the brackets of `2^x`, `2^q`, `2^x − 1` and `2^q − 1`

`ln2MulBracket_spec` (an enclosure of `x ln 2` of width at most `2^(−w)`), `pow2Bracket_spec`
(width `pow2Eps x w`, `tendsto_exp2Eps`), the irrationality of `2^x` for a dyadic non-integer `x`
(`irrational_two_rpow_of_dyadic`: `2^x = 2^⌊x⌋ · 2^f` with `(2^f)^(2^J)` an integer and
`1 < 2^f < 2`, by `irrational_nrt_of_notint_nrt`), `pow2Approx_spec` and the Ziv certificate
`pow2Approx_isSome_exists`; the rational versions `ln2MulRatBracket_spec`, `pow2RatBracket_spec`,
`irrational_two_rpow_toRat`, `pow2RatApprox_spec`, `pow2RatApprox_isSome_exists`; and for
`2^x − 1`: `expM1OfBracket_width` (the real arithmetic), the generic
`expM1OfBracket_spec_of_bounds` (any bracket of width `δ ≤ 1/64` with `|lo| < 2^e`,
`|lo| ≤ 2|v|`), `expM1OfBracket_spec` (width `expM1RatEps (x ln 2) c w`), `pow2M1Bracket_spec`
(width `pow2M1Eps x c w`),
`irrational_two_rpow_sub_one_finiteVal`, `pow2M1Approx_spec`, `pow2M1Approx_isSome_exists`;
and for `2^q − 1`: `pow2M1RatExp_bounds`, `pow2M1RatBracket_spec`,
`irrational_two_rpow_sub_one_toRat`, `pow2M1RatApprox_spec`, `pow2M1RatApprox_isSome_exists`.
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

/-- The width bound of `pow2Bracket`. -/
noncomputable def pow2Eps (xv : ℝ) (w : ℕ) : ℝ :=
  expOfBracketEps (xv * Real.log 2) ((1 / 2 : ℝ) ^ w) w

theorem tendsto_exp2Eps (xv : ℝ) : Filter.Tendsto (pow2Eps xv) Filter.atTop (nhds 0) := by
  unfold pow2Eps expOfBracketEps
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

/-- `pow2Bracket x e w` encloses `2^x` for a float `x` with `|x| < 2^e`, with width at most
`pow2Eps x w`. -/
theorem pow2Bracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (e : AzInt)
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (pow2Bracket x e w).1.toVal = some (lo : EReal) ∧
      (pow2Bracket x e w).2.toVal = some (hi : EReal) ∧
      lo ≤ (2 : ℝ) ^ xv ∧ (2 : ℝ) ^ xv ≤ hi ∧ hi - lo ≤ pow2Eps xv w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := ln2MulBracket_spec hx e hxe w hw
  have hw1 : hi - lo ≤ 1 := by
    have := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := w)
    linarith
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw
  rw [two_rpow_eq_exp]
  refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
  unfold pow2Eps
  refine hab.trans ?_
  unfold expOfBracketEps
  have := Real.exp_pos (xv * Real.log 2)
  nlinarith

/-- `pow2Approx` is a strict enclosure of `2^x` for a non-integer finite `x`, with width at
most `pow2Eps x w`. -/
theorem pow2Approx_spec {w : ℕ} (hw : 64 ≤ w) (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hni : ¬ isInteger (finite s e q m hv) = true) :
    ∃ lv hv' : ℝ, Rounds (pow2Approx (finite s e q m hv) e w).1 lv ∧
      Rounds (pow2Approx (finite s e q m hv) e w).2 hv' ∧
      lv < (2 : ℝ) ^ finiteVal s e m ∧ (2 : ℝ) ^ finiteVal s e m < hv' ∧
      hv' - lv ≤ pow2Eps (finiteVal s e m) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ :=
    pow2Bracket_spec (toVal_finite s e q m hv) e (abs_finiteVal_bounds s e hv).2 hw
  have hni' : ¬ ∃ n : ℤ, finiteVal s e m = n := fun h => hni ((isInteger_finite s e hv).mpr h)
  obtain ⟨N, J, hd⟩ := exists_dyadic_of_finiteVal s e m
  have hirr := irrational_two_rpow_of_dyadic hd hni'
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 hirr
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `2^x`. -/
theorem pow2Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (s : Bool) (e : AzInt)
    {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (hni : ¬ isInteger (finite s e q m hv) = true)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (pow2Approx (finite s e q m hv) e (w₀ * 2 ^ f)).1
      (pow2Approx (finite s e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  have hni' : ¬ ∃ n : ℤ, finiteVal s e m = n := fun h => hni ((isInteger_finite s e hv).mpr h)
  have hirr := irrational_two_rpow_of_dyadic
    (exists_dyadic_of_finiteVal s e m).choose_spec.choose_spec hni'
  exists_isSome_of_irrational_threshold p mode (pow2Approx (finite s e q m hv) e) hirr
    (pow2Eps (finiteVal s e m)) (tendsto_exp2Eps _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := pow2Approx_spec hw s e hv hni
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

/-- `pow2RatBracket q w` encloses `2^q` with width at most `pow2Eps q w`. -/
theorem pow2RatBracket_spec (q : AzRat) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (pow2RatBracket q w).1.toVal = some (lo : EReal) ∧
      (pow2RatBracket q w).2.toVal = some (hi : EReal) ∧
      lo ≤ (2 : ℝ) ^ (AzRat.toRat q : ℝ) ∧ (2 : ℝ) ^ (AzRat.toRat q : ℝ) ≤ hi ∧
      hi - lo ≤ pow2Eps (AzRat.toRat q : ℝ) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := ln2MulRatBracket_spec q w hw
  have hw1 : hi - lo ≤ 1 := by
    have := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := w)
    linarith
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw
  rw [two_rpow_eq_exp]
  refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
  unfold pow2Eps
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

/-- `pow2RatApprox` is a strict enclosure of `2^q` for a non-integer rational `q`, with width at
most `pow2Eps q w`. -/
theorem pow2RatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (hd : q.den.toNat ≠ 1) :
    ∃ lv hv : ℝ, Rounds (pow2RatApprox q w).1 lv ∧ Rounds (pow2RatApprox q w).2 hv ∧
      lv < (2 : ℝ) ^ (AzRat.toRat q : ℝ) ∧ (2 : ℝ) ^ (AzRat.toRat q : ℝ) < hv ∧
      hv - lv ≤ pow2Eps (AzRat.toRat q : ℝ) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := pow2RatBracket_spec q hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 (irrational_two_rpow_toRat q hd)
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `2^q`. -/
theorem pow2RatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (hd : q.den.toNat ≠ 1) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (pow2RatApprox q (w₀ * 2 ^ f)).1 (pow2RatApprox q (w₀ * 2 ^ f)).2
      p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (pow2RatApprox q) (irrational_two_rpow_toRat q hd)
    (pow2Eps (AzRat.toRat q : ℝ)) (tendsto_exp2Eps _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := pow2RatApprox_spec hw q hd
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-! ### The bracket of `2^x − 1` -/

/-- The real arithmetic of the width of `expM1OfBracket`: the upper end encloses `exp v − 1`,
and the width is at most twice that of the inner bracket plus `32 exp lo · δ + |exp lo − 1| u`
for a bracket of width `δ ≤ 1/64`. -/
theorem expM1OfBracket_width {lo hi v a b dv E corr hi' u δ D : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ 1 / 1024) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 64) (h1 : lo ≤ v) (h2 : v ≤ hi)
    (hwid : hi - lo ≤ δ) (ha : a ≤ Real.exp lo - 1) (hb : Real.exp lo - 1 ≤ b) (hab : b - a ≤ D)
    (hd1 : hi - lo ≤ dv) (hd2 : dv ≤ hi - lo + 2 * |hi - lo| * (u / 256))
    (hE1 : b + 1 ≤ E) (hE2 : E ≤ b + 1 + 2 * (b + 1) * (u / 256))
    (hc1 : E * (2 * dv) ≤ corr) (hc2 : corr ≤ E * (2 * dv) + 2 * (E * (2 * dv)) * (u / 256))
    (hh1 : b + corr ≤ hi') (hh2 : hi' ≤ b + corr + 2 * |b + corr| * (u / 256)) :
    Real.exp v - 1 ≤ hi' ∧
      hi' - a ≤ 2 * D + 32 * Real.exp lo * δ + |Real.exp lo - 1| * u := by
  have hEl := Real.exp_pos lo
  have hD0 : 0 ≤ D := by linarith
  have hhl : 0 ≤ hi - lo := by linarith
  rw [abs_of_nonneg hhl] at hd2
  have hdv0 : 0 ≤ dv := by linarith
  have hdv2 : dv ≤ 2 * δ := by nlinarith
  have hb1 : 0 < b + 1 := by linarith
  have hE0 : 0 < E := by linarith
  have hE3 : E ≤ 2 * (b + 1) := by nlinarith
  have hbD : b + 1 ≤ Real.exp lo + D := by linarith
  have hEd : 0 ≤ E * (2 * dv) := by positivity
  have hcorr0 : 0 ≤ corr := by linarith
  have hcorr2 : corr ≤ 2 * (E * (2 * dv)) := by nlinarith
  have hcorr3 : corr ≤ 16 * (Real.exp lo + D) * δ := by
    have : E * (2 * dv) ≤ 2 * (b + 1) * (2 * (2 * δ)) :=
      mul_le_mul hE3 (by linarith) (by linarith) (by linarith)
    nlinarith
  constructor
  · have e1 : Real.exp v ≤ Real.exp lo * (1 + 2 * (v - lo)) :=
      exp_le_exp_mul_one_add h1 (by linarith)
    have e2 : Real.exp lo * (2 * (v - lo)) ≤ (b + 1) * (2 * dv) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) hb1.le
    have e3 : (b + 1) * (2 * dv) ≤ E * (2 * dv) :=
      mul_le_mul_of_nonneg_right hE1 (by linarith)
    nlinarith
  · have habs : |b + corr| ≤ |Real.exp lo - 1| + D + corr := by
      calc |b + corr| ≤ |b| + |corr| := abs_add_le _ _
        _ ≤ |Real.exp lo - 1| + D + corr := by
          rw [abs_of_nonneg hcorr0]
          have : |b| ≤ |Real.exp lo - 1| + D :=
            abs_le.mpr ⟨by linarith [neg_abs_le (Real.exp lo - 1)],
              by linarith [le_abs_self (Real.exp lo - 1)]⟩
          linarith
    have h3 : 2 * |b + corr| * (u / 256) ≤ 2 * (|Real.exp lo - 1| + D + corr) * (u / 256) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : corr * u ≤ corr := mul_le_of_le_one_right hcorr0 (by linarith)
    have h5 : D * u ≤ D := mul_le_of_le_one_right hD0 (by linarith)
    have h6 : 16 * D * δ ≤ D / 4 := by nlinarith
    have h7 : 0 ≤ |Real.exp lo - 1| * u := by positivity
    have h8 : 0 ≤ Real.exp lo * δ := by positivity
    nlinarith

/-- The width bound of `pow2M1Bracket` at compensation `c`. -/
noncomputable def pow2M1Eps (xv : ℝ) (c w : ℕ) : ℝ := expM1RatEps (xv * Real.log 2) c w

theorem tendsto_exp2M1Eps (xv : ℝ) (c : ℕ) :
    Filter.Tendsto (pow2M1Eps xv c) Filter.atTop (nhds 0) :=
  tendsto_expM1RatEps (xv * Real.log 2) c

/-- `2^e ≤ 2 |x|` for a finite float `x` of exponent `e`. -/
theorem two_zpow_le_two_mul_abs_finiteVal (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) : (2 : ℝ) ^ e.toInt ≤ 2 * |finiteVal s e m| := by
  have h := (abs_finiteVal_bounds s e hv).1
  rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
  linarith

/-- The compensated width `2^(−w−c)` is at most `2^(−64) · 2^e` for `c = expM1Comp e`. -/
theorem half_pow_comp_le (e : AzInt) {w : ℕ} (hw : 64 ≤ w) :
    (1 / 2 : ℝ) ^ (w + expM1Comp e) ≤ (1 / 2 : ℝ) ^ 64 * (2 : ℝ) ^ e.toInt := by
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  have h64 : (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 64 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
  unfold expM1Comp
  rw [htoInt]
  split_ifs with hs
  · rw [add_zero, zpow_natCast]
    have : (1 : ℝ) ≤ 2 ^ e.abs.toNat := one_le_pow₀ (by norm_num)
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) w]
  · have h2c : (1 / 2 : ℝ) ^ e.abs.toNat = (2 : ℝ) ^ (-(e.abs.toNat : ℤ)) := by
      rw [zpow_neg, zpow_natCast, one_div_pow, one_div]
    rw [pow_add, ← h2c]
    exact mul_le_mul_of_nonneg_right h64 (by positivity)

/-- The slack of `expM1RatEps`: a third of it dominates `(|exp v − 1| + 33 exp v) 2^(−w)`. -/
theorem expM1RatEps_slack (v : ℝ) (c w : ℕ) :
    (|Real.exp v - 1| + 33 * Real.exp v) * (1 / 2 : ℝ) ^ w ≤ expM1RatEps v c w / 3 := by
  unfold expM1RatEps
  have hwc : (9 : ℝ) ≤ (w : ℝ) + c + 9 := by
    linarith [(Nat.cast_nonneg w : (0 : ℝ) ≤ w), (Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  have hEvp := Real.exp_pos v
  have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hkey : |Real.exp v - 1| + 33 * Real.exp v
      ≤ 2 * Real.exp v * (80 * ((w : ℝ) + c + 9)) + |Real.exp v - 1| + Real.exp v + 4 * |v| := by
    have : 2 * Real.exp v * (80 * 9) ≤ 2 * Real.exp v * (80 * ((w : ℝ) + c + 9)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [abs_nonneg v]
  have := mul_le_mul_of_nonneg_right hkey hu
  linarith

set_option maxHeartbeats 1000000 in
/-- `expM1OfBracket X e w` encloses `exp v − 1` for a bracket `X = [lo, hi]` of `v` of width at
most `δ ≤ 1/64` whose lower end satisfies `|lo| < 2^e` and `|lo| ≤ 2|v|`; the width is at most
`(2/3) expM1RatEps v c w + (|exp v − 1| + exp v) 2^(−w) + 32 exp v · δ`, `c = expM1Comp e`. -/
theorem expM1OfBracket_spec_of_bounds {X : AzFloat × AzFloat} {lo hi v δ : ℝ} (e : AzInt)
    {w : ℕ} (hlo : X.1.toVal = some (lo : EReal)) (hhi : X.2.toVal = some (hi : EReal))
    (h1 : lo ≤ v) (h2 : v ≤ hi) (hwid : hi - lo ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 64)
    (hlo_e : |lo| < (2 : ℝ) ^ e.toInt) (hlo_v : |lo| ≤ 2 * |v|) (hw : 64 ≤ w) :
    ∃ a b : ℝ, (expM1OfBracket X e w).1.toVal = some (a : EReal) ∧
      (expM1OfBracket X e w).2.toVal = some (b : EReal) ∧
      a ≤ Real.exp v - 1 ∧ Real.exp v - 1 ≤ b ∧
      b - a ≤ 2 * expM1RatEps v (expM1Comp e) w / 3
        + (|Real.exp v - 1| + Real.exp v) * (1 / 2 : ℝ) ^ w + 32 * Real.exp v * δ := by
  have : NeZero (w + 8) := ⟨by omega⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = expM1Comp e := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 / 1024 := by
    rw [hu]; exact (half_pow_small hw).trans (by norm_num)
  -- `exp lo − 1`
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expM1Bracket_spec hlo e hlo_e hw
  rw [← hc] at hab
  simp only [expM1OfBracket]
  -- the correction
  obtain ⟨dv, hd, hd1, hd2⟩ := subCeiling_abs hhi hlo (w + 8)
  have hb1' : 0 ≤ b + 1 := by linarith [Real.exp_pos lo]
  obtain ⟨E, hE, hEc⟩ := addCeiling_err hb toVal_one' (w + 8) hb1'
  have h2d : ((subPrecRound X.2 X.1 (w + 8) .Ceiling).1 <<< AzInt.ofInt 1).toVal
      = some ((2 * dv : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hd (AzInt.ofInt 1)
    rw [AzInt.toInt_ofInt, zpow_one, mul_comm] at h
    exact h
  have hdv0 : 0 ≤ dv := by linarith
  have hE0 : 0 ≤ E := by linarith [hEc.ge]
  obtain ⟨corr, hcorr, hcc⟩ := mulCeiling_err hE h2d (w + 8) (mul_nonneg hE0 (by linarith))
  obtain ⟨hi', hhi', hh1, hh2⟩ := addCeiling_abs hb hcorr (w + 8)
  have h256 : (1 / 2 : ℝ) ^ (w + 8) = u / 256 := by
    rw [pow_add, hu]; ring
  rw [h256] at hd2 hh2
  have hE1 := hEc.ge
  have hE2 := hEc.le
  rw [h256] at hE2
  have hc1 := hcc.ge
  have hc2 := hcc.le
  rw [h256] at hc2
  obtain ⟨hup, hwidth⟩ := expM1OfBracket_width hu0 hu1 hδ0 hδ1 h1 h2 hwid ha1 hb1 hab hd1 hd2
    hE1 hE2 hc1 hc2 hh1 hh2
  refine ⟨a, hi', ha, hhi', ?_, ?_, ?_⟩
  · exact ha1.trans (by linarith [Real.exp_le_exp.mpr h1])
  · exact hup
  · rw [← hc, ← hu]
    have hD := expM1Eps_le h1 hlo_v c w
    rw [← hu] at hD
    have hEv : Real.exp lo ≤ Real.exp v := Real.exp_le_exp.mpr h1
    have hEv1 : |Real.exp lo - 1| ≤ |Real.exp v - 1| + Real.exp v := by
      calc |Real.exp lo - 1| = |(Real.exp v - 1) - (Real.exp v - Real.exp lo)| := by ring_nf
        _ ≤ |Real.exp v - 1| + |Real.exp v - Real.exp lo| := abs_sub _ _
        _ ≤ |Real.exp v - 1| + Real.exp v := by
          rw [abs_of_nonneg (by linarith : 0 ≤ Real.exp v - Real.exp lo)]
          linarith [Real.exp_pos lo]
    have hR : expM1RatEps v c w
        = 3 * ((2 * Real.exp v * (80 * ((w : ℝ) + c + 9)) + |Real.exp v - 1| + Real.exp v
          + 4 * |v|) * u) := by
      unfold expM1RatEps; rw [hu]
    have h3 : 32 * Real.exp lo * δ ≤ 32 * Real.exp v * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0
    have h4 : |Real.exp lo - 1| * u ≤ (|Real.exp v - 1| + Real.exp v) * u :=
      mul_le_mul_of_nonneg_right hEv1 hu0.le
    linarith

/-- `expM1OfBracket X e w` encloses `exp (x ln 2) − 1` for a bracket `X` of `x ln 2` of width at
most `2^(−w−c)`, `c = expM1Comp e`, where `2^(e−1) ≤ |x| < 2^e`; the width is at most
`expM1RatEps (x ln 2) c w`. -/
theorem expM1OfBracket_spec {X : AzFloat × AzFloat} {lo hi xv : ℝ} (e : AzInt) {w : ℕ}
    (hlo : X.1.toVal = some (lo : EReal)) (hhi : X.2.toVal = some (hi : EReal))
    (h1 : lo ≤ xv * Real.log 2) (h2 : xv * Real.log 2 ≤ hi)
    (hwid : hi - lo ≤ (1 / 2 : ℝ) ^ (w + expM1Comp e)) (hxe : |xv| < (2 : ℝ) ^ e.toInt)
    (hxe1 : (2 : ℝ) ^ e.toInt ≤ 2 * |xv|) (hw : 64 ≤ w) :
    ∃ a b : ℝ, (expM1OfBracket X e w).1.toVal = some (a : EReal) ∧
      (expM1OfBracket X e w).2.toVal = some (b : EReal) ∧
      a ≤ Real.exp (xv * Real.log 2) - 1 ∧ Real.exp (xv * Real.log 2) - 1 ≤ b ∧
      b - a ≤ expM1RatEps (xv * Real.log 2) (expM1Comp e) w := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = expM1Comp e := ⟨_, rfl⟩
  have hδe := half_pow_comp_le e hw
  rw [← hc] at hδe
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (1 / 2 : ℝ) ^ (w + c) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 / 1024 := by
    rw [hu]; exact (half_pow_small hw).trans (by norm_num)
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδu : δ ≤ u := by
    rw [hδ, hu]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hδe' : δ ≤ (1 / 2 : ℝ) ^ 64 * (2 : ℝ) ^ e.toInt := by rw [hδ]; exact hδe
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e.toInt := by positivity
  have hδx : δ ≤ |xv| / 2 ^ 63 := by
    have := mul_le_mul_of_nonneg_left hxe1 (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 64)
    norm_num at this ⊢
    linarith
  have hln1 := Real.log_two_gt_d9
  have hln2 := Real.log_two_lt_d9
  obtain ⟨v, hv'⟩ : ∃ v : ℝ, v = xv * Real.log 2 := ⟨_, rfl⟩
  have habsv : |v| = |xv| * Real.log 2 := by
    rw [hv', abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 2)]
  rw [← hv'] at h1 h2
  rw [← hc, ← hδ] at hwid
  have hlo_e : |lo| < (2 : ℝ) ^ e.toInt := by
    have hxv0 := abs_nonneg xv
    have : |lo| ≤ |v| + δ := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le v, le_abs_self v]
    have h3 : |v| ≤ |xv| * (7 / 10) := by rw [habsv]; nlinarith
    have h4 : |xv| / 2 ^ 63 ≤ |xv| * (1 / 10) := by nlinarith
    linarith
  have hlo_v : |lo| ≤ 2 * |v| := by
    have : |lo| ≤ |v| + δ := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le v, le_abs_self v]
    have h3 : |xv| * (6 / 10) ≤ |v| := by rw [habsv]; nlinarith [abs_nonneg xv]
    have h4 : |xv| / 2 ^ 63 ≤ |xv| * (1 / 10) := by nlinarith [abs_nonneg xv]
    linarith
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expM1OfBracket_spec_of_bounds e hlo hhi h1 h2 hwid
    hδ0 (hδu.trans (by linarith)) hlo_e hlo_v hw
  rw [← hc] at hab
  rw [← hv', ← hc]
  refine ⟨a, b, ha, hb, ha1, hb1, hab.trans ?_⟩
  have hslack := expM1RatEps_slack v c w
  rw [← hu] at hslack hab ⊢
  have h3 : 32 * Real.exp v * δ ≤ 32 * Real.exp v * u :=
    mul_le_mul_of_nonneg_left hδu (by positivity)
  linarith

/-- `pow2M1Bracket x e w` encloses `2^x − 1` for a finite float `x` of exponent `e`, with width
at most `pow2M1Eps x (expM1Comp e) w`. -/
theorem pow2M1Bracket_spec (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (pow2M1Bracket (finite s e q m hv) e w).1.toVal = some (lo : EReal) ∧
      (pow2M1Bracket (finite s e q m hv) e w).2.toVal = some (hi : EReal) ∧
      lo ≤ (2 : ℝ) ^ finiteVal s e m - 1 ∧ (2 : ℝ) ^ finiteVal s e m - 1 ≤ hi ∧
      hi - lo ≤ pow2M1Eps (finiteVal s e m) (expM1Comp e) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := ln2MulBracket_spec (toVal_finite s e q m hv) e
    (abs_finiteVal_bounds s e hv).2 (w + expM1Comp e) (by omega)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expM1OfBracket_spec e hlo hhi h1 h2 hwid
    (abs_finiteVal_bounds s e hv).2 (two_zpow_le_two_mul_abs_finiteVal s e hv) hw
  unfold pow2M1Bracket
  rw [two_rpow_eq_exp]
  exact ⟨a, b, ha, hb, ha1, hb1, hab⟩

/-- `2^x − 1` is irrational for a non-integer finite float `x`. -/
theorem irrational_two_rpow_sub_one_finiteVal (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hni : ¬ isInteger (finite s e q m hv) = true) :
    Irrational ((2 : ℝ) ^ finiteVal s e m - 1) := by
  have hni' : ¬ ∃ n : ℤ, finiteVal s e m = n := fun h => hni ((isInteger_finite s e hv).mpr h)
  have h := (irrational_two_rpow_of_dyadic
    (exists_dyadic_of_finiteVal s e m).choose_spec.choose_spec hni').sub_intCast 1
  rwa [Int.cast_one] at h

/-- `pow2M1Approx` is a strict enclosure of `2^x − 1` for a non-integer float `x`, with width at
most `pow2M1Eps x (expM1Comp e) w`. -/
theorem pow2M1Approx_spec {w : ℕ} (hw : 64 ≤ w) (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hni : ¬ isInteger (finite s e q m hv) = true) :
    ∃ lv hv' : ℝ, Rounds (pow2M1Approx (finite s e q m hv) e w).1 lv ∧
      Rounds (pow2M1Approx (finite s e q m hv) e w).2 hv' ∧
      lv < (2 : ℝ) ^ finiteVal s e m - 1 ∧ (2 : ℝ) ^ finiteVal s e m - 1 < hv' ∧
      hv' - lv ≤ pow2M1Eps (finiteVal s e m) (expM1Comp e) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := pow2M1Bracket_spec s e hv hw
  obtain ⟨r1, r2, r3, r4⟩ :=
    rounds_of_bracket hlo hhi h1 h2 (irrational_two_rpow_sub_one_finiteVal s e hv hni)
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `2^x − 1`. -/
theorem pow2M1Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (s : Bool)
    (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hni : ¬ isInteger (finite s e q m hv) = true) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (pow2M1Approx (finite s e q m hv) e (w₀ * 2 ^ f)).1
      (pow2M1Approx (finite s e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (pow2M1Approx (finite s e q m hv) e)
    (irrational_two_rpow_sub_one_finiteVal s e hv hni) (pow2M1Eps (finiteVal s e m) (expM1Comp e))
    (tendsto_exp2M1Eps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := pow2M1Approx_spec hw s e hv hni
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-! ### The bracket of `2^q − 1` for a rational `q` -/

/-- `2^(e−1) ≤ |q| < 2^e` for the exponent `e = pow2M1RatExp q` of a rational `q ≠ 0`. -/
theorem pow2M1RatExp_bounds (q : AzRat) (h0 : q.num ≠ 0) :
    |(AzRat.toRat q : ℝ)| < (2 : ℝ) ^ (pow2M1RatExp q).toInt ∧
      (2 : ℝ) ^ (pow2M1RatExp q).toInt ≤ 2 * |(AzRat.toRat q : ℝ)| := by
  have hqpos : 0 < |(AzRat.toRat q : ℝ)| := AzRat.abs_toRat_pos q h0
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = Int.log 2 |(AzRat.toRat q : ℝ)| := ⟨_, rfl⟩
  have he : (pow2M1RatExp q).toInt = L + 1 := by
    unfold pow2M1RatExp
    rw [AzInt.toInt_ofInt, AzRat.floorLogBaseAbs_eq 2 (by decide) q h0, hL]; rfl
  have h2L : (2 : ℝ) ^ L ≤ |(AzRat.toRat q : ℝ)| := by
    rw [hL]; exact_mod_cast Int.zpow_log_le_self (by norm_num : 1 < 2) hqpos
  have hqL : |(AzRat.toRat q : ℝ)| < (2 : ℝ) ^ (L + 1) := by
    rw [hL]; exact_mod_cast Int.lt_zpow_succ_log_self (by norm_num : 1 < 2) |(AzRat.toRat q : ℝ)|
  rw [he]
  refine ⟨hqL, ?_⟩
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-- `pow2M1RatBracket q w` encloses `2^q − 1` for a rational `q ≠ 0`, with width at most
`pow2M1Eps q (expM1Comp (pow2M1RatExp q)) w`. -/
theorem pow2M1RatBracket_spec (q : AzRat) (h0 : q.num ≠ 0) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (pow2M1RatBracket q w).1.toVal = some (lo : EReal) ∧
      (pow2M1RatBracket q w).2.toVal = some (hi : EReal) ∧
      lo ≤ (2 : ℝ) ^ (AzRat.toRat q : ℝ) - 1 ∧ (2 : ℝ) ^ (AzRat.toRat q : ℝ) - 1 ≤ hi ∧
      hi - lo ≤ pow2M1Eps (AzRat.toRat q : ℝ) (expM1Comp (pow2M1RatExp q)) w := by
  obtain ⟨hxe, hxe1⟩ := pow2M1RatExp_bounds q h0
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    ln2MulRatBracket_spec q (w + expM1Comp (pow2M1RatExp q)) (by omega)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ :=
    expM1OfBracket_spec (pow2M1RatExp q) hlo hhi h1 h2 hwid hxe hxe1 hw
  unfold pow2M1RatBracket
  rw [two_rpow_eq_exp]
  exact ⟨a, b, ha, hb, ha1, hb1, hab⟩

/-- `2^q − 1` is irrational for a rational `q` that is not an integer (`den ≠ 1`). -/
theorem irrational_two_rpow_sub_one_toRat (q : AzRat) (hd : q.den.toNat ≠ 1) :
    Irrational ((2 : ℝ) ^ (AzRat.toRat q : ℝ) - 1) := by
  have h := (irrational_two_rpow_toRat q hd).sub_intCast 1
  rwa [Int.cast_one] at h

/-- `pow2M1RatApprox` is a strict enclosure of `2^q − 1` for a non-integer rational `q`, with
width at most `pow2M1Eps q (expM1Comp (pow2M1RatExp q)) w`. -/
theorem pow2M1RatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0)
    (hd : q.den.toNat ≠ 1) :
    ∃ lv hv : ℝ, Rounds (pow2M1RatApprox q w).1 lv ∧ Rounds (pow2M1RatApprox q w).2 hv ∧
      lv < (2 : ℝ) ^ (AzRat.toRat q : ℝ) - 1 ∧ (2 : ℝ) ^ (AzRat.toRat q : ℝ) - 1 < hv ∧
      hv - lv ≤ pow2M1Eps (AzRat.toRat q : ℝ) (expM1Comp (pow2M1RatExp q)) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := pow2M1RatBracket_spec q h0 hw
  obtain ⟨r1, r2, r3, r4⟩ :=
    rounds_of_bracket hlo hhi h1 h2 (irrational_two_rpow_sub_one_toRat q hd)
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `2^q − 1`. -/
theorem pow2M1RatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (hd : q.den.toNat ≠ 1) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (pow2M1RatApprox q (w₀ * 2 ^ f)).1
      (pow2M1RatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (pow2M1RatApprox q)
    (irrational_two_rpow_sub_one_toRat q hd)
    (pow2M1Eps (AzRat.toRat q : ℝ) (expM1Comp (pow2M1RatExp q))) (tendsto_exp2M1Eps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwidth⟩ := pow2M1RatApprox_spec hw q h0 hd
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

end Azurite.AzFloat
