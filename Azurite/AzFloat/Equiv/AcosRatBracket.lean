/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosRatBracket
import Azurite.AzFloat.Equiv.AcosBracket
import Azurite.AzFloat.Equiv.SqrtRat
import Azurite.AzFloat.Equiv.AtanRatWithPeriodBracket
import Azurite.AzRat.Equiv.Sub
import Azurite.AzRat.Equiv.Add
import Azurite.AzRat.Equiv.Div

/-!
# Equivalence: the bracket of `arccos q` for a rational `q`

`acosRatDouble_spec` (the doubled arctangent of the rational square root), `acosRatAbsEncl_spec`
(the enclosure of `arccos |q|`, nonnegative lower end), `acosRatBracket_spec` (width at most
`2^(−w)`), `acosRatApprox_spec`, `irrational_arccos_toRat`, `acosRatApprox_isSome_exists` (the
Ziv certificate).
-/

open Real

namespace Azurite.AzFloat

/-- The doubled arctangent of the rational square root: for a rational `0 < |q| < 1` and a level
`K ≥ w + 8`, an enclosure of `arccos |q|` with a nonnegative lower end, an upper end at most
`4` and width at most `2^(−w)/128`. -/
theorem acosRatDouble_spec (q : AzRat) (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1)
    {K w : ℕ} (hKw : w + 8 ≤ K) :
    ∃ lo hi : ℝ,
      ((atanWiden (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) (K + 64 + 8) .Floor).1
        (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) (K + 64 + 8) .Ceiling).1 K (K + 64)).1
          <<< AzInt.ofInt 1).toVal = some (lo : EReal) ∧
      ((atanWiden (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) (K + 64 + 8) .Floor).1
        (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) (K + 64 + 8) .Ceiling).1 K (K + 64)).2
          <<< AzInt.ofInt 1).toVal = some (hi : EReal) ∧
      0 ≤ lo ∧ lo ≤ arccos |(AzRat.toRat q : ℝ)| ∧ arccos |(AzRat.toRat q : ℝ)| ≤ hi ∧ hi ≤ 4 ∧
      hi - lo ≤ (1 / 2 : ℝ) ^ w / 128 := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  set a := |(AzRat.toRat q : ℝ)| with ha
  have ha0 : 0 < a := abs_pos.mpr hq0
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = a := by
    rw [AzRat.toRat_abs, Rat.cast_abs]
  set P := K + 64 + 8 with hP
  have : NeZero P := ⟨by omega⟩
  set ε := (1 / 2 : ℝ) ^ P with hε
  have hε0 : 0 < ε := by positivity
  have hQ : ((AzRat.toRat ((1 - q.abs) / (1 + q.abs)) : ℚ) : ℝ) = (1 - a) / (1 + a) := by
    rw [AzRat.toRat_div, AzRat.toRat_sub, AzRat.toRat_add, AzRat.toRat_one]
    push_cast
    rw [habs]
  have hQ0 : 0 ≤ (1 - a) / (1 + a) := div_nonneg (by linarith) (by linarith)
  set T := √((1 - a) / (1 + a)) with hT
  have hT0 : 0 ≤ T := sqrt_nonneg _
  have hT1 : T ≤ 1 := by
    apply sqrt_le_one.mpr
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨tl, htl, htl0, htl1, htl2⟩ := roundVal_floor_err P hT0
  obtain ⟨th, hth, hth1, hth2⟩ := roundVal_ceiling_err P hT0
  rw [← hε] at htl2 hth2
  have htlv : (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) P .Floor).1.toVal
      = some (tl : EReal) := by
    rw [sqrtRatPrecRound_eq, hQ, Spec.sqrt_coe _ hQ0]
    exact htl
  have hthv : (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) P .Ceiling).1.toVal
      = some (th : EReal) := by
    rw [sqrtRatPrecRound_eq, hQ, Spec.sqrt_coe _ hQ0]
    exact hth
  have hTε : T * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hT1 hε0.le
  have hid := arccos_eq_two_arctan ha0.le h1.le
  rw [← hT] at hid
  obtain ⟨lo, hi, hlo, hhi, hlo0, hl, hh, hhi4, hw⟩ :=
    atanDouble_spec (t := ((sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) P .Floor).1,
      (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) P .Ceiling).1)) hT1 hKw htlv hthv htl0 htl1
      hth1 (by rw [← hε]; linarith)
  rw [← hid] at hl hh
  exact ⟨lo, hi, hlo, hhi, hlo0, hl, hh, hhi4, hw⟩

/-- **The enclosure of `arccos |q|`** for a rational `0 < |q| < 1`: nonnegative lower end, width
at most `2^(−w)`. -/
theorem acosRatAbsEncl_spec (q : AzRat) (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1)
    (w : ℕ) :
    IsEncl0W (acosRatBracket false q w) (arccos |(AzRat.toRat q : ℝ)|) ((1 / 2 : ℝ) ^ w) := by
  unfold acosRatBracket
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  obtain ⟨lo, hi, hlo, hhi, hlo0, hl, hh, -, hw⟩ := acosRatDouble_spec q h0 h1
    (K := w + 8 + (if (ratExpBound ((1 - q.abs) / (1 + q.abs))).sign = true then 0
      else (ratExpBound ((1 - q.abs) / (1 + q.abs))).abs.toNat / 2)) (w := w) (by omega)
  exact ⟨lo, hi, hlo, hhi, hlo0, hl, hh, by linarith⟩

/-- **The bracket of `arccos q`** for a rational `0 < |q| < 1`: width at most `2^(−w)`. -/
theorem acosRatBracket_spec (q : AzRat) (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1)
    (w : ℕ) :
    ∃ lo hi : ℝ, (acosRatBracket (!q.sign) q w).1.toVal = some (lo : EReal) ∧
      (acosRatBracket (!q.sign) q w).2.toVal = some (hi : EReal) ∧
      lo ≤ arccos (AzRat.toRat q : ℝ) ∧ arccos (AzRat.toRat q : ℝ) ≤ hi ∧
      hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  have hs := toRat_sign_iff q h0
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  cases hsg : q.sign with
  | true =>
    obtain ⟨lo, hi, hlo, hhi, -, hl, hh, hw⟩ := acosRatAbsEncl_spec q h0 h1 w
    rw [abs_of_pos (hs.mp hsg)] at hl hh
    exact ⟨lo, hi, hlo, hhi, hl, hh, hw⟩
  | false =>
    have hlt : (AzRat.toRat q : ℝ) < 0 := by
      rcases lt_or_gt_of_ne hq0 with h | h
      · exact h
      · rw [hs.mpr h] at hsg; cases hsg
    unfold acosRatBracket
    simp only [Bool.not_false, ↓reduceIte]
    obtain ⟨al, ah, hal, hah, hal0, hl, hh, hah4, hw⟩ :=
      acosRatDouble_spec q h0 h1 (K := w + 8) (w := w) le_rfl
    obtain ⟨lo, hi, hlo, hhi, hl', hh', hwd⟩ := piShiftEncl_spec false false
      (A := ((atanWiden (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) (w + 8 + 64 + 8) .Floor).1
        (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) (w + 8 + 64 + 8) .Ceiling).1 (w + 8)
        (w + 8 + 64)).1 <<< AzInt.ofInt 1,
        (atanWiden (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) (w + 8 + 64 + 8) .Floor).1
        (sqrtRatPrecRound ((1 - q.abs) / (1 + q.abs)) (w + 8 + 64 + 8) .Ceiling).1 (w + 8)
        (w + 8 + 64)).2 <<< AzInt.ofInt 1))
      hal hah hal0 hl hh hah4 hw (V := w + 72) (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte] at hl' hh'
    have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
      have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
        rw [pow_add]
        norm_num
        ring
      rw [← h10]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hxa : (AzRat.toRat q : ℝ) = -|(AzRat.toRat q : ℝ)| := by
      rw [abs_of_neg hlt, neg_neg]
    rw [hxa, arccos_neg]
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩

/-- `acosRatApprox` as a pair of `Roundable`s bracketing `arccos q`. -/
theorem acosRatApprox_spec (q : AzRat) (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1)
    (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (acosRatApprox q w).1 lv ∧ Rounds (acosRatApprox q w).2 hv ∧
      lv ≤ arccos (AzRat.toRat q : ℝ) ∧ arccos (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, hl, hh, hwid⟩ := acosRatBracket_spec q h0 h1 w
  obtain ⟨lv, hv, hR1, hR2, hl', hh', he⟩ := enclApprox_spec false hlo hhi hl hh
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl' hh'
  exact ⟨lv, hv, hR1, hR2, hl', hh', by rw [he]; exact hwid⟩

/-- `arccos q` is irrational for a rational `q` with `|q| < 1`. -/
theorem irrational_arccos_toRat (q : AzRat) (h1 : |(AzRat.toRat q : ℝ)| < 1) :
    Irrational (arccos (AzRat.toRat q : ℝ)) := by
  obtain ⟨h2, h3⟩ := abs_lt.mp h1
  exact irrational_arccos_rat h2.le h3

/-- The Ziv certificate for `arccos q`, `q` a rational with `0 < |q| < 1`. -/
theorem acosRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (acosRatApprox q (w₀ * 2 ^ f)).1 (acosRatApprox q (w₀ * 2 ^ f)).2
      p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (acosRatApprox q)
    (irrational_arccos_toRat q h1) (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => acosRatApprox_spec q h0 h1 w) w₀ hw₀

end Azurite.AzFloat
