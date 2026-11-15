/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanRatBracket
import Azurite.AzFloat.Equiv.AtanBracket
import Azurite.AzFloat.Equiv.SinRatBracket

/-!
# Equivalence: the bracket of `arctan q` for a rational `q`

* `atanWiden_spec`: the widened levels enclose `arctan t` for `r_lo ≤ t ≤ r_hi`, width at most
  `(3/4) 2^(−K) + 14·2^(−V)`.
* `atanRatBracket_spec` (width at most `2^(−w)`), `atanRatApprox_spec`,
  `atanRatApprox_isSome_exists` (the Ziv certificate), `atanTinyRat?_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- **The widening**: for floats `0 ≤ r_lo ≤ t ≤ r_hi` with `t ≤ 1` and
`r_hi − r_lo ≤ 4·2^(−V)`, `V = K + 64`, `atanWiden` encloses `arctan t` with a nonnegative lower
end, an upper end at most `4` and width at most `(3/4) 2^(−K) + 14·2^(−V)`. -/
theorem atanWiden_spec {rl rh : AzFloat} {rlv rhv t : ℝ} (hrl : rl.toVal = some (rlv : EReal))
    (hrh : rh.toVal = some (rhv : EReal)) (h0 : 0 ≤ rlv) (h1 : rlv ≤ t) (h2 : t ≤ rhv)
    (ht1 : t ≤ 1) (K : ℕ) (hd : rhv - rlv ≤ 4 * (1 / 2 : ℝ) ^ (K + 64)) :
    ∃ lo hi : ℝ, (atanWiden rl rh K (K + 64)).1.toVal = some (lo : EReal) ∧
      (atanWiden rl rh K (K + 64)).2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ arctan t ∧
      arctan t ≤ hi ∧ hi ≤ 4 ∧
      hi - lo ≤ 3 / 4 * (1 / 2 : ℝ) ^ K + 14 * (1 / 2 : ℝ) ^ (K + 64) := by
  unfold atanWiden
  dsimp only
  have : NeZero (K + 64) := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ (K + 64) with hu
  have hu0 : 0 ≤ u := by positivity
  have hK1 : (1 / 2 : ℝ) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
  have hu1 : u ≤ 1 / 1024 := by
    have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 1024 := by norm_num
    rw [hu, pow_add]
    nlinarith
  obtain ⟨lb, hb, hlb, hhb, hb0, hb1, hb2, hbw⟩ := atanLoop_spec hrl h0 (h1.trans ht1) K K
  have hbw' := hbw (by omega)
  obtain ⟨dv, hdv, hdv1, hdv2⟩ := subCeiling_abs hrh hrl 64
  obtain ⟨up, hup, hup1, hup2⟩ := addCeiling_abs hhb hdv (K + 64)
  rw [← hu] at hup2
  have hlip := arctan_sub_arctan_le h1
  have hrr : arctan rlv ≤ arctan t := arctan_strictMono.monotone h1
  have hat1 : arctan rlv ≤ 1 := (arctan_le_self h0).trans (h1.trans ht1)
  have hdr0 : 0 ≤ rhv - rlv := by linarith
  have hdv3 : dv ≤ 8 * u := by
    have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
    rw [abs_of_nonneg hdr0] at hdv2
    have := mul_le_mul_of_nonneg_left h64 hdr0
    linarith
  have habs1 : |hb + dv| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith
  have m1 := mul_le_mul_of_nonneg_right habs1 hu0
  exact ⟨lb, up, hlb, hup, hb0, hb1.trans hrr, by linarith, by linarith, by linarith⟩

/-- `|q| ≤ 1` when `num ≤ den`, and `1 < |q|` otherwise. -/
theorem abs_toRat_le_one_iff (q : AzRat) : q.num ≤ q.den ↔ |(AzRat.toRat q : ℝ)| ≤ 1 := by
  have hden := den_pos_real q
  rw [abs_coe_toRat, div_le_one hden, Nat.cast_le]
  change AzNat.compare q.num q.den ≠ Ordering.gt ↔ _
  rw [AzNat.compare_eq_compare_toNat]
  constructor
  · intro h
    exact not_lt.mp fun hlt => h (compare_gt_iff_gt.mpr hlt)
  · intro h hgt
    exact absurd (compare_gt_iff_gt.mp hgt) (not_lt.mpr h)

/-- The floor and the ceiling at `V` bits of a rational `0 ≤ r ≤ 1`. -/
theorem ofAzRatRound_unit (r : AzRat) {rv : ℝ} (hrv : ((AzRat.toRat r : ℚ) : ℝ) = rv)
    (hr0 : 0 ≤ rv) (hr1 : rv ≤ 1) (V : ℕ) [NeZero V] (hV : 2 ≤ V) :
    ∃ lv hv : ℝ, (ofAzRatRound r V .Floor).1.toVal = some (lv : EReal) ∧
      (ofAzRatRound r V .Ceiling).1.toVal = some (hv : EReal) ∧ 0 ≤ lv ∧ lv ≤ rv ∧ rv ≤ hv ∧
      hv - lv ≤ 4 * (1 / 2 : ℝ) ^ V := by
  obtain ⟨lv, hlv, hl1, hl2⟩ := ofAzRatRound_floor_abs r V
  obtain ⟨hv, hhv, hh1, hh2⟩ := ofAzRatRound_ceiling_abs r V
  rw [hrv] at hl1 hl2 hh1 hh2
  rw [abs_of_nonneg hr0] at hl2 hh2
  set u := (1 / 2 : ℝ) ^ V with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 4 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hV
    rw [← hu] at this
    norm_num at this
    linarith
  have hru : rv * u ≤ u := mul_le_of_le_one_left hu0 hr1
  have hru0 : 0 ≤ rv * u := mul_nonneg hr0 hu0
  have hru4 : rv * u ≤ rv / 4 := by nlinarith
  exact ⟨lv, hv, hlv, hhv, by linarith, hl1, hh1, by linarith⟩

/-- **The bracket of `arctan |q|`**: ends with values around `arctan |q|`, width at most
`2^(−w)`. -/
theorem atanRatBracket_spec (q : AzRat) (h0 : q.num ≠ 0) (w : ℕ) :
    ∃ lo hi : ℝ, (atanRatBracket q w).1.toVal = some (lo : EReal) ∧
      (atanRatBracket q w).2.toVal = some (hi : EReal) ∧
      lo ≤ arctan |(AzRat.toRat q : ℝ)| ∧ arctan |(AzRat.toRat q : ℝ)| ≤ hi ∧
      hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  set a := |(AzRat.toRat q : ℝ)| with ha
  have ha0 : 0 < a := abs_pos.mpr hq0
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = a := by
    rw [AzRat.toRat_abs, Rat.cast_abs]
  have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 ^ 64 := by norm_num
  have h8 : (1 / 2 : ℝ) ^ 8 = 1 / 256 := by norm_num
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  unfold atanRatBracket
  split_ifs with hc
  · -- `|q| ≤ 1`
    have ha1 : a ≤ 1 := (abs_toRat_le_one_iff q).mp hc
    dsimp only
    set K := atanWork (ratExpBound q) w with hK
    have hKw : w + 8 ≤ K := by
      rw [hK]
      unfold atanWork
      omega
    have : NeZero (K + 64) := ⟨by omega⟩
    obtain ⟨lv, hv, hlv, hhv, hl0, hl1, hh1, hd⟩ :=
      ofAzRatRound_unit q.abs habs ha0.le ha1 (K + 64) (by omega)
    obtain ⟨lo, hi, hlo, hhi, -, h1, h2, -, h3⟩ := atanWiden_spec hlv hhv hl0 hl1 hh1 ha1 K hd
    refine ⟨lo, hi, hlo, hhi, h1, h2, h3.trans ?_⟩
    have hKle : (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ (w + 8) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hKw
    have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
    rw [pow_add, h8] at hKle
    rw [pow_add]
    nlinarith
  · -- `|q| > 1`
    have ha1 : 1 < a := not_le.mp fun h => hc ((abs_toRat_le_one_iff q).mpr h)
    dsimp only
    set K := w + 8 with hK
    set V := K + 64 with hV
    have hV64 : 64 ≤ V := by omega
    have : NeZero V := ⟨by omega⟩
    set u := (1 / 2 : ℝ) ^ V with hu
    have hu0 : 0 ≤ u := by positivity
    have hKw : (1 / 2 : ℝ) ^ K = (1 / 2 : ℝ) ^ w / 256 := by
      rw [hK, pow_add, h8]
      ring
    have huK : u ≤ (1 / 2 : ℝ) ^ K / 2 ^ 64 := by
      have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
      rw [hu, hV, pow_add]
      nlinarith
    have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hu1 : u ≤ 1 / 1024 := by
      have : (1 / 2 : ℝ) ^ K / 2 ^ 64 ≤ 1 / 1024 := by
        rw [hKw]
        norm_num
        linarith
      linarith
    set r := a⁻¹ with hr
    have hr0 : 0 < r := inv_pos.mpr ha0
    have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ ha1.le
    have hrabs : ((AzRat.toRat q.abs⁻¹ : ℚ) : ℝ) = r := by
      rw [AzRat.toRat_inv, Rat.cast_inv, habs]
    obtain ⟨lv, hv, hlv, hhv, hl0, hl1, hh1, hd⟩ :=
      ofAzRatRound_unit q.abs⁻¹ hrabs hr0.le hr1 V (by omega)
    obtain ⟨lb, up, hlb, hup, hlb0, hlb1, hup1, hup4, hbw⟩ :=
      atanWiden_spec hlv hhv hl0 hl1 hh1 hr1 K hd
    rw [← hV] at hlb hup
    rw [← hV, ← hu] at hbw
    obtain ⟨pl, ph, hpl, hph, hpl0, hpl1, hph1, hpw⟩ := piBracket_spec_width hV64
    rw [← hu] at hpw
    have hpl' : ((piBracket V).1 <<< AzInt.ofInt (-1)).toVal = some ((pl / 2 : ℝ) : EReal) := by
      have h := toVal_shiftLeft_of_toVal hpl (AzInt.ofInt (-1))
      rw [h, AzInt.toInt_ofInt, zpow_neg_one, div_eq_mul_inv]
    have hph' : ((piBracket V).2 <<< AzInt.ofInt (-1)).toVal = some ((ph / 2 : ℝ) : EReal) := by
      have h := toVal_shiftLeft_of_toVal hph (AzInt.ofInt (-1))
      rw [h, AzInt.toInt_ofInt, zpow_neg_one, div_eq_mul_inv]
    obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hpl' hup V
    obtain ⟨hi, hhi, hhi1, hhi2⟩ := subCeiling_abs hph' hlb V
    rw [← hu] at hlo2 hhi2
    have hinv : arctan a = π / 2 - arctan r := by
      have hra : r⁻¹ = a := by rw [hr, inv_inv]
      rw [← hra, arctan_inv_of_pos hr0]
    have hπ := pi_lt_four
    have hπ3 := pi_gt_three
    have hat1 : arctan r ≤ 1 := (arctan_le_self hr0.le).trans hr1
    have hup0 : 0 ≤ up := by linarith [arctan_nonneg.mpr hr0.le]
    have habs2 : |pl / 2 - up| ≤ 8 := by
      rw [abs_le]
      constructor <;> linarith
    have habs3 : |ph / 2 - lb| ≤ 8 := by
      rw [abs_le]
      constructor <;> linarith
    have m2 := mul_le_mul_of_nonneg_right habs2 hu0
    have m3 := mul_le_mul_of_nonneg_right habs3 hu0
    refine ⟨lo, hi, hlo, hhi, by linarith, by linarith, ?_⟩
    have hbig : 50 * u ≤ (1 / 2 : ℝ) ^ K := by
      have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
      have : (1 / 2 : ℝ) ^ K / 2 ^ 64 ≤ (1 / 2 : ℝ) ^ K / 50 := by
        apply div_le_div_of_nonneg_left hK0 (by norm_num) (by norm_num)
      linarith
    rw [hKw] at hbw hbig
    linarith

/-- `arctan q = ± arctan |q|` with the sign of the rational. -/
theorem arctan_toRat_eq (q : AzRat) (h0 : q.num ≠ 0) :
    arctan (AzRat.toRat q : ℝ)
      = (if q.sign then 1 else -1) * arctan |(AzRat.toRat q : ℝ)| := by
  have hs := toRat_sign_iff q h0
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  cases hsg : q.sign
  · have hneg : (AzRat.toRat q : ℝ) < 0 := by
      rcases lt_or_gt_of_ne hq0 with h | h
      · exact h
      · rw [hs.mpr h] at hsg; cases hsg
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [abs_of_neg hneg, arctan_neg]; ring
  · simp only [↓reduceIte]
    rw [abs_of_pos (hs.mp hsg), one_mul]

/-- `atanRatApprox` as a pair of `Roundable`s bracketing `arctan q`. -/
theorem atanRatApprox_spec (q : AzRat) (h0 : q.num ≠ 0) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (atanRatApprox q w).1 lv ∧ Rounds (atanRatApprox q w).2 hv ∧
      lv ≤ arctan (AzRat.toRat q : ℝ) ∧ arctan (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := atanRatBracket_spec q h0 w
  rw [arctan_toRat_eq q h0]
  simp only [atanRatApprox]
  cases q.sign with
  | true =>
    simp only [↓reduceIte, one_mul]
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    have hnlo : (-(atanRatBracket q w).2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(atanRatBracket q w).1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- `arctan q` is irrational for a nonzero rational `q`. -/
theorem irrational_arctan_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (arctan (AzRat.toRat q : ℝ)) :=
  irrational_arctan_rat fun h => coe_toRat_ne_zero_of_num_ne_zero q h0 (by rw [h, Rat.cast_zero])

/-- The Ziv certificate for `arctan q`, `q` a nonzero rational. -/
theorem atanRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (atanRatApprox q (w₀ * 2 ^ f)).1 (atanRatApprox q (w₀ * 2 ^ f)).2
      p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (atanRatApprox q) (irrational_arctan_toRat q h0)
    (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => atanRatApprox_spec q h0 w) w₀ hw₀

/-- The tiny-argument path of `arctan q` answers with the rounding of `arctan q`. -/
theorem atanTinyRat?_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (hT : atanTinyRat? q p mode = some r) :
    r = roundVal p mode (some ((arctan (AzRat.toRat q : ℝ) : ℝ) : EReal)) :=
  sinTinyRat?_eq_of arctan_neg (fun _ ha => arctan_lt_self ha)
    (fun a ha => by
      have h1 := sub_cube_div_three_le_arctan ha.le
      have h2 : 0 < a ^ 3 := by positivity
      linarith) q h0 hT

end Azurite.AzFloat
