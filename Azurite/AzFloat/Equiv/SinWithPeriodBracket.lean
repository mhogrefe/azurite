/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinWithPeriodBracket
import Azurite.AzFloat.Equiv.CosWithPeriodBracket
import Azurite.AzFloat.Equiv.SinRatBracket
import Azurite.Transcendental.NivenSin

/-!
# Equivalence: the brackets of `sin (2π x / u)`

`sinPeriodBracket_spec` (width `sinPeriodEps w`), `tendsto_sinPeriodEps`, `sinPeriodApprox_spec`,
`irrational_sin_two_pi_mul_toRat`, `sinPeriodApprox_isSome_exists` (the Ziv certificate from
Niven's theorem for the sine); the exact values `sin_two_pi_mul_toRat_of_den_eq_four`,
`sin_two_pi_mul_toRat_of_den_eq_twelve` through `num_eq_ofNat_iff`; the tiny path
`sinPeriodTinyBracket_spec`, `sinPeriodTiny?_cond`, `sinPeriodTiny?_eq`; `toVal_signedPow2`.
-/

namespace Azurite.AzFloat

/-! ### The bracket -/

/-- The width of `sinPeriodBracket r w`. -/
noncomputable def sinPeriodEps (w : ℕ) : ℝ :=
  sinEps (AzInt.ofInt 3) w + 152 * (1 / 2 : ℝ) ^ cosWork (AzInt.ofInt 3) w

/-- **`sinPeriodBracket` encloses `sin (2πr)`** for `0 ≤ r < 1`, at Ziv level `w ≥ 64`, with
width at most `sinPeriodEps w`. -/
theorem sinPeriodBracket_spec (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (sinPeriodBracket r w).1.toVal = some (lo : EReal) ∧
      (sinPeriodBracket r w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ)) ∧
      Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ)) ≤ hi ∧ hi - lo ≤ sinPeriodEps w := by
  set rv := ((AzRat.toRat r : ℚ) : ℝ) with hrv
  have hW64 : 64 ≤ cosWork (AzInt.ofInt 3) w := by unfold cosWork; omega
  have hεle := sinEps_le_one (AzInt.ofInt 3) hw
  simp only [sinPeriodBracket]
  set W := cosWork (AzInt.ofInt 3) w with hWdef
  have : NeZero W := ⟨by omega⟩
  set P := piBracket W with hP
  set a := (ofAzRatRound r W .Floor).1 with ha
  set t := (mulPrecRound (a <<< AzInt.ofInt 1) P.1 W .Floor).1 with ht
  set E := one <<< AzInt.ofInt (6 - W) with hE
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hW64
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  obtain ⟨lv, hv, hlv, hhv, hlv0, hlvπ, hπhv, hwid⟩ := piBracket_spec_width hW64
  rw [← hu] at hwid
  have hlv1 : 1 ≤ lv := by linarith
  have hlv4 : lv ≤ 4 := by linarith
  have hlv' : P.1.toVal = some (lv : EReal) := hlv
  obtain ⟨av, hav, hav1, hav2⟩ := ofAzRatRound_floor_abs r W
  rw [← hrv] at hav1
  rw [← hrv, ← hu, abs_of_nonneg hr0] at hav2
  have hav' : a.toVal = some (av : EReal) := hav
  have h2a := toVal_shiftLeft_one hav'
  obtain ⟨tv, htv, htv1, htv2⟩ := mulFloor_abs h2a hlv' W
  rw [← hu] at htv2
  have hrvu : rv * u ≤ u := by nlinarith
  have hav3 : av ≤ 1 := by linarith
  have hav4 : -2 * u ≤ av := by linarith
  have hprod : |2 * av * lv| ≤ 8 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hprodu := mul_le_mul_of_nonneg_right hprod hu0
  have havlv : av * lv < lv := by
    have : av < 1 := by linarith
    nlinarith
  have ht8 : |tv| < (2 : ℝ) ^ (AzInt.ofInt 3).toInt := by
    rw [AzInt.toInt_ofInt, show (2 : ℝ) ^ (3 : ℤ) = 8 by norm_num, abs_lt]
    constructor <;> nlinarith
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid'⟩ := sinBracket_spec htv ht8 hw
  have h64 : (1 : ℝ) * (2 : ℝ) ^ ((6 : ℤ) - (W : ℤ)) = 64 * u := by
    rw [one_mul, zpow_sub₀ two_ne_zero, zpow_natCast, hu, one_div_pow, div_eq_mul_inv]
    norm_num
  have hEv : E.toVal = some ((64 * u : ℝ) : EReal) := by
    rw [hE, toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt, h64]
  have herr0 : 0 ≤ 2 * Real.pi * rv - tv := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hlvπ.le), mul_nonneg hlv0 (sub_nonneg.mpr hav1)]
  have herr : 2 * Real.pi * rv - tv ≤ 48 * u := by
    have e1 : rv * (Real.pi - lv) ≤ 1 * (8 * u) :=
      mul_le_mul hr1.le (by linarith) (by linarith) zero_le_one
    have e2 : lv * (rv - av) ≤ 4 * (2 * u) :=
      mul_le_mul hlv4 (by linarith) (by linarith) (by norm_num)
    nlinarith
  have hz : |Real.sin (2 * Real.pi * rv) - Real.sin (|tv|)| ≤ 64 * u := by
    have h2π : 2 * Real.pi * rv = |2 * Real.pi * rv| := (abs_of_nonneg (by positivity)).symm
    refine (Real.abs_sin_sub_sin_le _ _).trans ?_
    rw [h2π]
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [abs_of_nonneg herr0]
    linarith
  have hB : IsEnclW (sinBracket t (AzInt.ofInt 3) w) (Real.sin (|tv|)) (sinEps (AzInt.ofInt 3) w) :=
    ⟨lo, hi, hlo, hhi, h1, h2, hwid'⟩
  have hC := hB.widen0 (M := 2) (isEncl0W_exact hEv (by positivity)) hz
    ((Real.abs_sin_le_one _).trans (by norm_num)) (by linarith) hεle (by norm_num) hW64
  obtain ⟨lo', hi', hlo', hhi', h1', h2', hwid''⟩ := hC
  rw [← hu] at hwid''
  refine ⟨lo', hi', hlo', hhi', h1', h2', hwid''.trans ?_⟩
  unfold sinPeriodEps
  rw [← hWdef, ← hu]
  linarith

/-- `sinPeriodEps w → 0` as `w → ∞`. -/
theorem tendsto_sinPeriodEps : Filter.Tendsto sinPeriodEps Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (cosWork (AzInt.ofInt 3)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by unfold cosWork; omega⟩
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp hc
  have h := (tendsto_sinEps (AzInt.ofInt 3)).add (h2.const_mul 152)
  simp only [mul_zero, add_zero] at h
  exact h

/-- `sinPeriodApprox` as a pair of `Roundable`s bracketing `± sin (2πr)`. -/
theorem sinPeriodApprox_spec (neg : Bool) (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sinPeriodApprox neg r w).1 lv ∧ Rounds (sinPeriodApprox neg r w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ)) ∧
      (if neg then -1 else 1) * Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ)) ≤ hv ∧
      hv - lv ≤ sinPeriodEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := sinPeriodBracket_spec r hr0 hr1 hw
  simp only [sinPeriodApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    have hnlo : (-(sinPeriodBracket r w).2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(sinPeriodBracket r w).1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- A sign does not change irrationality. -/
theorem irrational_sign_mul {v : ℝ} (h : Irrational v) (neg : Bool) :
    Irrational ((if neg then -1 else 1) * v) := by
  cases neg
  · simpa using h
  · simpa using h.neg

/-- `sin (2πr)` is irrational for an `AzRat` whose denominator is not `1, 2, 4, 12`. -/
theorem irrational_sin_two_pi_mul_toRat (r : AzRat) (h1 : r.den ≠ AzNat.ofNat 1)
    (h2 : r.den ≠ AzNat.ofNat 2) (h4 : r.den ≠ AzNat.ofNat 4) (h12 : r.den ≠ AzNat.ofNat 12) :
    Irrational (Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ))) :=
  irrational_sin_two_pi_mul_rat (den_toRat_ne h1) (den_toRat_ne h2) (den_toRat_ne h4)
    (den_toRat_ne h12)

/-- The Ziv certificate for `± sin (2πr)`, `r ∈ [0, 1)` with an irrational sine. -/
theorem sinPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1)
    (h1 : r.den ≠ AzNat.ofNat 1) (h2 : r.den ≠ AzNat.ofNat 2) (h4 : r.den ≠ AzNat.ofNat 4)
    (h12 : r.den ≠ AzNat.ofNat 12) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (sinPeriodApprox neg r (w₀ * 2 ^ f)).1
      (sinPeriodApprox neg r (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (sinPeriodApprox neg r)
    (irrational_sign_mul (irrational_sin_two_pi_mul_toRat r h1 h2 h4 h12) neg) sinPeriodEps
    tendsto_sinPeriodEps 64 (fun _ hw => sinPeriodApprox_spec neg r hr0 hr1 hw) w₀ hw₀

/-! ### The exact values -/

/-- The numerator of a nonnegative `AzRat` against a small natural. -/
theorem num_eq_ofNat_iff {r : AzRat} (h0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (n : ℕ) :
    r.num = AzNat.ofNat n ↔ (AzRat.toRat r).num = (n : ℤ) := by
  have hq : (0 : ℚ) ≤ AzRat.toRat r := by exact_mod_cast h0
  have hn := Rat.num_nonneg.mpr hq
  have hnum : (AzRat.toRat r).num
      = if r.sign then (r.num.toNat : ℤ) else -(r.num.toNat : ℤ) := rfl
  rw [hnum] at hn ⊢
  constructor
  · intro h
    rw [h, AzNat.toNat_ofNat] at hn ⊢
    split_ifs at hn ⊢ <;> omega
  · intro h
    apply AzNat.toNat_injective
    rw [AzNat.toNat_ofNat]
    split_ifs at hn h <;> omega

theorem sin_two_pi_mul_toRat_of_den_eq_four {r : AzRat} (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) (h : r.den = AzNat.ofNat 4) :
    Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ))
      = if r.num = AzNat.ofNat 1 then 1 else -1 := by
  have hq0 : (0 : ℚ) ≤ AzRat.toRat r := by exact_mod_cast hr0
  have hq1 : AzRat.toRat r < 1 := by exact_mod_cast hr1
  rw [sin_two_pi_mul_rat_of_den_eq_four (den_toRat_eq h) hq0 hq1]
  have h1 := num_eq_ofNat_iff hr0 1
  rw [Nat.cast_one] at h1
  by_cases hc : r.num = AzNat.ofNat 1
  · rw [ite_eq_left hc, ite_eq_left (h1.mp hc)]
  · rw [ite_eq_right hc, ite_eq_right fun h' => hc (h1.mpr h')]

theorem sin_two_pi_mul_toRat_of_den_eq_twelve {r : AzRat}
    (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1)
    (h : r.den = AzNat.ofNat 12) :
    Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ))
      = if r.num = AzNat.ofNat 1 ∨ r.num = AzNat.ofNat 5 then 1 / 2 else -1 / 2 := by
  have hq0 : (0 : ℚ) ≤ AzRat.toRat r := by exact_mod_cast hr0
  have hq1 : AzRat.toRat r < 1 := by exact_mod_cast hr1
  rw [sin_two_pi_mul_rat_of_den_eq_twelve (den_toRat_eq h) hq0 hq1]
  have h1 := num_eq_ofNat_iff hr0 1
  have h5 := num_eq_ofNat_iff hr0 5
  rw [Nat.cast_one] at h1
  rw [Nat.cast_ofNat] at h5
  have hiff := or_congr h1 h5
  by_cases hc : r.num = AzNat.ofNat 1 ∨ r.num = AzNat.ofNat 5
  · rw [ite_eq_left hc, ite_eq_left (hiff.mp hc)]
  · rw [ite_eq_right hc, ite_eq_right fun h' => hc (hiff.mpr h')]

theorem toVal_signedPow2 (pos : Bool) (k : ℤ) :
    (signedPow2 pos k).toVal
      = some (((if pos then 1 else -1) * (2 : ℝ) ^ k : ℝ) : EReal) := by
  have h1 : (one <<< AzInt.ofInt k).toVal = some (((2 : ℝ) ^ k : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt, one_mul]
  unfold signedPow2
  cases pos
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    rw [toVal_neg, h1, Option.map_some, EReal.coe_neg]
  · simp only [↓reduceIte, one_mul]
    exact h1

/-! ### Tiny arguments -/

/-- **The tiny bracket encloses `sin y`**, `y = 2π m 2^E / u < 2^e'`, `e' ≤ 0`. -/
theorem sinPeriodTinyBracket_spec {m u : AzNat} (hm : 0 < m.toNat) (hu : 0 < u.toNat)
    (E : AzInt) {e' : AzInt} (he : e'.toInt ≤ 0) {W : ℕ} (hW : 64 ≤ W)
    (hy : 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) < (2 : ℝ) ^ e'.toInt) :
    ∃ lo hi : ℝ, (sinPeriodTinyBracket m u E e' W).1.toVal = some (lo : EReal) ∧
      (sinPeriodTinyBracket m u E e' W).2.toVal = some (hi : EReal) ∧
      lo < Real.sin (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat)) ∧
      Real.sin (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat)) < hi := by
  have : NeZero W := ⟨by omega⟩
  set y := 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) with hydef
  simp only [sinPeriodTinyBracket]
  have hm' : (0 : ℝ) < m.toNat := by exact_mod_cast hm
  have hu' : (0 : ℝ) < u.toNat := by exact_mod_cast hu
  have hcv : ((AzRat.toRat (AzRat.ofAzNats m u) : ℚ) : ℝ) = (m.toNat : ℝ) / u.toNat := by
    rw [AzRat.toRat_ofAzNats]; push_cast; rfl
  have hpi := Real.pi_pos
  obtain ⟨lv, hv, hlv, hhv, hlv0, hlvπ, hπhv, -⟩ := piBracket_spec_width hW
  obtain ⟨cl, hcl, hcl1, -⟩ := ofAzRatRound_floor_abs (AzRat.ofAzNats m u) W
  obtain ⟨ch, hch, hch1, -⟩ := ofAzRatRound_ceiling_abs (AzRat.ofAzNats m u) W
  rw [hcv] at hcl1 hch1
  set cv := (m.toNat : ℝ) / u.toNat with hcvdef
  have hcv0 : 0 < cv := by positivity
  obtain ⟨a1, ha1, ha1le, -⟩ := mulFloor_abs hcl hlv W
  obtain ⟨a2, ha2, ha2ge, -⟩ := mulCeiling_abs hch hhv W
  have hylo := toVal_shiftLeft_of_toVal ha1 (E + AzInt.ofInt 1)
  have hyhi := toVal_shiftLeft_of_toVal ha2 (E + AzInt.ofInt 1)
  have hT : (2 : ℝ) ^ (E + AzInt.ofInt 1).toInt = (2 : ℝ) ^ E.toInt * 2 := by
    rw [AzInt.toInt_add, AzInt.toInt_ofInt, zpow_add₀ two_ne_zero, zpow_one]
  set T := (2 : ℝ) ^ (E + AzInt.ofInt 1).toInt with hTdef
  have hT0 : 0 < T := by positivity
  set t := (2 : ℝ) ^ e'.toInt with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) he
  have hd := toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal hyhi e') e'
  obtain ⟨lo, hlo, hlo1, -⟩ := subFloor_abs hylo hd W
  have hyeq : y = cv * Real.pi * T := by
    rw [hydef, hcvdef, hT]; ring
  have hy0 : 0 < y := by rw [hyeq]; positivity
  have h1 : a1 * T ≤ y := by
    rw [hyeq]
    refine mul_le_mul_of_nonneg_right ?_ hT0.le
    calc a1 ≤ cl * lv := ha1le
      _ ≤ cv * lv := mul_le_mul_of_nonneg_right hcl1 hlv0
      _ ≤ cv * Real.pi := mul_le_mul_of_nonneg_left hlvπ.le hcv0.le
  have h2 : y ≤ a2 * T := by
    rw [hyeq]
    refine mul_le_mul_of_nonneg_right ?_ hT0.le
    calc cv * Real.pi ≤ ch * Real.pi := mul_le_mul_of_nonneg_right hch1 hpi.le
      _ ≤ ch * hv := mul_le_mul_of_nonneg_left hπhv (by linarith)
      _ ≤ a2 := ha2ge
  have hs1 := Real.sin_lt hy0
  have hs2 := Real.sin_gt_sub_cube hy0
  have hcube : y ^ 3 ≤ a2 * T * t * t := by
    have e1 : y * y ≤ t * t := mul_le_mul hy.le hy.le hy0.le ht0.le
    calc y ^ 3 = y * (y * y) := by ring
      _ ≤ a2 * T * (t * t) := mul_le_mul h2 e1 (by positivity) (by linarith)
      _ = a2 * T * t * t := by ring
  have hy3 : 0 < y ^ 3 := by positivity
  exact ⟨lo, a2 * T, hlo, hyhi, by linarith, by linarith⟩

theorem sinPeriodTiny?_cond {neg : Bool} {m u : AzNat} {E e' : AzInt} {p : ℕ}
    {mode : RoundingMode} {r : AzFloat × Ordering}
    (h : sinPeriodTiny? neg m u E e' p mode = some r) :
    e'.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e'.abs.toNat := by
  unfold sinPeriodTiny? at h
  by_contra hc
  rw [ite_eq_right hc] at h
  cases h

/-- The tiny-argument path answers with the rounding of `± sin y`. -/
theorem sinPeriodTiny?_eq {neg : Bool} {m u : AzNat} (hm : 0 < m.toNat) (hu : 0 < u.toNat)
    {E e' : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode} {r : AzFloat × Ordering}
    (hy : 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) < (2 : ℝ) ^ e'.toInt)
    (hirr : Irrational
      (Real.sin (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat))))
    (hT : sinPeriodTiny? neg m u E e' p mode = some r) :
    r = roundVal p mode (some (((if neg then -1 else 1)
      * Real.sin (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat)) : ℝ) : EReal)) := by
  have hc := sinPeriodTiny?_cond hT
  have htoInt : e'.toInt = if e'.sign then (e'.abs.toNat : ℤ) else -(e'.abs.toNat : ℤ) := rfl
  rw [hc.1] at htoInt
  simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := sinPeriodTinyBracket_spec hm hu E (e' := e')
    (by omega) (W := p + zivGuardBits + 8) (by unfold zivGuardBits; omega) hy
  unfold sinPeriodTiny? at hT
  rw [ite_eq_left hc] at hT
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hT ⊢
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    rw [one_mul]
    exact roundingPossible_eq' p mode hR1 hR2 h1.le h2.le
      (Or.inr (not_mem_floatSet_of_irrational p hirr)) hT
  | true =>
    simp only [↓reduceIte] at hT ⊢
    have hnlo : (-(sinPeriodTinyBracket m u E e' (p + zivGuardBits + 8)).2).toVal
        = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(sinPeriodTinyBracket m u E e' (p + zivGuardBits + 8)).1).toVal
        = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    rw [neg_one_mul]
    exact roundingPossible_eq' p mode hR3 hR4 (by linarith) (by linarith)
      (Or.inr (not_mem_floatSet_of_irrational p hirr.neg)) hT

end Azurite.AzFloat
