/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanWithPeriodBracket
import Azurite.AzFloat.Equiv.SinCosWithPeriodBracket
import Azurite.AzFloat.Equiv.TanBracket
import Azurite.Transcendental.NivenTan

/-!
# Equivalence: the brackets of `tan (2π x / u)`

* `Spec.tanPole θ`: the extended-real tangent of IEEE 754 `tanPi` — `tan θ`, and at a pole
  (`cos θ = 0`) `+∞` or `−∞` with the sign of `sin θ`; `tanPole_pi_mul_int_add_half` (IEEE's
  rule: `tanPi (n + 1/2)` is `+∞` for even `n`, `−∞` for odd `n`), `tanPole_neg`,
  `tanPole_add_nat_mul_two_pi`, `tanPole_two_pi_div` (the reduction to the fractional part).
* `tanPeriodBracket_width`, `tanPeriodApprox_valid_or_none`, `tanPeriodApprox_isSome_exists`
  (the certificate from Niven's theorem for the tangent), the exact values at the denominators
  `8` and `4`.
* `tanPeriodTinyBracket_spec`, `tanPeriodTiny?_eq`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- The tangent with IEEE 754 poles: `tan θ` where `cos θ ≠ 0`, and at a pole `+∞` if
`sin θ > 0` (`θ = π/2 + 2kπ`), `−∞` otherwise. -/
noncomputable def tanPole (θ : ℝ) : EReal :=
  if Real.cos θ = 0 then (if 0 < Real.sin θ then ⊤ else ⊥) else ((Real.tan θ : ℝ) : EReal)

theorem tanPole_of_cos_ne_zero {θ : ℝ} (h : Real.cos θ ≠ 0) :
    tanPole θ = ((Real.tan θ : ℝ) : EReal) := by
  unfold tanPole
  rw [ite_eq_right h]

theorem tanPole_add_nat_mul_two_pi (θ : ℝ) (k : ℕ) :
    tanPole (θ + k * (2 * Real.pi)) = tanPole θ := by
  unfold tanPole
  rw [Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi, Real.tan_eq_sin_div_cos,
    Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi, ← Real.tan_eq_sin_div_cos]

theorem tanPole_neg (θ : ℝ) : tanPole (-θ) = -tanPole θ := by
  unfold tanPole
  rw [Real.cos_neg, Real.sin_neg, Real.tan_neg]
  by_cases hc : Real.cos θ = 0
  · rw [ite_eq_left hc, ite_eq_left hc]
    have hs : Real.sin θ ≠ 0 := fun hs => by
      have := Real.sin_sq_add_cos_sq θ
      rw [hs, hc] at this
      norm_num at this
    rcases lt_or_gt_of_ne hs with h | h
    · rw [ite_eq_left (by linarith : 0 < -Real.sin θ), ite_eq_right (not_lt.mpr h.le)]
      rfl
    · rw [ite_eq_right (by linarith : ¬ 0 < -Real.sin θ), ite_eq_left h]
      rfl
  · rw [ite_eq_right hc, ite_eq_right hc, EReal.coe_neg]

/-- IEEE 754: `tanPi (n + 1/2)` is `+∞` for an even integer `n` and `−∞` for an odd one. -/
theorem tanPole_pi_mul_int_add_half (n : ℤ) :
    tanPole (Real.pi * (n + 1 / 2)) = if Even n then ⊤ else ⊥ := by
  have hθ : Real.pi * ((n : ℝ) + 1 / 2) = Real.pi / 2 + n * Real.pi := by ring
  unfold tanPole
  rw [hθ, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero, ite_eq_left rfl,
    Real.sin_add_int_mul_pi, Real.sin_pi_div_two, mul_one]
  by_cases he : Even n
  · rw [ite_eq_left he, he.neg_one_zpow, ite_eq_left (by norm_num : (0 : ℝ) < 1)]
  · rw [ite_eq_right he, (Int.not_even_iff_odd.mp he).neg_one_zpow,
      ite_eq_right (by norm_num : ¬ (0 : ℝ) < -1)]

/-- The reduction of `tanPole (2π x / U)` to the fractional part `ρ` of `|x| / U`. -/
theorem tanPole_two_pi_div {xv U ρ : ℝ} {k : ℕ} (hk : |xv| / U = k + ρ) :
    tanPole (2 * Real.pi * xv / U)
      = if xv < 0 then -tanPole (2 * Real.pi * ρ) else tanPole (2 * Real.pi * ρ) := by
  have habs : tanPole (2 * Real.pi * (|xv| / U)) = tanPole (2 * Real.pi * ρ) := by
    rw [hk, show 2 * Real.pi * ((k : ℝ) + ρ) = 2 * Real.pi * ρ + k * (2 * Real.pi) by ring,
      tanPole_add_nat_mul_two_pi]
  split_ifs with hx
  · rw [← habs, abs_of_neg hx, ← tanPole_neg]
    congr 1
    ring
  · rw [← habs, abs_of_nonneg (not_lt.mp hx)]
    congr 1
    ring

end Spec

/-! ### The bracket -/

/-- `sinPeriodEps w ≤ 1` from `w = 64` on. -/
theorem sinPeriodEps_le_one {w : ℕ} (hw : 64 ≤ w) : sinPeriodEps w ≤ 1 := by
  have hW : 64 ≤ cosWork (AzInt.ofInt 3) w := by unfold cosWork; omega
  have h3 := half_pow_small hW
  have hV : 64 ≤ w + 12 := by omega
  have h := add_nine_mul_half_pow_le hV
  have h4 := half_pow_small hV
  have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 12) := by positivity
  have : (73 : ℝ) * (1 / 2 : ℝ) ^ 64 ≤ 1 / 10 ^ 16 := by norm_num
  unfold sinPeriodEps sinEps sinCosEps sinCosEpsW
  linarith

theorem isEnclW_sinCosPeriodBracket (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (sinCosPeriodBracket r w).1 (Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ)))
        (sinPeriodEps w) ∧
      IsEnclW (sinCosPeriodBracket r w).2 (Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)))
        (cosPeriodEps w) := by
  rw [sinCosPeriodBracket_fst, sinCosPeriodBracket_snd]
  exact ⟨sinPeriodBracket_spec r hr0 hr1 hw, cosPeriodBracket_spec r hr0 hr1 hw⟩

/-- The width of `tanPeriodBracket` once the bracket of the cosine is at most half of
`c = |cos (2πr)|`. -/
noncomputable def tanPeriodEps (c : ℝ) (w : ℕ) : ℝ :=
  (sinPeriodEps w + 2 * cosPeriodEps w / (c / 2) + 8 * (1 / 2 : ℝ) ^ (w + 12)) / (c / 2)

/-- `tanPeriodEps c w → 0` as `w → ∞`. -/
theorem tendsto_tanPeriodEps (c : ℝ) :
    Filter.Tendsto (tanPeriodEps c) Filter.atTop (nhds 0) := by
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp (Filter.tendsto_add_atTop_nat 12)
  have h := ((tendsto_sinPeriodEps.add (tendsto_cosPeriodEps.const_mul (2 / (c / 2)))).add
    (h2.const_mul 8)).div_const (c / 2)
  simp only [mul_zero, add_zero, zero_div] at h
  refine h.congr fun w => ?_
  simp only [Function.comp, tanPeriodEps]
  ring

/-- **`tanPeriodBracket` encloses `tan (2πr)`** with width at most `tanPeriodEps |cos (2πr)| w`,
as soon as `cosPeriodEps w ≤ |cos (2πr)| / 2`. -/
theorem tanPeriodBracket_width (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ} (hw : 64 ≤ w)
    (hc0 : 0 < |Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))|)
    (hc : cosPeriodEps w ≤ |Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))| / 2) :
    IsEnclW (tanPeriodBracket r w) (Real.tan (2 * Real.pi * (AzRat.toRat r : ℝ)))
      (tanPeriodEps |Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))| w) := by
  obtain ⟨hS, hC⟩ := isEnclW_sinCosPeriodBracket r hr0 hr1 hw
  rw [Real.tan_eq_sin_div_cos]
  exact tanOfSinCos_width hS hC (Real.abs_sin_le_one _) (sinPeriodEps_le_one hw) (by omega) hc0 hc

/-- At every level `w ≥ 64` the bracket of `tanPeriodApprox neg` encloses `± tan (2πr)` or is
rejected by `roundingPossible`. -/
theorem tanPeriodApprox_valid_or_none (neg : Bool) (r : AzRat)
    (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ}
    (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (tanPeriodApprox neg r w).1 lv ∧ Rounds (tanPeriodApprox neg r w).2 hv ∧
        lv ≤ (if neg then -1 else 1) * Real.tan (2 * Real.pi * (AzRat.toRat r : ℝ)) ∧
        (if neg then -1 else 1) * Real.tan (2 * Real.pi * (AzRat.toRat r : ℝ)) ≤ hv) ∨
      roundingPossible (tanPeriodApprox neg r w).1 (tanPeriodApprox neg r w).2 p mode = none := by
  obtain ⟨hS, hC⟩ := isEnclW_sinCosPeriodBracket r hr0 hr1 hw
  rw [Real.tan_eq_sin_div_cos]
  exact tanOfSinCos_valid_or_none neg hS hC (Real.abs_sin_le_one _) (sinPeriodEps_le_one hw)
    (by omega) p mode

/-- `tan (2πr)` is irrational for an `AzRat` whose denominator is not `1, 2, 4, 8`. -/
theorem irrational_tan_two_pi_mul_toRat (r : AzRat) (h1 : r.den ≠ AzNat.ofNat 1)
    (h2 : r.den ≠ AzNat.ofNat 2) (h4 : r.den ≠ AzNat.ofNat 4) (h8 : r.den ≠ AzNat.ofNat 8) :
    Irrational (Real.tan (2 * Real.pi * (AzRat.toRat r : ℝ))) :=
  irrational_tan_two_pi_mul_rat (den_toRat_ne h1) (den_toRat_ne h2) (den_toRat_ne h4)
    (den_toRat_ne h8)

/-- `cos (2πr) ≠ 0` unless the denominator of `r` is `4`. -/
theorem cos_two_pi_mul_toRat_ne_zero (r : AzRat) (h4 : r.den ≠ AzNat.ofNat 4) :
    Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) ≠ 0 := fun h =>
  den_toRat_ne h4 (den_eq_four_of_cos_two_pi_mul_rat_eq_zero h)

/-- The Ziv certificate for `± tan (2πr)`, `r ∈ [0, 1)` with an irrational tangent. -/
theorem tanPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1)
    (h1 : r.den ≠ AzNat.ofNat 1) (h2 : r.den ≠ AzNat.ofNat 2) (h4 : r.den ≠ AzNat.ofNat 4)
    (h8 : r.den ≠ AzNat.ofNat 8) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (tanPeriodApprox neg r (w₀ * 2 ^ f)).1
      (tanPeriodApprox neg r (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hc0 : 0 < |Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))| :=
    abs_pos.mpr (cos_two_pi_mul_toRat_ne_zero r h4)
  obtain ⟨W₁, hW₁⟩ := (tendsto_cosPeriodEps.eventually
    (gt_mem_nhds (half_pos hc0))).exists_forall_of_atTop
  exact exists_isSome_of_irrational_threshold p mode (tanPeriodApprox neg r)
    (irrational_sign_mul (irrational_tan_two_pi_mul_toRat r h1 h2 h4 h8) neg)
    (tanPeriodEps |Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))|) (tendsto_tanPeriodEps _)
    (max 64 W₁)
    (fun w hw => negSwapApprox_of_isEnclW neg (tanPeriodBracket_width r hr0 hr1
      (le_of_max_le_left hw) hc0 (hW₁ w (le_of_max_le_right hw)).le)) w₀ hw₀

/-! ### The exact values -/

theorem tan_two_pi_mul_toRat_of_den_eq_eight {r : AzRat} (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) (h : r.den = AzNat.ofNat 8) :
    Real.tan (2 * Real.pi * (AzRat.toRat r : ℝ))
      = if r.num = AzNat.ofNat 1 ∨ r.num = AzNat.ofNat 5 then 1 else -1 := by
  have hq0 : (0 : ℚ) ≤ AzRat.toRat r := by exact_mod_cast hr0
  have hq1 : AzRat.toRat r < 1 := by exact_mod_cast hr1
  rw [tan_two_pi_mul_rat_of_den_eq_eight (den_toRat_eq h) hq0 hq1]
  have h1 := num_eq_ofNat_iff hr0 1
  have h5 := num_eq_ofNat_iff hr0 5
  rw [Nat.cast_one] at h1
  rw [Nat.cast_ofNat] at h5
  have hiff := or_congr h1 h5
  by_cases hc : r.num = AzNat.ofNat 1 ∨ r.num = AzNat.ofNat 5
  · rw [ite_eq_left hc, ite_eq_left (hiff.mp hc)]
  · rw [ite_eq_right hc, ite_eq_right fun h' => hc (hiff.mpr h')]

/-- At the denominator `4` the tangent has a pole: `+∞` at `r = 1/4`, `−∞` at `r = 3/4`. -/
theorem tanPole_two_pi_mul_toRat_of_den_eq_four {r : AzRat}
    (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1)
    (h : r.den = AzNat.ofNat 4) :
    Spec.tanPole (2 * Real.pi * (AzRat.toRat r : ℝ))
      = if r.num = AzNat.ofNat 1 then ⊤ else ⊥ := by
  unfold Spec.tanPole
  rw [ite_eq_left (cos_two_pi_mul_rat_of_den_eq_four (den_toRat_eq h)),
    sin_two_pi_mul_toRat_of_den_eq_four hr0 hr1 h]
  by_cases hc : r.num = AzNat.ofNat 1
  · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left (by norm_num : (0 : ℝ) < 1)]
  · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right (by norm_num : ¬ (0 : ℝ) < -1)]

/-! ### Tiny arguments -/

/-- **The tiny bracket encloses `tan y`**, `y = 2π m 2^E / u < 2^e'`, `e' ≤ 0`. -/
theorem tanPeriodTinyBracket_spec {m u : AzNat} (hm : 0 < m.toNat) (hu : 0 < u.toNat)
    (E : AzInt) {e' : AzInt} (he : e'.toInt ≤ 0) {W : ℕ} (hW : 64 ≤ W)
    (hy : 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) < (2 : ℝ) ^ e'.toInt) :
    ∃ lo hi : ℝ, (tanPeriodTinyBracket m u E e' W).1.toVal = some (lo : EReal) ∧
      (tanPeriodTinyBracket m u E e' W).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.tan (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat)) ∧
      Real.tan (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat)) ≤ hi := by
  have : NeZero W := ⟨by omega⟩
  set y := 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) with hydef
  simp only [tanPeriodTinyBracket]
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
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hyhi hd W
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
  obtain ⟨hs1, hs2⟩ := tan_bounds_of_small hy0 (hy.le.trans ht1)
  have hcube : y ^ 3 ≤ a2 * T * t * t := by
    have e1 : y * y ≤ t * t := mul_le_mul hy.le hy.le hy0.le ht0.le
    calc y ^ 3 = y * (y * y) := by ring
      _ ≤ a2 * T * (t * t) := mul_le_mul h2 e1 (by positivity) (by linarith)
      _ = a2 * T * t * t := by ring
  exact ⟨a1 * T, hi, hylo, hhi, by linarith, by linarith⟩

theorem tanPeriodTiny?_cond {neg : Bool} {m u : AzNat} {E e' : AzInt} {p : ℕ}
    {mode : RoundingMode} {r : AzFloat × Ordering}
    (h : tanPeriodTiny? neg m u E e' p mode = some r) :
    e'.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e'.abs.toNat := by
  unfold tanPeriodTiny? at h
  by_contra hc
  rw [ite_eq_right hc] at h
  cases h

/-- The tiny-argument path answers with the rounding of `± tan y`. -/
theorem tanPeriodTiny?_eq {neg : Bool} {m u : AzNat} (hm : 0 < m.toNat) (hu : 0 < u.toNat)
    {E e' : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode} {r : AzFloat × Ordering}
    (hy : 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) < (2 : ℝ) ^ e'.toInt)
    (hirr : Irrational
      (Real.tan (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat))))
    (hT : tanPeriodTiny? neg m u E e' p mode = some r) :
    r = roundVal p mode (some (((if neg then -1 else 1)
      * Real.tan (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat)) : ℝ) : EReal)) := by
  have hc := tanPeriodTiny?_cond hT
  have htoInt : e'.toInt = if e'.sign then (e'.abs.toNat : ℤ) else -(e'.abs.toNat : ℤ) := rfl
  rw [hc.1] at htoInt
  simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := tanPeriodTinyBracket_spec hm hu E (e' := e')
    (by omega) (W := p + zivGuardBits + 8) (by unfold zivGuardBits; omega) hy
  unfold tanPeriodTiny? at hT
  rw [ite_eq_left hc] at hT
  obtain ⟨lv, hv, hl, hh, a, b, -⟩ := negSwapApprox_of_isEnclW neg
    (b := tanPeriodTinyBracket m u E e' (p + zivGuardBits + 8)) (W := hi - lo)
    ⟨lo, hi, hlo, hhi, h1, h2, le_rfl⟩
  exact roundingPossible_eq' p mode hl hh a b
    (Or.inr (not_mem_floatSet_of_irrational p (irrational_sign_mul hirr neg))) hT

end Azurite.AzFloat
