/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SechBracket
import Azurite.AzFloat.Equiv.CoshBracket

/-!
# Equivalence: the bracket of `sech x`

`sechOfCosh_spec` (the reciprocal of an enclosure of `C ≥ 1`, width at most `δ + 4·2^(−W)`),
`sechBracket_spec`, `sechApprox_spec`, `irrational_sech_of_toVal`, `sechApprox_isSome_exists`
(the Ziv certificate), the rational versions `sechRatBracket_spec`, `sechRatApprox_spec`,
`irrational_sech_toRat`, `sechRatApprox_isSome_exists`, and the tiny-exponent path
`sechNearOne?_eq`, `sechTiny_eq`, `sechRatTiny_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- **`sechOfCosh` encloses `1/C`** for an enclosure of `C ≥ 1` of width at most `δ`. -/
theorem sechOfCosh_spec {c : Encl} {C δ : ℝ} (hc : IsEnclW c C δ) (hC1 : 1 ≤ C) {W : ℕ}
    (hW : 1 ≤ W) : IsEnclW (sechOfCosh c W) C⁻¹ (δ + 4 * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := hc
  have hl := toVal_maxOf hlo toVal_one'
  have hl1 : 1 ≤ max lo 1 := le_max_right _ _
  have hlC : max lo 1 ≤ C := max_le h1 hC1
  have hlo' : lo ≤ max lo 1 := le_max_left _ _
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hhi1 : 1 ≤ hi := hC1.trans h2
  obtain ⟨q1, hq1, hq1a, hq1b⟩ := divFloor_abs toVal_one' hhi (by linarith : hi ≠ 0) W
  obtain ⟨q2, hq2, hq2a, hq2b⟩ := divCeiling_abs toVal_one' hl (by linarith : max lo 1 ≠ 0) W
  have hil0 : 0 < 1 / max lo 1 := by positivity
  have hih0 : 0 < 1 / hi := by positivity
  rw [abs_of_pos hih0] at hq1b
  rw [abs_of_pos hil0] at hq2b
  have hil1 : 1 / max lo 1 ≤ 1 := by rw [div_le_one (by linarith)]; exact hl1
  have hih1 : 1 / hi ≤ 1 := by rw [div_le_one (by linarith)]; exact hhi1
  have hCi : C⁻¹ = 1 / C := (one_div C).symm
  have hiC : 1 / hi ≤ 1 / C := one_div_le_one_div_of_le (by linarith) h2
  have hCl : 1 / C ≤ 1 / max lo 1 := one_div_le_one_div_of_le (by linarith) hlC
  have hm := add_inv_mono hl1 (hlC.trans h2)
  have e1 : 1 / hi * (1 / 2 : ℝ) ^ W ≤ 1 * (1 / 2 : ℝ) ^ W :=
    mul_le_mul_of_nonneg_right hih1 hη0
  have e2 : 1 / max lo 1 * (1 / 2 : ℝ) ^ W ≤ 1 * (1 / 2 : ℝ) ^ W :=
    mul_le_mul_of_nonneg_right hil1 hη0
  rw [hCi]
  exact ⟨q1, q2, hq1, hq2, by linarith, by linarith, by linarith⟩

/-- The width bound of `sechBracket`. -/
noncomputable def sechEps (xv : ℝ) (w : ℕ) : ℝ :=
  coshWidth (Real.exp |xv|) (expEps |xv| w) w + 4 * (1 / 2 : ℝ) ^ w

theorem tendsto_sechEps (xv : ℝ) : Filter.Tendsto (sechEps xv) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := (tendsto_coshWidth (Real.exp |xv|) (tendsto_expEps |xv|)).add (hp.const_mul 4)
  have h0 : (0 + 4 * 0 : ℝ) = 0 := by ring
  rw [h0] at h
  exact h

/-- **`sechBracket x e w` encloses `sech x`** for a float `|x| < 2^e`. -/
theorem sechBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (e : AzInt)
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (sechBracket x e w) (Real.cosh xv)⁻¹ (sechEps xv w) := by
  have h := sechOfCosh_spec (coshBracket_spec hx e hxe hw) (one_le_cosh xv) (W := w + 16)
    (by omega)
  refine h.mono ?_
  unfold sechEps
  have hpw : (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

/-- `sechApprox` as a pair of `Roundable`s bracketing `sech x`. -/
theorem sechApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {e : AzInt}
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sechApprox x e w).1 lv ∧ Rounds (sechApprox x e w).2 hv ∧
      lv ≤ (Real.cosh xv)⁻¹ ∧ (Real.cosh xv)⁻¹ ≤ hv ∧ hv - lv ≤ sechEps xv w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := sechBracket_spec hx e hxe hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `sech x` is irrational for a finite float `x ≠ 0`. -/
theorem irrational_sech_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.cosh xv)⁻¹ :=
  (irrational_cosh_of_toVal hx hx0).inv

/-- The Ziv certificate for `sech x`, `x` a finite nonzero float. -/
theorem sechApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {e : AzInt}
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (sechApprox x e (w₀ * 2 ^ f)).1
      (sechApprox x e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (sechApprox x e)
    (irrational_sech_of_toVal hx hx0) (sechEps xv) (tendsto_sechEps xv) 64
    (fun _ hw => sechApprox_spec hx hxe hw) w₀ hw₀

/-! ### The tiny-exponent path -/

/-- The tiny-exponent test of the exponential answers with the rounding of `sech x`, for
`0 < |x| < t` and `t²/2 ≤ 2^E`: `sech x = exp v` with `−x²/2 ≤ v < 0`. -/
theorem sechNearOne?_eq {E : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {x t : ℝ} (hx0 : x ≠ 0) (ht : |x| < t)
    (hE : t * t / 2 ≤ (2 : ℝ) ^ E.toInt) (h : expNearOne? false E p mode = some r) :
    r = roundVal p mode (some (((Real.cosh x)⁻¹ : ℝ) : EReal)) := by
  have hc1 : 1 < Real.cosh x := one_lt_cosh.mpr hx0
  have hc0 : 0 < Real.cosh x := by linarith
  have hv0 : 0 < Real.log (Real.cosh x) := Real.log_pos hc1
  have hvle : Real.log (Real.cosh x) ≤ x ^ 2 / 2 := by
    have := Real.log_le_log hc0 (cosh_le_exp_half_sq x)
    rwa [Real.log_exp] at this
  have hsq : x ^ 2 < t * t := by
    have h0 := abs_nonneg x
    have : |x| * |x| < t * t := mul_self_lt_mul_self h0 ht
    rwa [← sq, sq_abs] at this
  have hlt : |-Real.log (Real.cosh x)| < (2 : ℝ) ^ E.toInt := by
    rw [abs_neg, abs_of_pos hv0]
    linarith
  have := expNearOne?_eq hlt (neg_ne_zero.mpr hv0.ne') (by simp [hv0.le]) h
  rwa [Real.exp_neg, Real.exp_log hc0] at this

/-- The tiny-exponent path of `sech x` for a float `0 < |x| < 2^e`. -/
theorem sechTiny_eq {e : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {x : ℝ} (hx0 : x ≠ 0) (hxe : |x| < (2 : ℝ) ^ e.toInt)
    (h : expNearOne? false (coshTinyExp e) p mode = some r) :
    r = roundVal p mode (some (((Real.cosh x)⁻¹ : ℝ) : EReal)) :=
  sechNearOne?_eq hx0 hxe (two_zpow_coshTinyExp e).ge h

/-- The tiny-exponent path of `sech q` for a rational `q ≠ 0`. -/
theorem sechRatTiny_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (h : expNearOne? false (coshRatTinyExp q) p mode = some r) :
    r = roundVal p mode (some (((Real.cosh (AzRat.toRat q : ℝ))⁻¹ : ℝ) : EReal)) := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have hlt := abs_toRat_lt_two_zpow q
  have he : ((ratExpBound q + AzInt.ofInt (-1)).toInt) = (ratExpBound q).toInt - 1 := by
    rw [AzInt.toInt_add, AzInt.toInt_ofInt]
    ring
  rw [← he] at hlt
  exact sechTiny_eq hq0 hlt h

/-! ### The rational bracket -/

/-- The width bound of `sechRatBracket`. -/
noncomputable def sechRatEps (q : AzRat) (w : ℕ) : ℝ := coshRatEps q w + 4 * (1 / 2 : ℝ) ^ w

theorem tendsto_sechRatEps (q : AzRat) :
    Filter.Tendsto (sechRatEps q) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := (tendsto_coshRatEps q).add (hp.const_mul 4)
  have h0 : (0 + 4 * 0 : ℝ) = 0 := by ring
  rw [h0] at h
  exact h

/-- **`sechRatBracket q w` encloses `sech q`** for a rational `q`. -/
theorem sechRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) :
    IsEnclW (sechRatBracket q w) (Real.cosh ((AzRat.toRat q : ℚ) : ℝ))⁻¹ (sechRatEps q w) := by
  have h := sechOfCosh_spec (coshRatBracket_spec hw q) (one_le_cosh _) (W := w + 16) (by omega)
  refine h.mono ?_
  unfold sechRatEps
  have hpw : (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

/-- `sechRatApprox` as a pair of `Roundable`s bracketing `sech q`. -/
theorem sechRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) :
    ∃ lv hv : ℝ, Rounds (sechRatApprox q w).1 lv ∧ Rounds (sechRatApprox q w).2 hv ∧
      lv ≤ (Real.cosh (AzRat.toRat q : ℝ))⁻¹ ∧ (Real.cosh (AzRat.toRat q : ℝ))⁻¹ ≤ hv ∧
      hv - lv ≤ sechRatEps q w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := sechRatBracket_spec hw q
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `sech q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_sech_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.cosh (AzRat.toRat q : ℝ))⁻¹ :=
  (irrational_cosh_toRat q h0).inv

/-- The Ziv certificate for `sech q`. -/
theorem sechRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (sechRatApprox q (w₀ * 2 ^ f)).1
      (sechRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (sechRatApprox q) (irrational_sech_toRat q h0)
    (sechRatEps q) (tendsto_sechRatEps q) 64 (fun _ hw => sechRatApprox_spec hw q) w₀ hw₀

end Azurite.AzFloat
