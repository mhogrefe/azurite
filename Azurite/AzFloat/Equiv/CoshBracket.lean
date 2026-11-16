/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CoshBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.Equiv.PowRatBracket
import Azurite.Transcendental.Sinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Equivalence: the brackets of `cosh x` and `cosh q`

`coshStep_bounds` (the real arithmetic of the outward rounding), `coshOfExp_spec`,
`coshOfExp_width` (width at most `coshWidth`, which tends to `0`: `tendsto_coshWidth`),
`coshBracket_spec`, `coshApprox_spec`, `irrational_cosh_of_toVal`, `coshApprox_isSome_exists`
(the Ziv certificate), the rational versions `coshRatBracket_spec`, `coshRatApprox_spec`,
`irrational_cosh_toRat`, `coshRatApprox_isSome_exists`, and the tiny-exponent path
`coshNearOne?_eq`, `coshTiny_eq`, `coshRatTiny_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- `t + 1/t` is increasing on `t ≥ 1`. -/
theorem add_inv_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : a + 1 / a ≤ b + 1 / b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h : 1 / a - 1 / b = (b - a) / (a * b) := by
    field_simp
  have h1 : (b - a) / (a * b) ≤ b - a := div_le_self (by linarith) (by nlinarith)
  linarith

/-- The real arithmetic of `coshOfExp`: the enclosure and its width. -/
theorem coshStep_bounds {X l h q1 s1 q2 s2 η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8)
    (hl1 : 1 ≤ l) (hlX : l ≤ X) (hXh : X ≤ h)
    (hq1a : q1 ≤ 1 / l) (hq1b : 1 / l ≤ q1 + 2 * |1 / l| * η)
    (hs1a : s1 ≤ l + q1) (hs1b : l + q1 ≤ s1 + 2 * |l + q1| * η)
    (hq2a : 1 / h ≤ q2) (hq2b : q2 ≤ 1 / h + 2 * |1 / h| * η)
    (hs2a : h + q2 ≤ s2) (hs2b : s2 ≤ h + q2 + 2 * |h + q2| * η) :
    s1 ≤ X + 1 / X ∧ X + 1 / X ≤ s2 ∧ s2 - s1 ≤ (h - l) + η * (4 * h + 10) := by
  have hl0 : 0 < l := by linarith
  have hh0 : 0 < h := by linarith
  have hil0 : 0 < 1 / l := by positivity
  have hih0 : 0 < 1 / h := by positivity
  have hil1 : 1 / l ≤ 1 := by rw [div_le_one hl0]; exact hl1
  have hihl : 1 / h ≤ 1 / l := one_div_le_one_div_of_le hl0 (hlX.trans hXh)
  rw [abs_of_pos hil0] at hq1b
  rw [abs_of_pos hih0] at hq2b
  have e1 : 1 / l * η ≤ η := by nlinarith
  have e2 : 1 / h * η ≤ η := by nlinarith
  have hq1 : 0 ≤ q1 := by nlinarith
  have hq2 : 0 ≤ q2 := hih0.le.trans hq2a
  rw [abs_of_nonneg (by linarith)] at hs1b hs2b
  have hm1 := add_inv_mono hl1 hlX
  have hm2 := add_inv_mono (hl1.trans hlX) hXh
  refine ⟨by linarith, by linarith, ?_⟩
  have e3 : (l + q1) * η ≤ (h + 1) * η :=
    mul_le_mul_of_nonneg_right (by linarith [hlX.trans hXh]) hη0
  have e4 : (h + q2) * η ≤ (h + 2) * η := mul_le_mul_of_nonneg_right (by linarith) hη0
  nlinarith

/-- **`coshOfExp` encloses `(X + 1/X)/2`** for an enclosure `[lo, hi]` of `X ≥ 1`. -/
theorem coshOfExp_spec {b : Encl} {X lo hi : ℝ} (hlo : b.1.toVal = some (lo : EReal))
    (hhi : b.2.toVal = some (hi : EReal)) (hX1 : 1 ≤ X) (h1 : lo ≤ X) (h2 : X ≤ hi) {W : ℕ}
    (hW : 3 ≤ W) :
    IsEnclW (coshOfExp b W) ((X + 1 / X) / 2)
      ((hi - lo) + (1 / 2 : ℝ) ^ W * (4 * hi + 10)) := by
  have : NeZero W := ⟨by omega⟩
  have hl := toVal_maxOf hlo toVal_one'
  have hl1 : 1 ≤ max lo 1 := le_max_right _ _
  have hlX : max lo 1 ≤ X := max_le h1 hX1
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hη : (1 / 2 : ℝ) ^ W ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hW
      _ = 1 / 8 := by norm_num
  obtain ⟨q1, hq1, hq1a, hq1b⟩ := divFloor_abs toVal_one' hl (by linarith : max lo 1 ≠ 0) W
  obtain ⟨s1, hs1, hs1a, hs1b⟩ := addFloor_abs hl hq1 W
  obtain ⟨q2, hq2, hq2a, hq2b⟩ := divCeiling_abs toVal_one' hhi (by linarith : hi ≠ 0) W
  obtain ⟨s2, hs2, hs2a, hs2b⟩ := addCeiling_abs hhi hq2 W
  obtain ⟨b1, b2, b3⟩ := coshStep_bounds hη0 hη hl1 hlX h2 hq1a hq1b hs1a hs1b hq2a hq2b
    hs2a hs2b
  have hsh1 := toVal_shiftLeft_of_toVal hs1 (AzInt.ofInt (-1))
  have hsh2 := toVal_shiftLeft_of_toVal hs2 (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at hsh1 hsh2
  have hpos : 0 ≤ (1 / 2 : ℝ) ^ W * (4 * hi + 10) := by
    have : 0 ≤ hi := by linarith
    positivity
  have hlo' : lo ≤ max lo 1 := le_max_left _ _
  exact ⟨s1 / 2, s2 / 2, hsh1, hsh2, by linarith, by linarith, by linarith⟩

/-- The width of `coshOfExp` at precision `w + 16` on an enclosure of `X` of width `E`. -/
noncomputable def coshWidth (X E : ℝ) (w : ℕ) : ℝ := E + (1 / 2 : ℝ) ^ w * (4 * (X + E) + 10)

theorem tendsto_coshWidth (X : ℝ) {E : ℕ → ℝ} (hE : Filter.Tendsto E Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun w => coshWidth X (E w) w) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := hE.add (hp.mul (((hE.const_add X).const_mul 4).add_const 10))
  have h0 : (0 + 0 * (4 * (X + 0) + 10) : ℝ) = 0 := by ring
  rw [h0] at h
  exact h

/-- **`coshOfExp` at precision `w + 16` encloses `cosh a`**, `a ≥ 0`, from an enclosure of `e^a`
of width at most `E`, with width at most `coshWidth (e^a) E w`. -/
theorem coshOfExp_width {b : Encl} {av lo hi E : ℝ} (hlo : b.1.toVal = some (lo : EReal))
    (hhi : b.2.toVal = some (hi : EReal)) (ha0 : 0 ≤ av) (h1 : lo ≤ Real.exp av)
    (h2 : Real.exp av ≤ hi) (h3 : hi - lo ≤ E) (w : ℕ) :
    IsEnclW (coshOfExp b (w + 16)) (Real.cosh av) (coshWidth (Real.exp av) E w) := by
  have hX1 : 1 ≤ Real.exp av := by linarith [add_one_le_exp av]
  have hs := coshOfExp_spec hlo hhi hX1 h1 h2 (W := w + 16) (by omega)
  have hc : Real.cosh av = (Real.exp av + 1 / Real.exp av) / 2 := by
    rw [cosh_eq, exp_neg, one_div]
  rw [← hc] at hs
  refine hs.mono ?_
  unfold coshWidth
  have hhi0 : 0 ≤ hi := by linarith
  have hpw : (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hm : (1 / 2 : ℝ) ^ (w + 16) * (4 * hi + 10)
      ≤ (1 / 2 : ℝ) ^ w * (4 * (Real.exp av + E) + 10) :=
    mul_le_mul hpw (by linarith) (by positivity) (by positivity)
  linarith

/-! ### The float bracket -/

/-- **`coshBracket x e w` encloses `cosh x`** for a float `|x| < 2^e`. -/
theorem coshBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (e : AzInt)
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (coshBracket x e w) (Real.cosh xv) (coshWidth (Real.exp |xv|) (expEps |xv| w) w) := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ :=
    expBracket_spec habs e (by rwa [abs_abs]) hw
  have h := coshOfExp_width hlo hhi (abs_nonneg xv) h1 h2 h3 w
  rwa [cosh_abs] at h

/-- `coshApprox` as a pair of `Roundable`s bracketing `cosh x`. -/
theorem coshApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {e : AzInt}
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (coshApprox x e w).1 lv ∧ Rounds (coshApprox x e w).2 hv ∧
      lv ≤ Real.cosh xv ∧ Real.cosh xv ≤ hv ∧
      hv - lv ≤ coshWidth (Real.exp |xv|) (expEps |xv| w) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := coshBracket_spec hx e hxe hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `cosh x` is irrational for a finite float `x ≠ 0`. -/
theorem irrational_cosh_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.cosh xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  rw [hq] at hx0 ⊢
  exact irrational_cosh_rat (by exact_mod_cast hx0)

/-- The Ziv certificate for `cosh x`, `x` a finite nonzero float. -/
theorem coshApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {e : AzInt}
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (coshApprox x e (w₀ * 2 ^ f)).1
      (coshApprox x e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (coshApprox x e)
    (irrational_cosh_of_toVal hx hx0) (fun w => coshWidth (Real.exp |xv|) (expEps |xv| w) w)
    (tendsto_coshWidth _ (tendsto_expEps _)) 64
    (fun _ hw => coshApprox_spec hx hxe hw) w₀ hw₀

/-! ### The rational bracket -/

/-- The width bound of `coshRatBracket`. -/
noncomputable def coshRatEps (q : AzRat) (w : ℕ) : ℝ :=
  coshWidth (Real.exp (AzRat.toRat q.abs : ℝ)) (expRatEps (AzRat.toRat q.abs : ℝ) w) w

theorem tendsto_coshRatEps (q : AzRat) :
    Filter.Tendsto (coshRatEps q) Filter.atTop (nhds 0) :=
  tendsto_coshWidth _ (tendsto_expRatEps _)

/-- **`coshRatBracket q w` encloses `cosh q`** for a rational `q`. -/
theorem coshRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) :
    IsEnclW (coshRatBracket q w) (Real.cosh ((AzRat.toRat q : ℚ) : ℝ)) (coshRatEps q w) := by
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expRatBracket_spec hw q.abs
  have h := coshOfExp_width hlo hhi (by rw [habs]; exact abs_nonneg _) h1 h2 h3 w
  rw [habs, cosh_abs] at h
  rw [coshRatEps, habs]
  exact h

/-- `coshRatApprox` as a pair of `Roundable`s bracketing `cosh q`. -/
theorem coshRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) :
    ∃ lv hv : ℝ, Rounds (coshRatApprox q w).1 lv ∧ Rounds (coshRatApprox q w).2 hv ∧
      lv ≤ Real.cosh (AzRat.toRat q : ℝ) ∧ Real.cosh (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ coshRatEps q w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := coshRatBracket_spec hw q
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hlo hhi h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `cosh q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_cosh_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.cosh (AzRat.toRat q : ℝ)) :=
  irrational_cosh_rat (q := AzRat.toRat q)
    (fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp (by rw [h, Rat.cast_zero])))

/-- The Ziv certificate for `cosh q`. -/
theorem coshRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (coshRatApprox q (w₀ * 2 ^ f)).1
      (coshRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (coshRatApprox q) (irrational_cosh_toRat q h0)
    (coshRatEps q) (tendsto_coshRatEps q) 64 (fun _ hw => coshRatApprox_spec hw q) w₀ hw₀

/-! ### The tiny-exponent path -/

/-- The tiny-exponent test of the exponential answers with the rounding of `cosh x`, for
`0 < |x| < t` and `t²/2 ≤ 2^E`: `cosh x = exp v` with `0 < v ≤ x²/2`. -/
theorem coshNearOne?_eq {E : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {x t : ℝ} (hx0 : x ≠ 0) (ht : |x| < t)
    (hE : t * t / 2 ≤ (2 : ℝ) ^ E.toInt) (h : expNearOne? true E p mode = some r) :
    r = roundVal p mode (some ((Real.cosh x : ℝ) : EReal)) := by
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
  have hlt : |Real.log (Real.cosh x)| < (2 : ℝ) ^ E.toInt := by
    rw [abs_of_pos hv0]
    linarith
  have := expNearOne?_eq hlt hv0.ne' (by simp [hv0]) h
  rwa [Real.exp_log hc0] at this

/-- `2^(coshTinyExp e) = (2^e)²/2`. -/
theorem two_zpow_coshTinyExp (e : AzInt) :
    (2 : ℝ) ^ (coshTinyExp e).toInt = (2 : ℝ) ^ e.toInt * (2 : ℝ) ^ e.toInt / 2 := by
  unfold coshTinyExp
  rw [AzInt.toInt_add, AzInt.toInt_add, AzInt.toInt_ofInt, zpow_add₀ (by norm_num),
    zpow_add₀ (by norm_num), zpow_neg_one]
  ring

/-- The tiny-exponent path of `cosh x` for a float `0 < |x| < 2^e`. -/
theorem coshTiny_eq {e : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {x : ℝ} (hx0 : x ≠ 0) (hxe : |x| < (2 : ℝ) ^ e.toInt)
    (h : expNearOne? true (coshTinyExp e) p mode = some r) :
    r = roundVal p mode (some ((Real.cosh x : ℝ) : EReal)) :=
  coshNearOne?_eq hx0 hxe (two_zpow_coshTinyExp e).ge h

/-- The tiny-exponent path of `cosh q` for a rational `q ≠ 0`. -/
theorem coshRatTiny_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (h : expNearOne? true (coshRatTinyExp q) p mode = some r) :
    r = roundVal p mode (some ((Real.cosh (AzRat.toRat q : ℝ) : ℝ) : EReal)) := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have hlt := abs_toRat_lt_two_zpow q
  have he : ((ratExpBound q + AzInt.ofInt (-1)).toInt) = (ratExpBound q).toInt - 1 := by
    rw [AzInt.toInt_add, AzInt.toInt_ofInt]
    ring
  rw [← he] at hlt
  exact coshTiny_eq hq0 hlt h

end Azurite.AzFloat
