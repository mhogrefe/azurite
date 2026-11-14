/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CscBracket
import Azurite.AzFloat.Equiv.SinRatBracket
import Azurite.AzFloat.Equiv.SinWithPeriodBracket
import Azurite.AzFloat.Equiv.SecWithPeriodBracket

/-!
# Equivalence: the brackets of `csc x`

* `Spec.cscSigned a θ`: `1 / sin θ`, and at a pole (`sin θ = 0`) the infinity with the sign of
  the argument `a` (`+∞` for `a = 0`); `Spec.cscCore neg θ`: the same after the reduction, the
  sign as a Boolean; `cscSigned_two_pi_div`, `cscSigned_self`.
* `reciprocalNeg_valid_or_none`, `reciprocalNeg_isSome_exists`: the signed reciprocal of a
  bracket family; the instances for `cscApprox`, `cscRatApprox`, `cscPeriodApprox`.
* `csc_bounds_of_small`, `cscTinyCore?_eq`, `periodTinyArg_spec`, `cscTiny?_eq`,
  `cscTinyRat?_eq`, `cscPeriodTiny?_eq`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- The cosecant with poles: `1 / sin θ` where `sin θ ≠ 0`, and at a pole the infinity with the
sign of the argument `a` (`+∞` for `a ≥ 0`). -/
noncomputable def cscSigned (a θ : ℝ) : EReal :=
  if Real.sin θ = 0 then (if a < 0 then ⊥ else ⊤) else ((1 / Real.sin θ : ℝ) : EReal)

open Classical in
/-- The cosecant after the reduction: `± 1 / sin θ` (`neg`: the sign is negative), and at a
pole `−∞` for `neg`, `+∞` otherwise. -/
noncomputable def cscCore (neg : Bool) (θ : ℝ) : EReal :=
  if Real.sin θ = 0 then (if neg then ⊥ else ⊤)
  else (((if neg then -1 else 1) * (1 / Real.sin θ) : ℝ) : EReal)

theorem cscCore_of_irrational {neg : Bool} {θ : ℝ} (h : Irrational (1 / Real.sin θ)) :
    cscCore neg θ = (((if neg then -1 else 1) * (1 / Real.sin θ) : ℝ) : EReal) := by
  unfold cscCore
  refine ite_eq_right fun hc => ?_
  rw [hc, div_zero] at h
  exact h ⟨0, by simp⟩

/-- `cscSigned a θ = cscCore neg θ'` when `neg` is the sign of `a` and `sin θ = ± sin θ'` with
that sign. -/
theorem cscSigned_eq_cscCore {a θ θ' : ℝ} {neg : Bool} (hneg : neg = true ↔ a < 0)
    (hs : Real.sin θ = (if neg then -1 else 1) * Real.sin θ') :
    cscSigned a θ = cscCore neg θ' := by
  unfold cscSigned cscCore
  cases neg with
  | false =>
    have ha : ¬ a < 0 := fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hs ⊢
    rw [hs, ite_eq_right ha]
  | true =>
    have ha : a < 0 := hneg.mp rfl
    simp only [↓reduceIte, neg_one_mul] at hs ⊢
    rw [hs, ite_eq_left ha]
    by_cases h0 : Real.sin θ' = 0
    · rw [ite_eq_left h0, ite_eq_left (by rw [h0, neg_zero])]
    · rw [ite_eq_right h0, ite_eq_right (neg_ne_zero.mpr h0)]
      congr 1
      rw [one_div, one_div, inv_neg]

/-- The reduction of `cscSigned x (2π x / U)` to the fractional part `ρ` of `|x| / U`. -/
theorem cscSigned_two_pi_div {xv U ρ : ℝ} {neg : Bool} (hneg : neg = true ↔ xv < 0) {k : ℕ}
    (hk : |xv| / U = k + ρ) :
    cscSigned xv (2 * Real.pi * xv / U) = cscCore neg (2 * Real.pi * ρ) := by
  refine cscSigned_eq_cscCore hneg ?_
  have habs : Real.sin (2 * Real.pi * (|xv| / U)) = Real.sin (2 * Real.pi * ρ) := by
    rw [hk, show 2 * Real.pi * ((k : ℝ) + ρ) = 2 * Real.pi * ρ + k * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi]
  cases neg with
  | false =>
    have ha : ¬ xv < 0 := fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [← habs, abs_of_nonneg (not_lt.mp ha)]
    congr 1
    ring
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    rw [← habs, abs_of_neg (hneg.mp rfl), ← Real.sin_neg]
    congr 1
    ring

/-- `cscSigned x x` in terms of `|x|`. -/
theorem cscSigned_self {xv : ℝ} {neg : Bool} (hneg : neg = true ↔ xv < 0) :
    cscSigned xv xv = cscCore neg |xv| := by
  refine cscSigned_eq_cscCore hneg ?_
  cases neg with
  | false =>
    have ha : ¬ xv < 0 := fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg (not_lt.mp ha)]
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    rw [abs_of_neg (hneg.mp rfl), Real.sin_neg, neg_neg]

end Spec

/-! ### The signed reciprocal of a bracket family -/

/-- The signed reciprocal of a bracket encloses `± 1 / c` or is rejected. -/
theorem reciprocalNeg_valid_or_none (neg : Bool) {C : Encl} {c δ : ℝ} (hC : IsEnclW C c δ)
    {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ,
        Rounds (negSwapApprox neg (tanOfSinCos (Encl.exact one, C) (w + 12))).1 lv ∧
        Rounds (negSwapApprox neg (tanOfSinCos (Encl.exact one, C) (w + 12))).2 hv ∧
        lv ≤ (if neg then -1 else 1) * (1 / c) ∧ (if neg then -1 else 1) * (1 / c) ≤ hv) ∨
      roundingPossible (negSwapApprox neg (tanOfSinCos (Encl.exact one, C) (w + 12))).1
        (negSwapApprox neg (tanOfSinCos (Encl.exact one, C) (w + 12))).2 p mode = none := by
  have hS : IsEnclW (Encl.exact one, C).1 1 0 := (isEncl0W_exact toVal_one' zero_le_one).toW
  exact tanOfSinCos_valid_or_none neg hS (b := (Encl.exact one, C)) hC (by norm_num)
    zero_le_one (V := w + 12) (by omega) p mode

/-- The Ziv certificate for the signed reciprocal of a bracket family `C w` of width `ε w → 0`
around `c ≠ 0` with an irrational reciprocal. -/
theorem reciprocalNeg_isSome_exists (neg : Bool) (p : ℕ) [NeZero p] (mode : RoundingMode)
    {C : ℕ → Encl} {c : ℝ} {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hC : ∀ w, 64 ≤ w → IsEnclW (C w) c (ε w)) (hc : c ≠ 0) (hirr : Irrational (1 / c))
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (negSwapApprox neg (tanOfSinCos (Encl.exact one, C (w₀ * 2 ^ f)) (w₀ * 2 ^ f + 12))).1
      (negSwapApprox neg (tanOfSinCos (Encl.exact one, C (w₀ * 2 ^ f)) (w₀ * 2 ^ f + 12))).2 p
      mode).isSome = true := by
  have hc0 : 0 < |c| := abs_pos.mpr hc
  obtain ⟨W₁, hW₁⟩ := (hε.eventually (gt_mem_nhds (half_pos hc0))).exists_forall_of_atTop
  refine exists_isSome_of_irrational_threshold p mode
    (fun w => negSwapApprox neg (tanOfSinCos (Encl.exact one, C w) (w + 12)))
    (irrational_sign_mul hirr neg) (recipEps ε |c|) (tendsto_recipEps hε _) (max 64 W₁)
    (fun w hw => ?_) w₀ hw₀
  have hS : IsEnclW (Encl.exact one, C w).1 1 0 := (isEncl0W_exact toVal_one' zero_le_one).toW
  exact negSwapApprox_of_isEnclW neg (tanOfSinCos_width hS (b := (Encl.exact one, C w))
    (hC w (le_of_max_le_left hw)) (by norm_num) zero_le_one (V := w + 12) (by omega) hc0
    (hW₁ w (le_of_max_le_right hw)).le)

/-! ### The three instances -/

theorem irrational_sin_abs_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.sin |xv|) := by
  rcases abs_choice xv with h | h
  · rw [h]; exact irrational_sin_of_toVal hx hx0
  · rw [h, Real.sin_neg]; exact (irrational_sin_of_toVal hx hx0).neg

theorem irrational_csc_abs_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (1 / Real.sin |xv|) := by
  rw [one_div]
  exact (irrational_sin_abs_of_toVal hx hx0).inv

/-- At every level `w ≥ 64` the bracket of `cscApprox neg` encloses `± csc |x|` or is
rejected. -/
theorem cscApprox_valid_or_none (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ}
    (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (cscApprox neg x ex w).1 lv ∧ Rounds (cscApprox neg x ex w).2 hv ∧
        lv ≤ (if neg then -1 else 1) * (1 / Real.sin |xv|) ∧
        (if neg then -1 else 1) * (1 / Real.sin |xv|) ≤ hv) ∨
      roundingPossible (cscApprox neg x ex w).1 (cscApprox neg x ex w).2 p mode = none :=
  reciprocalNeg_valid_or_none neg (sinBracket_spec hx hex hw) hw p mode

/-- The Ziv certificate for `csc x`, `x` a nonzero finite float. -/
theorem cscApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cscApprox neg x ex (w₀ * 2 ^ f)).1
      (cscApprox neg x ex (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  reciprocalNeg_isSome_exists neg p mode (tendsto_sinEps ex)
    (fun _ hw => sinBracket_spec hx hex hw) (irrational_sin_abs_of_toVal hx hx0).ne_zero
    (irrational_csc_abs_of_toVal hx hx0) w₀ hw₀

theorem irrational_sin_abs_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.sin |(AzRat.toRat q : ℝ)|) := by
  rcases abs_choice (AzRat.toRat q : ℝ) with h | h
  · rw [h]; exact irrational_sin_toRat q h0
  · rw [h, Real.sin_neg]; exact (irrational_sin_toRat q h0).neg

theorem irrational_csc_abs_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (1 / Real.sin |(AzRat.toRat q : ℝ)|) := by
  rw [one_div]
  exact (irrational_sin_abs_toRat q h0).inv

/-- At every level `w ≥ 64` the bracket of `cscRatApprox` encloses `± csc |q|` or is rejected. -/
theorem cscRatApprox_valid_or_none (q : AzRat) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (cscRatApprox q w).1 lv ∧ Rounds (cscRatApprox q w).2 hv ∧
        lv ≤ (if (!q.sign) = true then -1 else 1) * (1 / Real.sin |(AzRat.toRat q : ℝ)|) ∧
        (if (!q.sign) = true then -1 else 1) * (1 / Real.sin |(AzRat.toRat q : ℝ)|) ≤ hv) ∨
      roundingPossible (cscRatApprox q w).1 (cscRatApprox q w).2 p mode = none :=
  reciprocalNeg_valid_or_none (!q.sign) (sinRatBracket_spec q hw) hw p mode

/-- The Ziv certificate for `csc q`, `q` a nonzero rational. -/
theorem cscRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cscRatApprox q (w₀ * 2 ^ f)).1 (cscRatApprox q (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  reciprocalNeg_isSome_exists (!q.sign) p mode (tendsto_sinRatEps q)
    (fun _ hw => sinRatBracket_spec q hw) (irrational_sin_abs_toRat q h0).ne_zero
    (irrational_csc_abs_toRat q h0) w₀ hw₀

/-- `csc (2πr)` is irrational for an `AzRat` whose denominator is not `1, 2, 4, 12`. -/
theorem irrational_csc_two_pi_mul_toRat (r : AzRat) (h1 : r.den ≠ AzNat.ofNat 1)
    (h2 : r.den ≠ AzNat.ofNat 2) (h4 : r.den ≠ AzNat.ofNat 4) (h12 : r.den ≠ AzNat.ofNat 12) :
    Irrational (1 / Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ))) := by
  rw [one_div]
  exact (irrational_sin_two_pi_mul_toRat r h1 h2 h4 h12).inv

/-- At every level `w ≥ 64` the bracket of `cscPeriodApprox neg` encloses `± csc (2πr)` or is
rejected. -/
theorem cscPeriodApprox_valid_or_none (neg : Bool) (r : AzRat)
    (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ}
    (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (cscPeriodApprox neg r w).1 lv ∧ Rounds (cscPeriodApprox neg r w).2 hv ∧
        lv ≤ (if neg then -1 else 1) * (1 / Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ))) ∧
        (if neg then -1 else 1) * (1 / Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ))) ≤ hv) ∨
      roundingPossible (cscPeriodApprox neg r w).1 (cscPeriodApprox neg r w).2 p mode = none :=
  reciprocalNeg_valid_or_none neg (sinPeriodBracket_spec r hr0 hr1 hw) hw p mode

/-- The Ziv certificate for `± csc (2πr)`, `r ∈ [0, 1)` with an irrational sine. -/
theorem cscPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1)
    (h1 : r.den ≠ AzNat.ofNat 1) (h2 : r.den ≠ AzNat.ofNat 2) (h4 : r.den ≠ AzNat.ofNat 4)
    (h12 : r.den ≠ AzNat.ofNat 12) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cscPeriodApprox neg r (w₀ * 2 ^ f)).1
      (cscPeriodApprox neg r (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  reciprocalNeg_isSome_exists neg p mode tendsto_sinPeriodEps
    (fun _ hw => sinPeriodBracket_spec r hr0 hr1 hw)
    (irrational_sin_two_pi_mul_toRat r h1 h2 h4 h12).ne_zero
    (irrational_csc_two_pi_mul_toRat r h1 h2 h4 h12) w₀ hw₀

/-! ### Tiny arguments -/

/-- `1/a < csc a ≤ 1/a + a` for `0 < a ≤ 1`. -/
theorem csc_bounds_of_small {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    1 / a < 1 / Real.sin a ∧ 1 / Real.sin a ≤ 1 / a + a := by
  have hpi := Real.pi_gt_three
  have hs0 : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith)
  have hs1 := Real.sin_lt ha0
  have hs2 := Real.sin_gt_sub_cube ha0
  refine ⟨one_div_lt_one_div_of_lt hs0 hs1, ?_⟩
  rw [div_le_iff₀ hs0]
  have h1a : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hlow : 1 ≤ (1 / a + a) * (a - a ^ 3 / 6) := by
    have e : (1 / a + a) * (a - a ^ 3 / 6) = 1 + 5 * a ^ 2 / 6 - a ^ 4 / 6 := by
      field_simp
      ring
    rw [e]
    nlinarith [mul_nonneg (sq_nonneg a) h1a]
  have hpos : 0 ≤ 1 / a + a := by positivity
  calc (1 : ℝ) ≤ (1 / a + a) * (a - a ^ 3 / 6) := hlow
    _ ≤ (1 / a + a) * Real.sin a := mul_le_mul_of_nonneg_left hs2.le hpos

theorem cscTinyCore?_cond {neg : Bool} {alo ahi : AzFloat} {e : AzInt} {p : ℕ}
    {mode : RoundingMode} {r : AzFloat × Ordering}
    (h : cscTinyCore? neg alo ahi e p mode = some r) :
    e.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e.abs.toNat := by
  unfold cscTinyCore? at h
  by_contra hc
  rw [ite_eq_right hc] at h
  cases h

/-- **The tiny-argument test answers with the rounding of `± csc a`.** -/
theorem cscTinyCore?_eq {neg : Bool} {alo ahi : AzFloat} {e : AzInt} {p : ℕ} [NeZero p]
    {mode : RoundingMode} {r : AzFloat × Ordering} {a l h : ℝ}
    (hl : alo.toVal = some (l : EReal)) (hh : ahi.toVal = some (h : EReal)) (hl0 : 0 < l)
    (hla : l ≤ a) (hah : a ≤ h) (hlt : a < (2 : ℝ) ^ e.toInt)
    (hirr : Irrational (1 / Real.sin a)) (hT : cscTinyCore? neg alo ahi e p mode = some r) :
    r = roundVal p mode
      (some (((if neg then -1 else 1) * (1 / Real.sin a) : ℝ) : EReal)) := by
  have hc := cscTinyCore?_cond hT
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [hc.1] at htoInt
  simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
  have ht1 : (2 : ℝ) ^ e.toInt ≤ 1 := by
    rw [htoInt, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have ha0 : 0 < a := lt_of_lt_of_le hl0 hla
  have hh0 : 0 < h := lt_of_lt_of_le ha0 hah
  obtain ⟨hb1, hb2⟩ := csc_bounds_of_small ha0 (hlt.le.trans ht1)
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  unfold cscTinyCore? at hT
  rw [ite_eq_left hc] at hT
  obtain ⟨lo, hlo, hlo1, -⟩ := divFloor_abs toVal_one' hh hh0.ne' (p + zivGuardBits + 8)
  obtain ⟨c, hcv, hc1, -⟩ := divCeiling_abs toVal_one' hl hl0.ne' (p + zivGuardBits + 8)
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hcv hh (p + zivGuardBits + 8)
  have h1 : 1 / h ≤ 1 / a := one_div_le_one_div_of_le ha0 hah
  have h2 : 1 / a ≤ 1 / l := one_div_le_one_div_of_le hl0 hla
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hvB := not_mem_floatSet_of_irrational p hirr
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hT ⊢
    exact roundingPossible_eq' p mode hR1 hR2 (by linarith) (by linarith) (Or.inr hvB) hT
  | true =>
    simp only [↓reduceIte, neg_one_mul] at hT ⊢
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hT
    have hr := roundingPossible_eq' p (-mode) hR1 hR2 (v := 1 / Real.sin a) (by linarith)
      (by linarith) (Or.inr hvB) hr'
    rw [hr]
    exact (roundVal_neg p mode (1 / Real.sin a)).symm

/-- **The floats of `periodTinyArg` enclose `y = 2π m 2^E / u`**, the lower one positive. -/
theorem periodTinyArg_spec {m u : AzNat} (hm : 0 < m.toNat) (hu : 0 < u.toNat) (E : AzInt)
    {W : ℕ} (hW : 64 ≤ W) :
    ∃ lo hi : ℝ, (periodTinyArg m u E W).1.toVal = some (lo : EReal) ∧
      (periodTinyArg m u E W).2.toVal = some (hi : EReal) ∧ 0 < lo ∧
      lo ≤ 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) ∧
      2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) ≤ hi := by
  have : NeZero W := ⟨by omega⟩
  set y := 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) with hydef
  simp only [periodTinyArg]
  have hm' : (0 : ℝ) < m.toNat := by exact_mod_cast hm
  have hu' : (0 : ℝ) < u.toNat := by exact_mod_cast hu
  have hcv : ((AzRat.toRat (AzRat.ofAzNats m u) : ℚ) : ℝ) = (m.toNat : ℝ) / u.toNat := by
    rw [AzRat.toRat_ofAzNats]; push_cast; rfl
  have hpi := Real.pi_pos
  have hus : (1 / 2 : ℝ) ^ W ≤ 1 / 10 ^ 18 := half_pow_small hW
  obtain ⟨lv, hv, hlv, hhv, hlv0, hlvπ, hπhv, hwid⟩ := piBracket_spec_width hW
  obtain ⟨cl, hcl, hcl1, hcl2⟩ := ofAzRatRound_floor_abs (AzRat.ofAzNats m u) W
  obtain ⟨ch, hch, hch1, -⟩ := ofAzRatRound_ceiling_abs (AzRat.ofAzNats m u) W
  rw [hcv] at hcl1 hcl2 hch1
  set cv := (m.toNat : ℝ) / u.toNat with hcvdef
  have hcv0 : 0 < cv := by positivity
  rw [abs_of_pos hcv0] at hcl2
  have hcl0 : 0 < cl := by nlinarith
  obtain ⟨a1, ha1, ha1le, ha1ge⟩ := mulFloor_abs hcl hlv W
  obtain ⟨a2, ha2, ha2ge, -⟩ := mulCeiling_abs hch hhv W
  have hlvpos : 0 < lv := by linarith [Real.pi_gt_three]
  have hprod : 0 < cl * lv := mul_pos hcl0 hlvpos
  rw [abs_of_pos hprod] at ha1ge
  have ha10 : 0 < a1 := by nlinarith
  have hylo := toVal_shiftLeft_of_toVal ha1 (E + AzInt.ofInt 1)
  have hyhi := toVal_shiftLeft_of_toVal ha2 (E + AzInt.ofInt 1)
  have hT : (2 : ℝ) ^ (E + AzInt.ofInt 1).toInt = (2 : ℝ) ^ E.toInt * 2 := by
    rw [AzInt.toInt_add, AzInt.toInt_ofInt, zpow_add₀ two_ne_zero, zpow_one]
  set T := (2 : ℝ) ^ (E + AzInt.ofInt 1).toInt with hTdef
  have hT0 : 0 < T := by positivity
  have hyeq : y = cv * Real.pi * T := by
    rw [hydef, hcvdef, hT]; ring
  refine ⟨a1 * T, a2 * T, hylo, hyhi, mul_pos ha10 hT0, ?_, ?_⟩
  · rw [hyeq]
    refine mul_le_mul_of_nonneg_right ?_ hT0.le
    calc a1 ≤ cl * lv := ha1le
      _ ≤ cv * lv := mul_le_mul_of_nonneg_right hcl1 hlv0
      _ ≤ cv * Real.pi := mul_le_mul_of_nonneg_left hlvπ.le hcv0.le
  · rw [hyeq]
    refine mul_le_mul_of_nonneg_right ?_ hT0.le
    calc cv * Real.pi ≤ ch * Real.pi := mul_le_mul_of_nonneg_right hch1 hpi.le
      _ ≤ ch * hv := mul_le_mul_of_nonneg_left hπhv (by linarith)
      _ ≤ a2 := ha2ge

/-- The tiny-argument path of `csc (2π x / u)` answers with the rounding of `± csc y`. -/
theorem cscPeriodTiny?_eq {neg : Bool} {m u : AzNat} (hm : 0 < m.toNat) (hu : 0 < u.toNat)
    {E e' : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode} {r : AzFloat × Ordering}
    (hy : 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) < (2 : ℝ) ^ e'.toInt)
    (hirr : Irrational
      (1 / Real.sin (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat))))
    (hT : cscPeriodTiny? neg m u E e' p mode = some r) :
    r = roundVal p mode (some (((if neg then -1 else 1)
      * (1 / Real.sin (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat))) : ℝ)
        : EReal)) := by
  obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2⟩ := periodTinyArg_spec hm hu E
    (W := p + zivGuardBits + 8) (by unfold zivGuardBits; omega)
  exact cscTinyCore?_eq hlo hhi hlo0 h1 h2 hy hirr hT

/-- The tiny-argument path of `csc x` answers with the rounding of `± csc |x|`. -/
theorem cscTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : cscTiny? s (finite s e q m hv) e p mode = some r) :
    r = roundVal p mode (some (((if (!s) = true then -1 else 1)
      * (1 / Real.sin |finiteVal s e m|) : ℝ) : EReal)) := by
  have hx : (finite s e q m hv).toVal = some ((finiteVal s e m : ℝ) : EReal) :=
    toVal_finite s e q m hv
  have hx0 : finiteVal s e m ≠ 0 := finiteVal_ne_zero s e hv
  have habs : (finite s e q m hv).abs.toVal = some ((|finiteVal s e m| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  exact cscTinyCore?_eq habs habs (abs_pos.mpr hx0) le_rfl le_rfl
    (abs_finiteVal_bounds s e hv).2 (irrational_csc_abs_of_toVal hx hx0) h

/-- The tiny-argument path of `csc q` answers with the rounding of `± csc |q|`. -/
theorem cscTinyRat?_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (hT : cscTinyRat? q p mode = some r) :
    r = roundVal p mode (some (((if (!q.sign) = true then -1 else 1)
      * (1 / Real.sin |(AzRat.toRat q : ℝ)|) : ℝ) : EReal)) := by
  unfold cscTinyRat? at hT
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  have ha0 := abs_pos.mpr hq0
  have hus : (1 / 2 : ℝ) ^ (p + zivGuardBits + 8) ≤ 1 / 10 ^ 18 :=
    half_pow_small (by unfold zivGuardBits; omega)
  obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs q.abs (p + zivGuardBits + 8)
  obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs q.abs (p + zivGuardBits + 8)
  rw [habs] at hl1 hl2 hc1
  rw [abs_abs] at hl2
  have hl0 : 0 < l := by nlinarith
  have hlt : |((AzRat.toRat q : ℚ) : ℝ)| < (2 : ℝ) ^ (ratExpBound q).toInt :=
    lt_of_lt_of_le (abs_toRat_lt_two_zpow q) (zpow_le_zpow_right₀ (by norm_num) (by omega))
  exact cscTinyCore?_eq hl hc hl0 hl1 hc1 hlt (irrational_csc_abs_toRat q h0) hT

end Azurite.AzFloat
