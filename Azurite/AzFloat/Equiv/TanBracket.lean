/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanBracket
import Azurite.AzFloat.Equiv.SinCosBracket

/-!
# Equivalence: the bracket of `tan x`

* `irrational_tan_rat`: `tan q` is irrational for a rational `q ≠ 0` (from the cosine:
  `cos 2q = 2/(1 + tan² q) − 1`); `irrational_tan_of_toVal`.
* `roundingPossible_none_of_neg_one_one`: the dummy bracket `[−1, 1]` is never accepted.
* `enclDivSignedPos_spec`: the quotient of a signed enclosure by a positive one, with its width.
* `tanBracket_spec`: `tanBracket x ex w` is the dummy bracket (and then `|cos x| ≤ sinCosEps`) or
  encloses `tan |x|`, with a width bound for every lower bound `m` of the bracket of `|cos x|`.
* `tanApprox_valid_or_none`, `tanApprox_spec` (width `tanEps |cos x| ex w` once
  `sinCosEps ex w ≤ |cos x|/2`), `tendsto_tanEps`, `tanApprox_isSome_exists` (the certificate).
* `tanTiny?_eq`: the tiny-argument path.
-/

namespace Azurite.AzFloat

/-! ### Irrationality -/

/-- `tan q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_tan_rat {q : ℚ} (hq : q ≠ 0) : Irrational (Real.tan q) := by
  have hc : Real.cos (q : ℝ) ≠ 0 := (irrational_cos_rat hq).ne_zero
  have h2 : Irrational (Real.cos ((2 * q : ℚ) : ℝ)) := irrational_cos_rat (by simpa using hq)
  intro ⟨t, ht⟩
  apply h2
  have hsq := Real.inv_one_add_tan_sq hc
  rw [← ht] at hsq
  refine ⟨2 * (1 + t ^ 2)⁻¹ - 1, ?_⟩
  push_cast
  rw [Real.cos_two_mul, hsq]

/-- `tan x` is irrational for a nonzero finite float `x`. -/
theorem irrational_tan_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.tan xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [hq, Rat.cast_zero]
  rw [hq]
  exact irrational_tan_rat hq0

/-- `tan x = ± tan |x|` with the sign bit of `x`. -/
theorem tan_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    Real.tan xv = (if neg then -1 else 1) * Real.tan |xv| := by
  cases neg with
  | false =>
    have h : ¬ xv < 0 := fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg (not_lt.mp h)]
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    rw [abs_of_neg (hneg.mp rfl), Real.tan_neg, neg_neg]

/-! ### The dummy bracket -/

/-- A bracket with ends `−1` and `1` is never accepted by `roundingPossible`. -/
theorem roundingPossible_none_of_neg_one_one {l h : AzFloat}
    (hl : l.toVal = some ((-1 : ℝ) : EReal)) (hh : h.toVal = some ((1 : ℝ) : EReal)) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    roundingPossible (fun P M => setPrecRound l P M) (fun P M => setPrecRound h P M) p mode
      = none := by
  unfold roundingPossible
  have hne : eqIEEE (setPrecRound l (p + 1) .Floor).1 (setPrecRound h (p + 1) .Floor).1
      = false := by
    by_contra hcon
    rw [Bool.not_eq_false, eqIEEE_iff] at hcon
    obtain ⟨v, hv1, hv2⟩ := hcon
    rw [setPrecRound_eq_roundVal hl] at hv1
    obtain ⟨a, ha, ha1, -⟩ := roundVal_floor_abs (p + 1) (-1 : ℝ)
    obtain ⟨b, hb, hbf⟩ := setPrecFloor_err hh zero_le_one (p + 1)
    rw [ha] at hv1
    rw [hb] at hv2
    have hab : (a : EReal) = (b : EReal) := Option.some.inj (hv1.trans hv2.symm)
    have hab' : a = b := EReal.coe_eq_coe_iff.mp hab
    linarith [hbf.nonneg]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]

/-! ### The signed quotient -/

/-- The corner estimate of the quotient. -/
theorem quot_sub_le {sl sh bi bj m δ ε : ℝ} (hm : 0 < m) (hi : m ≤ bi) (hj : m ≤ bj)
    (hd0 : 0 ≤ sh - sl) (hd : sh - sl ≤ δ) (hsl : |sl| ≤ 2) (hε : |bi - bj| ≤ ε) :
    sh / bj - sl / bi ≤ δ / m + 2 * ε / m ^ 2 := by
  have hbi : 0 < bi := lt_of_lt_of_le hm hi
  have hbj : 0 < bj := lt_of_lt_of_le hm hj
  have e : sh / bj - sl / bi = (sh - sl) / bj + sl * (bi - bj) / (bi * bj) := by
    field_simp
    ring
  have t1 : (sh - sl) / bj ≤ δ / m := div_le_div₀ (hd0.trans hd) hd hm hj
  have t2 : sl * (bi - bj) / (bi * bj) ≤ 2 * ε / m ^ 2 := by
    have hnum : sl * (bi - bj) ≤ 2 * ε :=
      calc sl * (bi - bj) ≤ |sl * (bi - bj)| := le_abs_self _
        _ = |sl| * |bi - bj| := abs_mul _ _
        _ ≤ 2 * ε := mul_le_mul hsl hε (abs_nonneg _) (by norm_num)
    have hε0 : 0 ≤ 2 * ε := by linarith [(abs_nonneg (bi - bj)).trans hε]
    have hden : m ^ 2 ≤ bi * bj := by rw [sq]; exact mul_le_mul hi hj hm.le hbi.le
    exact (div_le_div_of_nonneg_right hnum (mul_pos hbi hbj).le).trans
      (div_le_div_of_nonneg_left hε0 (by positivity) hden)
  rw [e]
  linarith

/-- **The quotient of a signed enclosure (`|s| ≤ 1`) by a positive one** with lower end at least
`m > 0`. -/
theorem enclDivSignedPos_spec {S B : Encl} {s b b1 b2 δ ε m : ℝ} (hS : IsEnclW S s δ)
    (hb1 : B.1.toVal = some (b1 : EReal)) (hb2 : B.2.toVal = some (b2 : EReal)) (hm : 0 < m)
    (hmb : m ≤ b1) (hb1b : b1 ≤ b) (hbb2 : b ≤ b2) (hε : b2 - b1 ≤ ε) (hs : |s| ≤ 1)
    (hδ : δ ≤ 1) {W : ℕ} (hW : 64 ≤ W) :
    IsEnclW (enclDivSignedPos W S B) (s / b)
      ((δ + 2 * ε / m + 8 * (1 / 2 : ℝ) ^ W) / m) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨sl, sh, hsl, hsh, hs1, hs2, hs3⟩ := hS
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨hsa, hsb⟩ := abs_le.mp hs
  have hb1p : 0 < b1 := lt_of_lt_of_le hm hmb
  have hbp : 0 < b := lt_of_lt_of_le hb1p hb1b
  have hb2p : 0 < b2 := lt_of_lt_of_le hbp hbb2
  have hslabs : |sl| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hshabs : |sh| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hmb2 : m ≤ b2 := hmb.trans (hb1b.trans hbb2)
  have hd0 : 0 ≤ sh - sl := by linarith
  have hε0 : 0 ≤ b2 - b1 := by linarith
  -- the divisor of the lower end
  have hlo : ∃ bi : ℝ, (if S.1.isNegative then B.1 else B.2).toVal = some (bi : EReal) ∧
      (bi = b1 ∨ bi = b2) ∧ sl / bi ≤ s / b := by
    cases hn : S.1.isNegative with
    | true =>
      have h : sl < 0 := (toVal_sign_of_isNegative hsl).1 hn
      refine ⟨b1, by simpa using hb1, Or.inl rfl, ?_⟩
      calc sl / b1 ≤ sl / b := by
            rw [div_le_div_iff₀ hb1p hbp]
            nlinarith
        _ ≤ s / b := div_le_div_of_nonneg_right hs1 hbp.le
    | false =>
      have h : 0 ≤ sl := (toVal_sign_of_isNegative hsl).2 hn
      refine ⟨b2, by simpa using hb2, Or.inr rfl, ?_⟩
      calc sl / b2 ≤ sl / b := div_le_div_of_nonneg_left h hbp hbb2
        _ ≤ s / b := div_le_div_of_nonneg_right hs1 hbp.le
  -- the divisor of the upper end
  have hup : ∃ bj : ℝ, (if S.2.isNegative then B.2 else B.1).toVal = some (bj : EReal) ∧
      (bj = b1 ∨ bj = b2) ∧ s / b ≤ sh / bj := by
    cases hn : S.2.isNegative with
    | true =>
      have h : sh < 0 := (toVal_sign_of_isNegative hsh).1 hn
      refine ⟨b2, by simpa using hb2, Or.inr rfl, ?_⟩
      calc s / b ≤ sh / b := div_le_div_of_nonneg_right hs2 hbp.le
        _ ≤ sh / b2 := by
          rw [div_le_div_iff₀ hbp hb2p]
          nlinarith
    | false =>
      have h : 0 ≤ sh := (toVal_sign_of_isNegative hsh).2 hn
      refine ⟨b1, by simpa using hb1, Or.inl rfl, ?_⟩
      calc s / b ≤ sh / b := div_le_div_of_nonneg_right hs2 hbp.le
        _ ≤ sh / b1 := div_le_div_of_nonneg_left h hb1p hb1b
  obtain ⟨bi, hbi, hbi12, hlo'⟩ := hlo
  obtain ⟨bj, hbj, hbj12, hup'⟩ := hup
  have hmi : m ≤ bi := by rcases hbi12 with h | h <;> rw [h] <;> assumption
  have hmj : m ≤ bj := by rcases hbj12 with h | h <;> rw [h] <;> assumption
  have hbip : 0 < bi := lt_of_lt_of_le hm hmi
  have hbjp : 0 < bj := lt_of_lt_of_le hm hmj
  have hij : |bi - bj| ≤ ε := by
    rcases hbi12 with h | h <;> rcases hbj12 with h' | h' <;> rw [h, h', abs_le] <;>
      constructor <;> linarith
  obtain ⟨r1, hr1, hr1a, hr1b⟩ := divFloor_abs hsl hbi hbip.ne' W
  obtain ⟨r2, hr2, hr2a, hr2b⟩ := divCeiling_abs hsh hbj hbjp.ne' W
  rw [← hu] at hr1b hr2b
  have hquot : ∀ {a c : ℝ}, |a| ≤ 2 → m ≤ c → |a / c| ≤ 2 / m := fun {a c} ha hc => by
    rw [abs_div, abs_of_pos (lt_of_lt_of_le hm hc)]
    exact div_le_div₀ (by norm_num) ha hm hc
  have e1 := mul_le_mul_of_nonneg_right (hquot hslabs hmi) hu0
  have e2 := mul_le_mul_of_nonneg_right (hquot hshabs hmj) hu0
  have hc := quot_sub_le hm hmi hmj hd0 hs3 hslabs hij
  have hfin : δ / m + 2 * ε / m ^ 2 + 2 * (2 / m * u) + 2 * (2 / m * u)
      = (δ + 2 * ε / m + 8 * u) / m := by
    field_simp
    ring
  exact ⟨r1, r2, hr1, hr2, hr1a.trans hlo', hup'.trans hr2a, by rw [← hfin]; linarith⟩

/-! ### The bracket -/

/-- A float of value `0` is `zero`. -/
theorem eq_zero_of_toVal_eq_zero {x : AzFloat} (h : x.toVal = some ((0 : ℝ) : EReal)) :
    x = zero := by
  cases x with
  | nan => simp at h
  | infinity s => cases s <;> simp at h
  | zero => rfl
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at h
    exact absurd h (finiteVal_ne_zero s e hv)

/-- **`tanBracket`** is the dummy bracket (only when `|cos x| ≤ sinCosEps ex w`) or encloses
`tan |x|`, with a width bound for every positive lower bound `m` of the bracket of `|cos x|`. -/
theorem tanBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    (tanBracket x ex w = (-one, one) ∧ |Real.cos xv| ≤ sinCosEps ex w) ∨
      ∃ b1 : ℝ, 0 < b1 ∧ |Real.cos xv| - sinCosEps ex w ≤ b1 ∧ ∀ m : ℝ, 0 < m → m ≤ b1 →
        IsEnclW (tanBracket x ex w) (Real.tan |xv|)
          ((sinCosEps ex w + 2 * sinCosEps ex w / m + 8 * (1 / 2 : ℝ) ^ (w + 12)) / m) := by
  obtain ⟨hS, hC⟩ := sinCosBracket_spec hx hex hw
  have hδ1 := sinCosEps_le_one ex hw
  obtain ⟨b1, b2, hb1, hb2, hb10, hb1c, hcb2, hbw⟩ := enclAbs_spec hC
  obtain ⟨cl, ch, hcl, hch, hc1, hc2, hc3⟩ := hC
  rcases eq_or_lt_of_le hb10 with h0 | hpos
  · left
    have hz : (enclAbs (sinCosBracket x ex w).2).1 = zero :=
      eq_zero_of_toVal_eq_zero (by rw [hb1, ← h0])
    refine ⟨?_, by linarith⟩
    unfold tanBracket
    dsimp only
    rw [hz]
  · right
    refine ⟨b1, hpos, by linarith, fun m hm hmb => ?_⟩
    have hnz : (enclAbs (sinCosBracket x ex w).2).1 ≠ zero := fun h => by
      rw [h, toVal_zero'] at hb1
      have : (0 : ℝ) = b1 := EReal.coe_eq_coe_iff.mp (Option.some.inj hb1)
      linarith
    have hq := enclDivSignedPos_spec hS hb1 hb2 hm hmb hb1c hcb2 hbw (Real.abs_sin_le_one _) hδ1
      (W := w + 12) (by omega)
    -- the sign of the cosine
    have hnch : (-(sinCosBracket x ex w).2.2).toVal = some ((-ch : ℝ) : EReal) := by
      rw [toVal_neg, hch, Option.map_some, EReal.coe_neg]
    obtain ⟨cv, hcv, -, hcvle, -⟩ := clampNonneg_spec (toVal_maxOf hcl hnch)
    have hcvb : cv = b1 := EReal.coe_eq_coe_iff.mp (Option.some.inj (hcv.symm.trans hb1))
    have hmax : 0 < max cl (-ch) := by
      by_contra hcon
      push Not at hcon
      rw [max_eq_right hcon] at hcvle
      linarith
    have htan : Real.tan |xv| = Real.sin |xv| / Real.cos xv := by
      rw [Real.tan_eq_sin_div_cos, Real.cos_abs]
    unfold tanBracket
    dsimp only
    split
    · next h => exact absurd h hnz
    split_ifs with hneg
    · have hchn : ch < 0 := (toVal_sign_of_isNegative hch).1 hneg
      have hcos : Real.cos xv < 0 := lt_of_le_of_lt hc2 hchn
      obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := hq
      rw [abs_of_neg hcos] at h1 h2
      have e : Real.sin |xv| / -Real.cos xv = -Real.tan |xv| := by rw [htan, div_neg]
      rw [e] at h1 h2
      refine ⟨-hi, -lo, ?_, ?_, by linarith, by linarith, by linarith⟩
      · show (-(enclDivSignedPos _ _ _).2).toVal = _
        rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
      · show (-(enclDivSignedPos _ _ _).1).toVal = _
        rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    · have hch0 : 0 ≤ ch := (toVal_sign_of_isNegative hch).2 (by simpa using hneg)
      have hclp : 0 < cl := by
        rcases lt_max_iff.mp hmax with h | h
        · exact h
        · linarith
      have hcos : 0 < Real.cos xv := lt_of_lt_of_le hclp hc1
      rw [abs_of_pos hcos, ← htan] at hq
      exact hq

/-- The width of `tanBracket` once the bracket of `cos x` (width `sinCosEps ex w`) is at most
half of `c = |cos x|`. -/
noncomputable def tanEps (c : ℝ) (ex : AzInt) (w : ℕ) : ℝ :=
  (sinCosEps ex w + 2 * sinCosEps ex w / (c / 2) + 8 * (1 / 2 : ℝ) ^ (w + 12)) / (c / 2)

/-- `tanEps c ex w → 0` as `w → ∞`. -/
theorem tendsto_tanEps (c : ℝ) (ex : AzInt) :
    Filter.Tendsto (tanEps c ex) Filter.atTop (nhds 0) := by
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp (Filter.tendsto_add_atTop_nat 12)
  have h := (((tendsto_sinCosEps ex).const_mul (1 + 2 / (c / 2))).add
    (h2.const_mul 8)).div_const (c / 2)
  simp only [mul_zero, add_zero, zero_div] at h
  refine h.congr fun w => ?_
  simp only [Function.comp, tanEps]
  ring

/-- **`tanBracket` encloses `tan |x|`** with width at most `tanEps |cos x| ex w`, as soon as
`sinCosEps ex w ≤ |cos x| / 2`. -/
theorem tanBracket_width {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) (hc0 : 0 < |Real.cos xv|)
    (hc : sinCosEps ex w ≤ |Real.cos xv| / 2) :
    IsEnclW (tanBracket x ex w) (Real.tan |xv|) (tanEps |Real.cos xv| ex w) := by
  rcases tanBracket_spec hx hex hw with ⟨-, h⟩ | ⟨b1, -, hb1, h⟩
  · linarith
  · exact h (|Real.cos xv| / 2) (by linarith) (by linarith)

/-- From an enclosure by `tanBracket` to the `Roundable`s of `tanApprox neg`. -/
theorem tanApprox_of_isEnclW (neg : Bool) {x : AzFloat} {ex : AzInt} {w : ℕ} {v W : ℝ}
    (h : IsEnclW (tanBracket x ex w) v W) :
    ∃ lv hv : ℝ, Rounds (tanApprox neg x ex w).1 lv ∧ Rounds (tanApprox neg x ex w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * v ∧ (if neg then -1 else 1) * v ≤ hv ∧ hv - lv ≤ W := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := h
  simp only [tanApprox]
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
    have hnlo : (-(tanBracket x ex w).2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(tanBracket x ex w).1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- At every level `w ≥ 64` the bracket of `tanApprox neg` encloses `± tan |x|` or is rejected
by `roundingPossible`. -/
theorem tanApprox_valid_or_none (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ}
    (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (tanApprox neg x ex w).1 lv ∧ Rounds (tanApprox neg x ex w).2 hv ∧
        lv ≤ (if neg then -1 else 1) * Real.tan |xv| ∧
        (if neg then -1 else 1) * Real.tan |xv| ≤ hv) ∨
      roundingPossible (tanApprox neg x ex w).1 (tanApprox neg x ex w).2 p mode = none := by
  rcases tanBracket_spec hx hex hw with ⟨hd, -⟩ | ⟨b1, hb1, -, h⟩
  · right
    have hnn : (-(-one : AzFloat)).toVal = some ((1 : ℝ) : EReal) := by
      rw [toVal_neg, toVal_neg_one_float, Option.map_some, ← EReal.coe_neg, neg_neg]
    simp only [tanApprox, hd]
    cases neg with
    | false => exact roundingPossible_none_of_neg_one_one toVal_neg_one_float toVal_one' p mode
    | true => exact roundingPossible_none_of_neg_one_one toVal_neg_one_float hnn p mode
  · left
    obtain ⟨lv, hv, hl, hh, h1, h2, -⟩ := tanApprox_of_isEnclW neg (h b1 hb1 le_rfl)
    exact ⟨lv, hv, hl, hh, h1, h2⟩

/-- The Ziv certificate for `tan x`, `x` a nonzero finite float of sign `¬ neg`. -/
theorem tanApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hneg : neg = true ↔ xv < 0) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (tanApprox neg x ex (w₀ * 2 ^ f)).1
      (tanApprox neg x ex (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hc0 : 0 < |Real.cos xv| := abs_pos.mpr (irrational_cos_of_toVal hx hx0).ne_zero
  obtain ⟨W₁, hW₁⟩ := ((tendsto_sinCosEps ex).eventually
    (gt_mem_nhds (half_pos hc0))).exists_forall_of_atTop
  have hval := tan_eq_of_neg_iff hneg
  refine exists_isSome_of_irrational_threshold p mode (tanApprox neg x ex)
    (v := (if neg then -1 else 1) * Real.tan |xv|) ?_ (tanEps |Real.cos xv| ex)
    (tendsto_tanEps _ ex) (max 64 W₁)
    (fun w hw => tanApprox_of_isEnclW neg (tanBracket_width hx hex (le_of_max_le_left hw) hc0
      (hW₁ w (le_of_max_le_right hw)).le)) w₀ hw₀
  rw [← hval]
  exact irrational_tan_of_toVal hx hx0

/-! ### Tiny arguments -/

/-- `a < tan a ≤ a + a³` for `0 < a ≤ 1`. -/
theorem tan_bounds_of_small {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    a < Real.tan a ∧ Real.tan a ≤ a + a ^ 3 := by
  have hpi := Real.pi_gt_three
  refine ⟨Real.lt_tan ha0 (by linarith), ?_⟩
  have hcos := Real.one_sub_sq_div_two_le_cos (x := a)
  have hden : 0 < 1 - a ^ 2 / 2 := by nlinarith
  have hcpos : 0 < Real.cos a := lt_of_lt_of_le hden hcos
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcpos]
  have hsin := Real.sin_le ha0.le
  have h3 : 0 ≤ a + a ^ 3 := by positivity
  have h1a : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hstep : a ≤ (a + a ^ 3) * (1 - a ^ 2 / 2) := by
    nlinarith [mul_nonneg (pow_nonneg ha0.le 3) h1a]
  calc Real.sin a ≤ a := hsin
    _ ≤ (a + a ^ 3) * (1 - a ^ 2 / 2) := hstep
    _ ≤ (a + a ^ 3) * Real.cos a := mul_le_mul_of_nonneg_left hcos h3

/-- The tiny-argument path answers with the rounding of `tan x`. -/
theorem tanTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : tanTiny? s (finite s e q m hv) e q p mode = some r) :
    r = roundVal p mode (some ((Real.tan (finiteVal s e m) : ℝ) : EReal)) := by
  unfold tanTiny? at h
  dsimp only at h
  set w := max p q + zivGuardBits with hw
  have : NeZero (w + 8) := ⟨by omega⟩
  set xv := finiteVal s e m with hxv
  have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
  have hlt := (abs_finiteVal_bounds s e hv).2
  rw [← hxv] at hlt
  have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  set t := (2 : ℝ) ^ e.toInt with ht
  have ht0 : 0 < t := by positivity
  have habs : (finite s e q m hv).abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hd : (((finite s e q m hv).abs <<< e) <<< e).toVal = some ((a * t * t : ℝ) : EReal) :=
    toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal habs e) e
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs habs hd (w + 8)
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe habs)
  rw [fval_of_toVal_coe habs] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  by_cases hc : e.sign = false ∧ w + 8 ≤ e.abs.toNat
  swap
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)
  rw [ite_eq_left hc] at h
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [hc.1] at htoInt
  simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
  have ht1 : t ≤ 1 := by
    rw [ht, htoInt, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨hs1, hs2⟩ := tan_bounds_of_small ha0 (hlt.le.trans ht1)
  have hcube : a ^ 3 ≤ a * t * t := by
    have h1 : a * a ≤ t * t := mul_le_mul hlt.le hlt.le ha0.le ht0.le
    nlinarith
  have hsgn := finiteVal_sign_iff s e hv
  rw [← hxv] at hsgn
  cases s with
  | true =>
    simp only [↓reduceIte] at h
    have hpos : 0 < xv := hsgn.mp rfl
    have hax : a = xv := abs_of_pos hpos
    have hr := roundingPossible_eq' p mode (v := Real.tan a) hR1 hR2 hs1.le (by linarith)
      (Or.inl fun hEq => absurd hEq hs1.ne) h
    rw [hr, hax]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
    have hneg : xv < 0 := by
      rcases lt_or_gt_of_ne hx0 with h' | h'
      · exact h'
      · exact absurd (hsgn.mpr h') (by simp)
    have hax : xv = -a := by rw [ha, abs_of_neg hneg, neg_neg]
    have hr := roundingPossible_eq' p (-mode) (v := Real.tan a) hR1 hR2 hs1.le (by linarith)
      (Or.inl fun hEq => absurd hEq hs1.ne) hr'
    rw [hr, hax, Real.tan_neg]
    exact (roundVal_neg p mode (Real.tan a)).symm

end Azurite.AzFloat
