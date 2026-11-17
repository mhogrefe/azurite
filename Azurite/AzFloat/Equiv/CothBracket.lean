/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CothBracket
import Azurite.AzFloat.Equiv.TanhBracket
import Azurite.AzFloat.Equiv.CscBracket

/-!
# Equivalence: the brackets of `coth x` and `coth q`

`coth_eq_expm1` (`1/tanh a = 1 + 2/v`, `v = e^(2a) − 1`), `cothOfExpM1_spec` (width at most
`cothWidth δ c W`), `cothOfExpM1_width`, `cothBracket_spec`, `cothApprox_spec`,
`irrational_coth_of_toVal`, `cothApprox_isSome_exists`, the rational versions
`cothRatBracket_spec`, `cothRatApprox_spec`, `irrational_coth_toRat`,
`cothRatApprox_isSome_exists`, the tiny-argument path `coth_bounds_of_small`, `cothTiny?_eq`,
`cothTinyRat?_eq`, and the large-argument path `cothNearOne?_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- `1/tanh a = 1 + 2/v` with `v = e^(2a) − 1`, for `a > 0`. -/
theorem coth_eq_expm1 {a : ℝ} (ha : 0 < a) :
    (Real.tanh a)⁻¹ = 1 + 2 / (Real.exp (2 * a) - 1) := by
  have hv : 0 < Real.exp (2 * a) - 1 := by
    have := add_one_lt_exp (by linarith : 2 * a ≠ 0)
    linarith
  rw [tanh_eq_expm1, inv_div]
  field_simp
  ring

/-- The width of `cothOfExpM1` at precision `w` on an enclosure of width `δ` of `V ≥ c`. -/
noncomputable def cothWidth (δ c : ℝ) (w : ℕ) : ℝ :=
  2 * δ / c ^ 2 + (4 + 10 * (2 / c)) * (1 / 2 : ℝ) ^ w

theorem tendsto_cothWidth (c : ℝ) {E : ℕ → ℝ} (hE : Filter.Tendsto E Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun w => cothWidth (E w) c w) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := ((hE.const_mul 2).div_const (c ^ 2)).add (hp.const_mul (4 + 10 * (2 / c)))
  have h0 : (2 * 0 / c ^ 2 + (4 + 10 * (2 / c)) * 0 : ℝ) = 0 := by ring
  rw [h0] at h
  exact h

/-- The real arithmetic of `cothOfExpM1`: the enclosure and its width. -/
theorem cothStep_bounds {V l h c K q1 s1 q2 s2 η δ : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hc0 : 0 < c) (hcl : c ≤ l) (hlV : l ≤ V) (hVh : V ≤ h) (hδ : h - l ≤ δ) (hK : K = 2 / c)
    (hq1a : q1 ≤ 2 / h) (hq1b : 2 / h ≤ q1 + 2 * |2 / h| * η)
    (hs1a : s1 ≤ 1 + q1) (hs1b : 1 + q1 ≤ s1 + 2 * |1 + q1| * η)
    (hq2a : 2 / l ≤ q2) (hq2b : q2 ≤ 2 / l + 2 * |2 / l| * η)
    (hs2a : 1 + q2 ≤ s2) (hs2b : s2 ≤ 1 + q2 + 2 * |1 + q2| * η) :
    s1 ≤ 1 + 2 / V ∧ 1 + 2 / V ≤ s2 ∧ s2 - s1 ≤ 2 * δ / c ^ 2 + (4 + 10 * K) * η := by
  have hl0 : 0 < l := lt_of_lt_of_le hc0 hcl
  have hV0 : 0 < V := lt_of_lt_of_le hl0 hlV
  have hh0 : 0 < h := lt_of_lt_of_le hV0 hVh
  have hK0 : 0 < K := by rw [hK]; positivity
  have h2h0 : 0 < 2 / h := by positivity
  have h2l0 : 0 < 2 / l := by positivity
  rw [abs_of_pos h2h0] at hq1b
  rw [abs_of_pos h2l0] at hq2b
  have h2lK : 2 / l ≤ K := by
    rw [hK]
    exact div_le_div_of_nonneg_left (by norm_num) hc0 hcl
  have h2hK : 2 / h ≤ K := by
    rw [hK]
    exact div_le_div_of_nonneg_left (by norm_num) hc0 (hcl.trans (hlV.trans hVh))
  have h2hV : 2 / h ≤ 2 / V := div_le_div_of_nonneg_left (by norm_num) hV0 hVh
  have h2Vl : 2 / V ≤ 2 / l := div_le_div_of_nonneg_left (by norm_num) hl0 hlV
  have e1 : 2 / h * η ≤ K * η := mul_le_mul_of_nonneg_right h2hK hη0
  have e2 : 2 / l * η ≤ K * η := mul_le_mul_of_nonneg_right h2lK hη0
  have hq1 : 0 ≤ q1 := by nlinarith
  have hq2 : 0 ≤ q2 := h2l0.le.trans hq2a
  rw [abs_of_nonneg (by linarith)] at hs1b hs2b
  have hKη : K * η ≤ K / 2 := by nlinarith
  have hq2u : q2 ≤ 2 * K := by linarith
  have hq1u : q1 ≤ K := by linarith
  refine ⟨by linarith, by linarith, ?_⟩
  have hdiff : 2 / l - 2 / h ≤ 2 * δ / c ^ 2 := by
    have e : 2 / l - 2 / h = 2 * (h - l) / (l * h) := by
      field_simp
    rw [e]
    have hδ0 : 0 ≤ δ := by linarith [hlV.trans hVh]
    refine div_le_div₀ (by linarith) (by linarith) (by positivity) ?_
    rw [sq]
    exact mul_le_mul hcl (hcl.trans (hlV.trans hVh)) hc0.le hl0.le
  have e3 : (1 + q2) * η ≤ (1 + 2 * K) * η := mul_le_mul_of_nonneg_right (by linarith) hη0
  have e4 : (1 + q1) * η ≤ (1 + K) * η := mul_le_mul_of_nonneg_right (by linarith) hη0
  nlinarith

/-- **`cothOfExpM1` encloses `1 + 2/V`** for an enclosure `[vl, vh]` of `V` and a float lower
bound `c ≤ lb ≤ V`, `c > 0`. -/
theorem cothOfExpM1_spec {v : Encl} {lb : AzFloat} {V vl vh c lbv : ℝ}
    (hlo : v.1.toVal = some (vl : EReal)) (hhi : v.2.toVal = some (vh : EReal)) (h1 : vl ≤ V)
    (h2 : V ≤ vh) (hlb : lb.toVal = some (lbv : EReal)) (hc0 : 0 < c) (hclb : c ≤ lbv)
    (hlbV : lbv ≤ V) {W : ℕ} (hW : 1 ≤ W) :
    IsEnclW (cothOfExpM1 v lb W) (1 + 2 / V) (cothWidth (vh - vl) c W) := by
  have : NeZero W := ⟨by omega⟩
  have hl := toVal_maxOf hlo hlb
  set l := max vl lbv with hldef
  have hlc : c ≤ l := hclb.trans (le_max_right _ _)
  have hlV : l ≤ V := max_le h1 hlbV
  have hlo' : vl ≤ l := le_max_left _ _
  have hl0 : 0 < l := lt_of_lt_of_le hc0 hlc
  have hh0 : 0 < vh := lt_of_lt_of_le hl0 (hlV.trans h2)
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hη : (1 / 2 : ℝ) ^ W ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hW
      _ = 1 / 2 := by norm_num
  obtain ⟨q1, hq1, hq1a, hq1b⟩ := divFloor_abs toVal_two_float hhi hh0.ne' W
  obtain ⟨s1, hs1, hs1a, hs1b⟩ := addFloor_abs toVal_one' hq1 W
  obtain ⟨q2, hq2, hq2a, hq2b⟩ := divCeiling_abs toVal_two_float hl hl0.ne' W
  obtain ⟨s2, hs2, hs2a, hs2b⟩ := addCeiling_abs toVal_one' hq2 W
  obtain ⟨b1, b2, b3⟩ := cothStep_bounds hη0 hη hc0 hlc hlV h2 (δ := vh - vl) (by linarith)
    rfl hq1a hq1b hs1a hs1b hq2a hq2b hs2a hs2b
  exact ⟨s1, s2, hs1, hs2, b1, b2, b3⟩

/-- **`cothOfExpM1` at precision `w + 16` encloses `coth a`**, `a > 0`, from an enclosure of
`e^(2a) − 1` of width at most `E`, with width at most `cothWidth E c w`. -/
theorem cothOfExpM1_width {v : Encl} {lb : AzFloat} {av lo hi E c lbv : ℝ}
    (hlo : v.1.toVal = some (lo : EReal)) (hhi : v.2.toVal = some (hi : EReal)) (ha0 : 0 < av)
    (h1 : lo ≤ Real.exp (2 * av) - 1) (h2 : Real.exp (2 * av) - 1 ≤ hi) (h3 : hi - lo ≤ E)
    (hlb : lb.toVal = some (lbv : EReal)) (hc0 : 0 < c) (hclb : c ≤ lbv)
    (hlbV : lbv ≤ 2 * av) (w : ℕ) :
    IsEnclW (cothOfExpM1 v lb (w + 16)) (Real.tanh av)⁻¹ (cothWidth E c w) := by
  have hV : 2 * av ≤ Real.exp (2 * av) - 1 := by
    have := add_one_le_exp (2 * av)
    linarith
  have hs := cothOfExpM1_spec hlo hhi h1 h2 hlb hc0 hclb (hlbV.trans hV) (W := w + 16)
    (by omega)
  rw [← coth_eq_expm1 ha0] at hs
  refine hs.mono ?_
  unfold cothWidth
  have hpw : (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hc : 0 ≤ 4 + 10 * (2 / c) := by positivity
  have hm := mul_le_mul_of_nonneg_left hpw hc
  have hd : 2 * (hi - lo) / c ^ 2 ≤ 2 * E / c ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- `coth x` from `coth |x|`. -/
theorem coth_abs_eq {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    (if neg then -1 else 1) * (Real.tanh |xv|)⁻¹ = (Real.tanh xv)⁻¹ := by
  cases neg with
  | true =>
    have hlt : xv < 0 := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg hlt, tanh_neg, inv_neg]
    ring
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg hpos]

/-- `x = sign · |x|` for the hyperbolic cotangent. -/
theorem coth_sign_eq {s : Bool} {xv : ℝ} (hs : s = true ↔ 0 < xv) (hx0 : xv ≠ 0) :
    (if s then 1 else -1) * (Real.tanh |xv|)⁻¹ = (Real.tanh xv)⁻¹ := by
  have hneg : (!s) = true ↔ xv < 0 := by
    cases s with
    | true => simpa using (hs.mp rfl).le
    | false =>
      simp only [Bool.not_false, true_iff]
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact h
      · exact absurd (hs.mpr h) (by simp)
  rw [← coth_abs_eq hneg]
  cases s <;> simp

/-! ### The float bracket -/

/-- The width bound of `cothBracket`. -/
noncomputable def cothEps (av : ℝ) (c w : ℕ) : ℝ :=
  cothWidth (expM1Eps (2 * av) c w) (2 * av) w

theorem tendsto_cothEps (av : ℝ) (c : ℕ) :
    Filter.Tendsto (cothEps av c) Filter.atTop (nhds 0) :=
  tendsto_cothWidth _ (tendsto_expM1Eps _ _)

/-- **`cothBracket a e w` encloses `coth a`** for a float `0 < a < 2^e`. -/
theorem cothBracket_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) (e : AzInt) (hae : av < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (cothBracket a e w) (Real.tanh av)⁻¹
      (cothEps av (expM1Comp (e + AzInt.ofInt 1)) w) := by
  have h2a : (a <<< AzInt.ofInt 1).toVal = some ((2 * av : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal ha (AzInt.ofInt 1)
    rw [AzInt.toInt_ofInt, zpow_one, mul_comm] at h
    exact h
  have hlt : |2 * av| < (2 : ℝ) ^ (e + AzInt.ofInt 1).toInt := by
    rw [AzInt.toInt_add, AzInt.toInt_ofInt, zpow_add₀ (by norm_num), zpow_one,
      abs_of_pos (by linarith)]
    linarith
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expM1Bracket_spec h2a (e + AzInt.ofInt 1) hlt hw
  exact cothOfExpM1_width hlo hhi ha0 h1 h2 h3 h2a (by linarith) le_rfl le_rfl w

/-- `cothApprox neg` as a pair of `Roundable`s bracketing `coth x`. -/
theorem cothApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {e : AzInt} (hxe : |xv| < (2 : ℝ) ^ e.toInt) {neg : Bool}
    (hneg : neg = true ↔ xv < 0) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (cothApprox neg x e w).1 lv ∧ Rounds (cothApprox neg x e w).2 hv ∧
      lv ≤ (Real.tanh xv)⁻¹ ∧ (Real.tanh xv)⁻¹ ≤ hv ∧
      hv - lv ≤ cothEps |xv| (expM1Comp (e + AzInt.ofInt 1)) w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    cothBracket_spec habs (abs_pos.mpr hx0) e hxe hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  rw [coth_abs_eq hneg] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `coth x` is irrational for a finite float `x ≠ 0`. -/
theorem irrational_coth_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.tanh xv)⁻¹ :=
  (irrational_tanh_of_toVal hx hx0).inv

/-- The Ziv certificate for `coth x`, `x` a finite nonzero float. -/
theorem cothApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {e : AzInt}
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cothApprox neg x e (w₀ * 2 ^ f)).1
      (cothApprox neg x e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (cothApprox neg x e)
    (irrational_coth_of_toVal hx hx0) (cothEps |xv| (expM1Comp (e + AzInt.ofInt 1)))
    (tendsto_cothEps _ _) 64 (fun _ hw => cothApprox_spec hx hx0 hxe hneg hw) w₀ hw₀

/-! ### The rational bracket -/

/-- The width bound of `cothRatBracket`. -/
noncomputable def cothRatEps (q : AzRat) (w : ℕ) : ℝ :=
  cothWidth (expM1RatEps (AzRat.toRat (q.abs + q.abs) : ℝ)
    (expM1Comp (AzInt.ofInt (AzRat.floorLogBaseAbs 2 (q.abs + q.abs) + 2))) w)
    |((AzRat.toRat q : ℚ) : ℝ)| w

theorem tendsto_cothRatEps (q : AzRat) :
    Filter.Tendsto (cothRatEps q) Filter.atTop (nhds 0) :=
  tendsto_cothWidth _ (tendsto_expM1RatEps _ _)

/-- **`cothRatBracket q w` encloses `coth |q|`** for a rational `q ≠ 0`. -/
theorem cothRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    IsEnclW (cothRatBracket q w) (Real.tanh |((AzRat.toRat q : ℚ) : ℝ)|)⁻¹
      (cothRatEps q w) := by
  have : NeZero (w + 16) := ⟨by omega⟩
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have ha0 := abs_pos.mpr hq0
  have h2 : ((AzRat.toRat (q.abs + q.abs) : ℚ) : ℝ) = 2 * |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_add, AzRat.toRat_abs]
    push_cast
    ring
  have hne : (q.abs + q.abs).num ≠ 0 := fun h => by
    have := coe_toRat_eq_zero_of_num_eq_zero _ h
    rw [h2] at this
    linarith
  obtain ⟨lo, hi, hlo, hhi, h1, h2', h3⟩ := expM1RatBracket_spec hw (q.abs + q.abs) hne
  obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs (q.abs + q.abs) (w + 16)
  rw [h2] at h1 h2' hl1 hl2
  rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * |((AzRat.toRat q : ℚ) : ℝ)|)] at hl2
  have hη : (1 / 2 : ℝ) ^ (w + 16) ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hlc : |((AzRat.toRat q : ℚ) : ℝ)| ≤ l := by nlinarith
  exact cothOfExpM1_width hlo hhi ha0 h1 h2' h3 hl ha0 hlc hl1 w

/-- `cothRatApprox` as a pair of `Roundable`s bracketing `coth q`. -/
theorem cothRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    ∃ lv hv : ℝ, Rounds (cothRatApprox q w).1 lv ∧ Rounds (cothRatApprox q w).2 hv ∧
      lv ≤ (Real.tanh (AzRat.toRat q : ℝ))⁻¹ ∧ (Real.tanh (AzRat.toRat q : ℝ))⁻¹ ≤ hv ∧
      hv - lv ≤ cothRatEps q w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := cothRatBracket_spec hw q h0
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec (!q.sign) hlo hhi h1 h2
  rw [coth_abs_eq (toRat_neg_iff q h0)] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `coth q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_coth_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.tanh (AzRat.toRat q : ℝ))⁻¹ :=
  (irrational_tanh_toRat q h0).inv

/-- The Ziv certificate for `coth q`. -/
theorem cothRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cothRatApprox q (w₀ * 2 ^ f)).1
      (cothRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (cothRatApprox q) (irrational_coth_toRat q h0)
    (cothRatEps q) (tendsto_cothRatEps q) 64 (fun _ hw => cothRatApprox_spec hw q h0) w₀ hw₀

/-! ### Tiny arguments -/

/-- `1/a < coth a ≤ 1/a + a` for `0 < a ≤ 1`. -/
theorem coth_bounds_of_small {a : ℝ} (h0 : 0 < a) :
    1 / a < (Real.tanh a)⁻¹ ∧ (Real.tanh a)⁻¹ ≤ 1 / a + a := by
  have hT0 : 0 < Real.tanh a := by
    rw [tanh_eq_sinh_div_cosh]
    exact div_pos (sinh_pos_iff.mpr h0) (cosh_pos a)
  refine ⟨?_, ?_⟩
  · rw [← one_div]
    exact one_div_lt_one_div_of_lt hT0 (tanh_lt_self h0)
  · rw [coth_eq_expm1 h0]
    have hq := quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * a)
    have hv : 2 * a + 2 * a ^ 2 ≤ Real.exp (2 * a) - 1 := by nlinarith
    have hpos : 0 < 2 * a + 2 * a ^ 2 := by positivity
    have h1 : 2 / (Real.exp (2 * a) - 1) ≤ 2 / (2 * a + 2 * a ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) hpos hv
    have h2 : 1 + 2 / (2 * a + 2 * a ^ 2) = 1 / a + a - a ^ 2 / (1 + a) := by
      field_simp
      ring
    have h3 : 0 ≤ a ^ 2 / (1 + a) := by positivity
    linarith

/-- The tiny-argument path of `csc` answers with the rounding of `coth x`. -/
theorem cothTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : cscTiny? s (finite s e q m hv) e p mode = some r) :
    r = roundVal p mode (some (((Real.tanh (finiteVal s e m))⁻¹ : ℝ) : EReal)) := by
  have hx : (finite s e q m hv).toVal = some ((finiteVal s e m : ℝ) : EReal) :=
    toVal_finite s e q m hv
  have hx0 : finiteVal s e m ≠ 0 := finiteVal_ne_zero s e hv
  have habs : (finite s e q m hv).abs.toVal = some ((|finiteVal s e m| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have ha0 := abs_pos.mpr hx0
  have hirr : Irrational (Real.tanh |finiteVal s e m|)⁻¹ :=
    irrational_coth_of_toVal habs ha0.ne'
  rw [cscTinyCore?_eq_of habs habs ha0 le_rfl le_rfl (abs_finiteVal_bounds s e hv).2
    (fun _ => coth_bounds_of_small ha0) hirr h, coth_abs_eq (finiteVal_neg_iff s e hv)]

/-- The tiny-argument path of `csc q` answers with the rounding of `coth q`. -/
theorem cothTinyRat?_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (hT : cscTinyRat? q p mode = some r) :
    r = roundVal p mode (some (((Real.tanh (AzRat.toRat q : ℝ))⁻¹ : ℝ) : EReal)) := by
  unfold cscTinyRat? at hT
  have hcond := cond_of_guardedBy hT
  replace hT := eq_some_of_guardedBy hT
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  have ha0 := abs_pos.mpr hq0
  obtain ⟨rl, rh, h, hrl, hrh, hh, h1, h2, h3, -⟩ :=
    tinyRat_spec q (p + zivGuardBits + 8) hcond.1
  obtain ⟨hb1, hb2⟩ := coth_bounds_of_small ha0
  have hirr : Irrational (Real.tanh |((AzRat.toRat q : ℚ) : ℝ)|)⁻¹ := by
    have h := (irrational_tanh_toRat q.abs (fun h => h0 h)).inv
    rwa [habs] at h
  rw [tinyRecipOf?_eq hrl hrh hh (by linarith) (by linarith) hirr hT,
    coth_abs_eq (toRat_neg_iff q h0)]

/-! ### Large arguments -/

/-- **The large-argument path answers with the rounding of `± coth a`**, for `a > 0` and a
natural `N ≤ 2a`. -/
theorem cothNearOne?_eq {pos : Bool} {N p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {a : ℝ} (hN : (N : ℝ) ≤ 2 * a)
    (h : cothNearOne? pos N p mode = some r) :
    r = roundVal p mode (some (((if pos then 1 else -1) * (Real.tanh a)⁻¹ : ℝ) : EReal)) := by
  unfold cothNearOne? at h
  dsimp only at h
  set M := min N 4611686018427387904 with hMdef
  have hE : (AzInt.ofInt (2 - (M : Int))).toInt = (2 : ℤ) - M := AzInt.toInt_ofInt _
  have key : ∀ {m' : RoundingMode} {r' : AzFloat × Ordering},
      expNearOne? true (AzInt.ofInt (2 - (M : Int))) p m' = some r' →
      r' = roundVal p m' (some (((Real.tanh a)⁻¹ : ℝ) : EReal)) := by
    intro m' r' h'
    have hc := expNearOne?_cond h'
    rw [hE] at hc
    have hM1 : 1 ≤ M := by
      by_contra hcon
      have hM0 : M = 0 := by omega
      rw [hM0] at hc
      norm_num at hc
    have hMa : (M : ℝ) ≤ 2 * a :=
      le_trans (by exact_mod_cast min_le_left N 4611686018427387904) hN
    obtain ⟨hT0, hlog, hb⟩ := log_tanh_bound hM1 hMa
    rw [← hE, ← abs_neg] at hb
    have := expNearOne?_eq hb (neg_ne_zero.mpr hlog.ne) (by simp [hlog]) h'
    rwa [Real.exp_neg, Real.exp_log hT0] at this
  cases pos with
  | true =>
    simp only [↓reduceIte, one_mul] at h ⊢
    exact key h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul] at h ⊢
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [key hr', roundVal_neg]

end Azurite.AzFloat
