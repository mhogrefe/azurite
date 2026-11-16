/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CschBracket
import Azurite.AzFloat.Equiv.SinhRatBracket
import Azurite.AzFloat.Equiv.CoshBracket
import Azurite.AzFloat.Equiv.TanhBracket

/-!
# Equivalence: the brackets of `csch x` and `csch q`

`cschOfSinh_spec` (the reciprocal of an enclosure of `S ≥ lb ≥ c > 0`, width at most
`cschWidth δ c W`), `cschBracket_spec`, `cschApprox_spec`, `irrational_csch_of_toVal`,
`cschApprox_isSome_exists`, the rational versions `cschRatBracket_spec`, `cschRatApprox_spec`,
`irrational_csch_toRat`, `cschRatApprox_isSome_exists`, and the tiny-argument path
`csch_bounds_of_small`, `cschTinyCore?_eq`, `cschTiny?_eq`, `cschTinyRat?_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- The width of `cschOfSinh` at precision `w` on an enclosure of width `δ` of `S ≥ c`. -/
noncomputable def cschWidth (δ c : ℝ) (w : ℕ) : ℝ := δ / c ^ 2 + 4 * (1 / c) * (1 / 2 : ℝ) ^ w

theorem tendsto_cschWidth (c : ℝ) {E : ℕ → ℝ} (hE : Filter.Tendsto E Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun w => cschWidth (E w) c w) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := (hE.div_const (c ^ 2)).add (hp.const_mul (4 * (1 / c)))
  have h0 : (0 / c ^ 2 + 4 * (1 / c) * 0 : ℝ) = 0 := by ring
  rw [h0] at h
  exact h

/-- **`cschOfSinh` encloses `1/S`** for an enclosure of `S` of width at most `δ` and a float
lower bound `c ≤ lb ≤ S`, `c > 0`. -/
theorem cschOfSinh_spec {s : Encl} {lb : AzFloat} {S δ c lbv : ℝ} (hs : IsEnclW s S δ)
    (hlb : lb.toVal = some (lbv : EReal)) (hc0 : 0 < c) (hclb : c ≤ lbv) (hlbS : lbv ≤ S)
    {W : ℕ} (hW : 1 ≤ W) : IsEnclW (cschOfSinh s lb W) S⁻¹ (cschWidth δ c W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := hs
  have hl := toVal_maxOf hlo hlb
  set l := max lo lbv with hldef
  have hlc : c ≤ l := hclb.trans (le_max_right _ _)
  have hlS : l ≤ S := max_le h1 hlbS
  have hlo' : lo ≤ l := le_max_left _ _
  have hl0 : 0 < l := lt_of_lt_of_le hc0 hlc
  have hhi0 : 0 < hi := lt_of_lt_of_le hl0 (hlS.trans h2)
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  obtain ⟨q1, hq1, hq1a, hq1b⟩ := divFloor_abs toVal_one' hhi hhi0.ne' W
  obtain ⟨q2, hq2, hq2a, hq2b⟩ := divCeiling_abs toVal_one' hl hl0.ne' W
  have hil0 : 0 < 1 / l := by positivity
  have hih0 : 0 < 1 / hi := by positivity
  rw [abs_of_pos hih0] at hq1b
  rw [abs_of_pos hil0] at hq2b
  have hilc : 1 / l ≤ 1 / c := one_div_le_one_div_of_le hc0 hlc
  have hihc : 1 / hi ≤ 1 / c := one_div_le_one_div_of_le hc0 (hlc.trans (hlS.trans h2))
  have hSi : S⁻¹ = 1 / S := (one_div S).symm
  have hiS : 1 / hi ≤ 1 / S := one_div_le_one_div_of_le (lt_of_lt_of_le hl0 hlS) h2
  have hSl : 1 / S ≤ 1 / l := one_div_le_one_div_of_le hl0 hlS
  have hdiff : 1 / l - 1 / hi ≤ δ / c ^ 2 := by
    have e : 1 / l - 1 / hi = (hi - l) / (l * hi) := by
      field_simp
    rw [e]
    have hδ0 : 0 ≤ δ := by linarith [hlS.trans h2]
    refine div_le_div₀ hδ0 (by linarith) (by positivity) ?_
    rw [sq]
    exact mul_le_mul hlc (hlc.trans (hlS.trans h2)) hc0.le hl0.le
  have e1 : 1 / hi * (1 / 2 : ℝ) ^ W ≤ 1 / c * (1 / 2 : ℝ) ^ W :=
    mul_le_mul_of_nonneg_right hihc hη0
  have e2 : 1 / l * (1 / 2 : ℝ) ^ W ≤ 1 / c * (1 / 2 : ℝ) ^ W :=
    mul_le_mul_of_nonneg_right hilc hη0
  rw [hSi]
  unfold cschWidth
  exact ⟨q1, q2, hq1, hq2, by linarith, by linarith, by linarith⟩

/-- `csch x` from `csch |x|`. -/
theorem csch_abs_eq {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    (if neg then -1 else 1) * (Real.sinh |xv|)⁻¹ = (Real.sinh xv)⁻¹ := by
  cases neg with
  | true =>
    have hlt : xv < 0 := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg hlt, sinh_neg, inv_neg]
    ring
  | false =>
    have hpos : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg hpos]

/-- `x = sign · |x|` for the hyperbolic cosecant. -/
theorem csch_sign_eq {s : Bool} {xv : ℝ} (hs : s = true ↔ 0 < xv) (hx0 : xv ≠ 0) :
    (if s then 1 else -1) * (Real.sinh |xv|)⁻¹ = (Real.sinh xv)⁻¹ := by
  have hneg : (!s) = true ↔ xv < 0 := by
    cases s with
    | true => simpa using (hs.mp rfl).le
    | false =>
      simp only [Bool.not_false, true_iff]
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact h
      · exact absurd (hs.mpr h) (by simp)
  rw [← csch_abs_eq hneg]
  cases s <;> simp

/-! ### The float bracket -/

/-- The width bound of `cschBracket`. -/
noncomputable def cschEps (av : ℝ) (c w : ℕ) : ℝ := cschWidth (sinhEps av c w) av w

theorem tendsto_cschEps (av : ℝ) (c : ℕ) :
    Filter.Tendsto (cschEps av c) Filter.atTop (nhds 0) :=
  tendsto_cschWidth av (tendsto_sinhEps av c)

/-- **`cschBracket a e w` encloses `csch a`** for a float `0 < a < 2^e`. -/
theorem cschBracket_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) (e : AzInt) (hae : av < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (cschBracket a e w) (Real.sinh av)⁻¹ (cschEps av (expM1Comp e) w) := by
  have h := cschOfSinh_spec (sinhBracket_spec ha ha0 e hae hw) ha ha0 le_rfl
    (self_le_sinh_iff.mpr ha0.le) (W := w + 16) (by omega)
  refine h.mono ?_
  unfold cschEps cschWidth
  have hpw : (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hc : 0 ≤ 4 * (1 / av) := by positivity
  have := mul_le_mul_of_nonneg_left hpw hc
  linarith

/-- `cschApprox neg` as a pair of `Roundable`s bracketing `csch x`. -/
theorem cschApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {e : AzInt} (hxe : |xv| < (2 : ℝ) ^ e.toInt) {neg : Bool}
    (hneg : neg = true ↔ xv < 0) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (cschApprox neg x e w).1 lv ∧ Rounds (cschApprox neg x e w).2 hv ∧
      lv ≤ (Real.sinh xv)⁻¹ ∧ (Real.sinh xv)⁻¹ ≤ hv ∧
      hv - lv ≤ cschEps |xv| (expM1Comp e) w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    cschBracket_spec habs (abs_pos.mpr hx0) e hxe hw
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  rw [csch_abs_eq hneg] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `csch x` is irrational for a finite float `x ≠ 0`. -/
theorem irrational_csch_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.sinh xv)⁻¹ :=
  (irrational_sinh_of_toVal hx hx0).inv

/-- The Ziv certificate for `csch x`, `x` a finite nonzero float. -/
theorem cschApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {e : AzInt}
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cschApprox neg x e (w₀ * 2 ^ f)).1
      (cschApprox neg x e (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (cschApprox neg x e)
    (irrational_csch_of_toVal hx hx0) (cschEps |xv| (expM1Comp e)) (tendsto_cschEps _ _) 64
    (fun _ hw => cschApprox_spec hx hx0 hxe hneg hw) w₀ hw₀

/-! ### The rational bracket -/

/-- The width bound of `cschRatBracket`. -/
noncomputable def cschRatEps (q : AzRat) (w : ℕ) : ℝ :=
  cschWidth (sinhRatEps q w) (|((AzRat.toRat q : ℚ) : ℝ)| / 2) w

theorem tendsto_cschRatEps (q : AzRat) :
    Filter.Tendsto (cschRatEps q) Filter.atTop (nhds 0) :=
  tendsto_cschWidth _ (tendsto_sinhRatEps q)

/-- **`cschRatBracket q w` encloses `csch |q|`** for a rational `q ≠ 0`. -/
theorem cschRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    IsEnclW (cschRatBracket q w) (Real.sinh |((AzRat.toRat q : ℚ) : ℝ)|)⁻¹
      (cschRatEps q w) := by
  have : NeZero (w + 16) := ⟨by omega⟩
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have ha0 := abs_pos.mpr hq0
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs q.abs (w + 16)
  rw [habs] at hl1 hl2
  rw [abs_abs] at hl2
  have hη : (1 / 2 : ℝ) ^ (w + 16) ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hlc : |((AzRat.toRat q : ℚ) : ℝ)| / 2 ≤ l := by nlinarith
  have h := cschOfSinh_spec (sinhRatBracket_spec hw q h0) hl (by positivity) hlc
    (hl1.trans (self_le_sinh_iff.mpr ha0.le)) (W := w + 16) (by omega)
  refine h.mono ?_
  unfold cschRatEps cschWidth
  have hpw : (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hc : 0 ≤ 4 * (1 / (|((AzRat.toRat q : ℚ) : ℝ)| / 2)) := by positivity
  have := mul_le_mul_of_nonneg_left hpw hc
  linarith

/-- `cschRatApprox` as a pair of `Roundable`s bracketing `csch q`. -/
theorem cschRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    ∃ lv hv : ℝ, Rounds (cschRatApprox q w).1 lv ∧ Rounds (cschRatApprox q w).2 hv ∧
      lv ≤ (Real.sinh (AzRat.toRat q : ℝ))⁻¹ ∧ (Real.sinh (AzRat.toRat q : ℝ))⁻¹ ≤ hv ∧
      hv - lv ≤ cschRatEps q w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := cschRatBracket_spec hw q h0
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec (!q.sign) hlo hhi h1 h2
  rw [csch_abs_eq (toRat_neg_iff q h0)] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `csch q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_csch_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.sinh (AzRat.toRat q : ℝ))⁻¹ :=
  (irrational_sinh_toRat q h0).inv

/-- The Ziv certificate for `csch q`. -/
theorem cschRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cschRatApprox q (w₀ * 2 ^ f)).1
      (cschRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (cschRatApprox q) (irrational_csch_toRat q h0)
    (cschRatEps q) (tendsto_cschRatEps q) 64 (fun _ hw => cschRatApprox_spec hw q h0) w₀ hw₀

/-! ### Tiny arguments -/

/-- `1/a − a ≤ csch a < 1/a` for `0 < a ≤ 1`. -/
theorem csch_bounds_of_small {a : ℝ} (h0 : 0 < a) (h1 : a ≤ 1) :
    1 / a - a ≤ (Real.sinh a)⁻¹ ∧ (Real.sinh a)⁻¹ < 1 / a := by
  obtain ⟨hs1, hs2⟩ := sinh_tiny_bounds a h0 h1
  have hs0 : 0 < Real.sinh a := h0.trans hs1
  rw [← one_div]
  refine ⟨?_, one_div_lt_one_div_of_lt h0 hs1⟩
  rw [le_div_iff₀ hs0]
  have hnn : 0 ≤ 1 / a - a := by
    rw [sub_nonneg, le_div_iff₀ h0]
    nlinarith
  have e : (1 / a - a) * (a + a ^ 3) = 1 - a ^ 4 := by
    field_simp
    ring
  have ha4 : 0 ≤ a ^ 4 := by positivity
  calc (1 / a - a) * Real.sinh a ≤ (1 / a - a) * (a + a ^ 3) :=
        mul_le_mul_of_nonneg_left hs2 hnn
    _ ≤ 1 := by rw [e]; linarith

theorem cschTinyCore?_cond {pos : Bool} {alo ahi : AzFloat} {e : AzInt} {p : ℕ}
    {mode : RoundingMode} {r : AzFloat × Ordering}
    (h : cschTinyCore? pos alo ahi e p mode = some r) :
    e.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e.abs.toNat := by
  unfold cschTinyCore? at h
  by_contra hc
  rw [ite_eq_right hc] at h
  cases h

/-- **The tiny-argument test answers with the rounding of `± csch a`.** -/
theorem cschTinyCore?_eq {pos : Bool} {alo ahi : AzFloat} {e : AzInt} {p : ℕ} [NeZero p]
    {mode : RoundingMode} {r : AzFloat × Ordering} {a l h : ℝ}
    (hl : alo.toVal = some (l : EReal)) (hh : ahi.toVal = some (h : EReal)) (hl0 : 0 < l)
    (hla : l ≤ a) (hah : a ≤ h) (hlt : a < (2 : ℝ) ^ e.toInt)
    (hirr : Irrational (Real.sinh a)⁻¹) (hT : cschTinyCore? pos alo ahi e p mode = some r) :
    r = roundVal p mode
      (some (((if pos then 1 else -1) * (Real.sinh a)⁻¹ : ℝ) : EReal)) := by
  have hc := cschTinyCore?_cond hT
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [hc.1] at htoInt
  simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
  have ht1 : (2 : ℝ) ^ e.toInt ≤ 1 := by
    rw [htoInt, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have ha0 : 0 < a := lt_of_lt_of_le hl0 hla
  have hh0 : 0 < h := lt_of_lt_of_le ha0 hah
  obtain ⟨hb1, hb2⟩ := csch_bounds_of_small ha0 (hlt.le.trans ht1)
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  unfold cschTinyCore? at hT
  rw [ite_eq_left hc] at hT
  obtain ⟨c, hcv, hc1, -⟩ := divCeiling_abs toVal_one' hl hl0.ne' (p + zivGuardBits + 8)
  obtain ⟨f, hfv, hf1, -⟩ := divFloor_abs toVal_one' hh hh0.ne' (p + zivGuardBits + 8)
  have hlo : (-(divPrecRound one alo (p + zivGuardBits + 8) .Ceiling).1).toVal
      = some ((-c : ℝ) : EReal) := by
    rw [toVal_neg, hcv, Option.map_some, EReal.coe_neg]
  have hnf : (-(divPrecRound one ahi (p + zivGuardBits + 8) .Floor).1).toVal
      = some ((-f : ℝ) : EReal) := by
    rw [toVal_neg, hfv, Option.map_some, EReal.coe_neg]
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hnf hh (p + zivGuardBits + 8)
  have h1 : 1 / h ≤ 1 / a := one_div_le_one_div_of_le ha0 hah
  have h2 : 1 / a ≤ 1 / l := one_div_le_one_div_of_le hl0 hla
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hvB := not_mem_floatSet_of_irrational p hirr.neg
  cases pos with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul] at hT ⊢
    exact roundingPossible_eq' p mode hR1 hR2 (by linarith) (by linarith) (Or.inr hvB) hT
  | true =>
    simp only [↓reduceIte, one_mul] at hT ⊢
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hT
    have hr := roundingPossible_eq' p (-mode) hR1 hR2 (v := -(Real.sinh a)⁻¹) (by linarith)
      (by linarith) (Or.inr hvB) hr'
    rw [hr]
    have := roundVal_neg p mode (-(Real.sinh a)⁻¹)
    rw [neg_neg] at this
    exact this.symm

/-- The tiny-argument path of `csch x` answers with the rounding of `csch x`. -/
theorem cschTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : cschTiny? s (finite s e q m hv) e p mode = some r) :
    r = roundVal p mode (some (((Real.sinh (finiteVal s e m))⁻¹ : ℝ) : EReal)) := by
  have hx : (finite s e q m hv).toVal = some ((finiteVal s e m : ℝ) : EReal) :=
    toVal_finite s e q m hv
  have hx0 : finiteVal s e m ≠ 0 := finiteVal_ne_zero s e hv
  have habs : (finite s e q m hv).abs.toVal = some ((|finiteVal s e m| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hirr : Irrational (Real.sinh |finiteVal s e m|)⁻¹ :=
    irrational_csch_of_toVal habs (abs_pos.mpr hx0).ne'
  rw [cschTinyCore?_eq habs habs (abs_pos.mpr hx0) le_rfl le_rfl
    (abs_finiteVal_bounds s e hv).2 hirr h, csch_sign_eq (finiteVal_sign_iff s e hv) hx0]

/-- The tiny-argument path of `csch q` answers with the rounding of `csch q`. -/
theorem cschTinyRat?_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (hT : cschTinyRat? q p mode = some r) :
    r = roundVal p mode (some (((Real.sinh (AzRat.toRat q : ℝ))⁻¹ : ℝ) : EReal)) := by
  unfold cschTinyRat? at hT
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
  have hirr : Irrational (Real.sinh |((AzRat.toRat q : ℚ) : ℝ)|)⁻¹ := by
    have h := (irrational_sinh_toRat q.abs (fun h => h0 h)).inv
    rwa [habs] at h
  rw [cschTinyCore?_eq hl hc hl0 hl1 hc1 hlt hirr hT,
    csch_sign_eq (toRat_sign_iff q h0) hq0]

end Azurite.AzFloat
