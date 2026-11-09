/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosBracket
import Azurite.AzFloat.Equiv.Interval
import Azurite.AzFloat.Equiv.Rem
import Azurite.AzFloat.Equiv.LambertWBracket
import Azurite.Transcendental.Cos
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Equivalence: the bracket of `cos x`

* `IsEnclW`/`IsEncl0W`: enclosures with a width bound, and the width-tracking versions of the
  interval operations (`IsEncl0W.mul`, `IsEncl0W.div_nat`, `IsEnclW.sub0`, `IsEnclW.add0`,
  `IsEnclW.widen0`, `enclClamp0_spec`, `enclAbs_spec`, `cosDouble_spec`).
* `abs_cos_sub_sum_le`: the alternating-series tail bound for the cosine series.
* `cosSeriesLoop_spec`, `cosSeries_spec`: the series encloses `cos m` for `|m| ≤ 1`, with width
  `cosSeriesEps W`.
* `cosBracket_spec`: `cosBracket x ex w` encloses `cos x` with width at most `cosEps ex w`;
  `tendsto_cosEps`; `cosApprox_spec`; `cosApprox_isSome_exists` (the Ziv certificate from
  `irrational_cos_rat`: the value of a nonzero float is a nonzero rational).
-/

open Finset

namespace Azurite.AzFloat

/-! ### Enclosures with width bounds -/

/-- `a` encloses `x` with width at most `δ`. -/
def IsEnclW (a : Encl) (x δ : ℝ) : Prop :=
  ∃ lo hi : ℝ, a.1.toVal = some (lo : EReal) ∧ a.2.toVal = some (hi : EReal) ∧ lo ≤ x ∧ x ≤ hi ∧
    hi - lo ≤ δ

/-- `a` encloses `x` with a nonnegative lower end and width at most `δ`. -/
def IsEncl0W (a : Encl) (x δ : ℝ) : Prop :=
  ∃ lo hi : ℝ, a.1.toVal = some (lo : EReal) ∧ a.2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧
    lo ≤ x ∧ x ≤ hi ∧ hi - lo ≤ δ

theorem IsEncl0W.toW {a : Encl} {x δ : ℝ} (h : IsEncl0W a x δ) : IsEnclW a x δ := by
  obtain ⟨lo, hi, hlo, hhi, -, h1, h2, h3⟩ := h
  exact ⟨lo, hi, hlo, hhi, h1, h2, h3⟩

theorem IsEnclW.mono {a : Encl} {x δ δ' : ℝ} (h : IsEnclW a x δ) (hδ : δ ≤ δ') :
    IsEnclW a x δ' := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := h
  exact ⟨lo, hi, hlo, hhi, h1, h2, h3.trans hδ⟩

theorem IsEncl0W.mono {a : Encl} {x δ δ' : ℝ} (h : IsEncl0W a x δ) (hδ : δ ≤ δ') :
    IsEncl0W a x δ' := by
  obtain ⟨lo, hi, hlo, hhi, h0, h1, h2, h3⟩ := h
  exact ⟨lo, hi, hlo, hhi, h0, h1, h2, h3.trans hδ⟩

theorem isEncl0W_exact {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (h0 : 0 ≤ xv) :
    IsEncl0W (Encl.exact x) xv 0 :=
  ⟨xv, xv, hx, hx, h0, le_rfl, le_rfl, by simp⟩

/-- `W 2^(−W)` is tiny from `W = 64` on. -/
theorem nat_mul_half_pow_le {W : ℕ} (hW : 64 ≤ W) : (W : ℝ) * (1 / 2 : ℝ) ^ W ≤ 1 / 10 ^ 16 := by
  have h := add_nine_mul_half_pow_le hW
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  calc (W : ℝ) * (1 / 2 : ℝ) ^ W ≤ ((W : ℝ) + 9) * (1 / 2 : ℝ) ^ W := by nlinarith
    _ ≤ 73 * (1 / 2 : ℝ) ^ 64 := h
    _ ≤ 1 / 10 ^ 16 := by norm_num

/-- The product of nonnegative enclosures of values `≤ 1` with widths `≤ 1`. -/
theorem IsEncl0W.mul {a b : Encl} {x y δ ε : ℝ} (ha : IsEncl0W a x δ) (hb : IsEncl0W b y ε)
    (hx : x ≤ 1) (hy : y ≤ 1) (hδ : δ ≤ 1) (hε : ε ≤ 1) {W : ℕ} (hW : 64 ≤ W) :
    IsEncl0W (Encl.mul W a b) (x * y) (δ + ε + δ * ε + 16 * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨la, ha', hla, hha, ha0, ha1, ha2, ha3⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, hb0, hb1, hb2, hb3⟩ := hb
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hδ0 : 0 ≤ δ := by linarith
  have hε0 : 0 ≤ ε := by linarith
  have hla1 : la ≤ 1 := by linarith
  have hlb1 : lb ≤ 1 := by linarith
  obtain ⟨lo, hlo, hlof⟩ := mulFloor_err hla hlb W (mul_nonneg ha0 hb0)
  obtain ⟨hi, hhi, hhic⟩ := mulCeiling_err hha hhb W (mul_nonneg (by linarith) (by linarith))
  refine ⟨lo, hi, hlo, hhi, hlof.nonneg, hlof.le.trans (mul_le_mul ha1 hb1 hb0 (by linarith)),
    (mul_le_mul ha2 hb2 (by linarith) (by linarith)).trans hhic.ge, ?_⟩
  have h1 := hlof.ge
  have h2 := hhic.le
  rw [← hu] at h1 h2
  have hprod : ha' * hb' ≤ la * lb + δ + ε + δ * ε := by
    have : ha' * hb' ≤ (la + δ) * (lb + ε) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hla1) hε0, mul_nonneg (sub_nonneg.mpr hlb1) hδ0]
  have hab4 : ha' * hb' ≤ 4 := by nlinarith
  have hab1 : la * lb ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hab4 hu0, mul_le_mul_of_nonneg_right hab1 hu0,
    mul_nonneg (mul_nonneg ha0 hb0) hu0]

/-- Division of a nonnegative enclosure of a value `≤ 1` by a positive natural. -/
theorem IsEncl0W.div_nat {a : Encl} {x δ : ℝ} (ha : IsEncl0W a x δ) {n : ℕ} (hn : 0 < n)
    (hx : x ≤ 1) (hδ : δ ≤ 1) {W : ℕ} (hW : 64 ≤ W) :
    IsEncl0W (Encl.div W a (Encl.nat n)) (x / n) ((δ + 8 * (1 / 2 : ℝ) ^ W) / n) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨la, ha', hla, hha, ha0, ha1, ha2, ha3⟩ := ha
  have hn1 : (Encl.nat n).1.toVal = some ((n : ℝ) : EReal) := toVal_ofAzNat_ofNat n
  have hn2 : (Encl.nat n).2.toVal = some ((n : ℝ) : EReal) := toVal_ofAzNat_ofNat n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨lo, hlo, hlof⟩ := divFloor_err hla hn2 hnpos ha0 W
  obtain ⟨hi, hhi, hhic⟩ := divCeiling_err hha hn1 hnpos (by linarith) W
  refine ⟨lo, hi, hlo, hhi, hlof.nonneg,
    hlof.le.trans (div_le_div_of_nonneg_right ha1 hnpos.le),
    (div_le_div_of_nonneg_right ha2 hnpos.le).trans hhic.ge, ?_⟩
  have h1 := hlof.ge
  have h2 := hhic.le
  rw [← hu] at h1 h2
  have hha1 : ha' ≤ 2 := by linarith
  have hla1 : la ≤ 1 := by linarith
  have h3 : hi - lo ≤ (ha' - la) / n + 2 * (ha' / n) * u + 2 * (la / n) * u := by
    have : (ha' - la) / n = ha' / n - la / n := by ring
    linarith
  have h4 : (ha' - la) / n ≤ δ / n := div_le_div_of_nonneg_right (by linarith) hnpos.le
  have h5 : 2 * (ha' / n) * u + 2 * (la / n) * u ≤ 8 * u / n := by
    have : 2 * (ha' / n) * u + 2 * (la / n) * u = (2 * ha' + 2 * la) * u / n := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hu0) hnpos.le
  have e : (δ + 8 * u) / n = δ / n + 8 * u / n := by ring
  rw [e]
  linarith

/-- The difference of an enclosure (`|x| ≤ M`) and a nonnegative one (`y ≤ M`). -/
theorem IsEnclW.sub0 {a b : Encl} {x y δ ε M : ℝ} (ha : IsEnclW a x δ) (hb : IsEncl0W b y ε)
    (hx : |x| ≤ M) (hy : y ≤ M) (hδ : δ ≤ 1) (hε : ε ≤ 1) {W : ℕ} (hW : 64 ≤ W) :
    IsEnclW (Encl.sub W a b) (x - y) (δ + ε + 8 * (M + 1) * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨la, ha', hla, hha, ha1, ha2, ha3⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, hb0, hb1, hb2, hb3⟩ := hb
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hla hhb W
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := subCeiling_abs hha hlb W
  rw [← hu] at hlo2 hhi2
  refine ⟨lo, hi, hlo, hhi, by linarith, by linarith, ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg x).trans hx
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  have h1 : |la - hb'| ≤ 2 * (M + 1) := by rw [abs_le]; constructor <;> linarith
  have h2 : |ha' - lb| ≤ 2 * (M + 1) := by rw [abs_le]; constructor <;> linarith
  have h3 := mul_le_mul_of_nonneg_right h1 hu0
  have h4 := mul_le_mul_of_nonneg_right h2 hu0
  linarith

/-- The sum of an enclosure (`|x| ≤ M`) and a nonnegative one (`y ≤ M`). -/
theorem IsEnclW.add0 {a b : Encl} {x y δ ε M : ℝ} (ha : IsEnclW a x δ) (hb : IsEncl0W b y ε)
    (hx : |x| ≤ M) (hy : y ≤ M) (hδ : δ ≤ 1) (hε : ε ≤ 1) {W : ℕ} (hW : 64 ≤ W) :
    IsEnclW (Encl.add W a b) (x + y) (δ + ε + 8 * (M + 1) * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨la, ha', hla, hha, ha1, ha2, ha3⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, hb0, hb1, hb2, hb3⟩ := hb
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := addFloor_abs hla hlb W
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := addCeiling_abs hha hhb W
  rw [← hu] at hlo2 hhi2
  refine ⟨lo, hi, hlo, hhi, by linarith, by linarith, ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg x).trans hx
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  have h1 : |la + lb| ≤ 2 * (M + 1) := by rw [abs_le]; constructor <;> linarith
  have h2 : |ha' + hb'| ≤ 2 * (M + 1) := by rw [abs_le]; constructor <;> linarith
  have h3 := mul_le_mul_of_nonneg_right h1 hu0
  have h4 := mul_le_mul_of_nonneg_right h2 hu0
  linarith

/-- Widening an enclosure of `x` (`|x| ≤ M`) by a nonnegative enclosure of `y ≤ M` encloses
every `z` with `|z − x| ≤ y`. -/
theorem IsEnclW.widen0 {a e : Encl} {x y z δ ε M : ℝ} (ha : IsEnclW a x δ) (he : IsEncl0W e y ε)
    (hz : |z - x| ≤ y) (hx : |x| ≤ M) (hy : y ≤ M) (hδ : δ ≤ 1) (hε : ε ≤ 1) {W : ℕ}
    (hW : 64 ≤ W) :
    IsEnclW (Encl.widen W a e) z (δ + 2 * y + 2 * ε + 8 * (M + 1) * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨la, ha', hla, hha, ha1, ha2, ha3⟩ := ha
  obtain ⟨le', he', hle, hhe, he0, he1, he2, he3⟩ := he
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hla hhe W
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := addCeiling_abs hha hhe W
  rw [← hu] at hlo2 hhi2
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  refine ⟨lo, hi, hlo, hhi, by linarith, by linarith, ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg x).trans hx
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  have h1 : |la - he'| ≤ 2 * (M + 1) := by rw [abs_le]; constructor <;> linarith
  have h2 : |ha' + he'| ≤ 2 * (M + 1) := by rw [abs_le]; constructor <;> linarith
  have h3 := mul_le_mul_of_nonneg_right h1 hu0
  have h4 := mul_le_mul_of_nonneg_right h2 hu0
  linarith

theorem enclClamp0_spec {a : Encl} {x δ : ℝ} (ha : IsEnclW a x δ) (h0 : 0 ≤ x) :
    IsEncl0W (enclClamp0 a) x δ := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := ha
  obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hlo
  refine ⟨cv, hi, hcv, hhi, hcv0, hcvle.trans (max_le h1 h0), h2, ?_⟩
  rcases le_or_gt 0 lo with hl | hl
  · rw [hcveq hl]; exact h3
  · rw [max_eq_right hl.le] at hcvle
    linarith

theorem enclAbs_spec {a : Encl} {x δ : ℝ} (ha : IsEnclW a x δ) : IsEncl0W (enclAbs a) |x| δ := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := ha
  have hnhi : (-a.2).toVal = some ((-hi : ℝ) : EReal) := by
    rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
  have hnlo : (-a.1).toVal = some ((-lo : ℝ) : EReal) := by
    rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
  obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec (toVal_maxOf hlo hnhi)
  refine ⟨cv, max hi (-lo), hcv, toVal_maxOf hhi hnlo, hcv0, ?_, ?_, ?_⟩
  · refine hcvle.trans (max_le (max_le ?_ ?_) (abs_nonneg x))
    · exact h1.trans (le_abs_self x)
    · linarith [neg_abs_le x]
  · exact abs_le.mpr ⟨by linarith [le_max_right hi (-lo)], by linarith [le_max_left hi (-lo)]⟩
  · rcases le_or_gt 0 (max lo (-hi)) with hm | hm
    · rw [hcveq hm]
      rcases le_total hi (-lo) with hc | hc
      · rw [max_eq_right hc]; linarith [le_max_right lo (-hi)]
      · rw [max_eq_left hc]; linarith [le_max_left lo (-hi)]
    · have hlo' : lo < 0 := lt_of_le_of_lt (le_max_left _ _) hm
      have hhi' : 0 < hi := by linarith [le_max_right lo (-hi)]
      rw [max_eq_right hm.le] at hcvle
      rcases le_total hi (-lo) with hc | hc
      · rw [max_eq_right hc]; linarith
      · rw [max_eq_left hc]; linarith

theorem toVal_nat2_fst : (Encl.nat 2).1.toVal = some ((2 : ℝ) : EReal) := by
  have h := toVal_ofAzNat_ofNat 2
  push_cast at h
  exact h

theorem toVal_nat2_snd : (Encl.nat 2).2.toVal = some ((2 : ℝ) : EReal) := toVal_nat2_fst

/-- The double-angle step on a nonnegative enclosure of a value `c ≤ 1` (a cosine). -/
theorem cosDouble_spec {a : Encl} {c δ : ℝ} (ha : IsEncl0W a c δ) (hc : c ≤ 1) (hδ : δ ≤ 1 / 8)
    {W : ℕ} (hW : 64 ≤ W) :
    IsEnclW (cosDouble W a) (2 * c ^ 2 - 1) (6 * δ + 80 * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hW
  have hc0 : 0 ≤ c := by obtain ⟨lo, hi, -, -, h0, h1, -, -⟩ := ha; linarith
  have hδ0 : 0 ≤ δ := by obtain ⟨lo, hi, -, -, -, h1, h2, h3⟩ := ha; linarith
  have hδδ : δ * δ ≤ δ := by nlinarith
  have hsq := ha.mul ha hc hc (by linarith) (by linarith) hW
  rw [← hu] at hsq
  obtain ⟨ls, hs, hls, hhs, hs0, hs1, hs2, hs3⟩ := hsq
  have hcc : c * c ≤ 1 := by nlinarith
  obtain ⟨lo, hlo, hlof⟩ := mulFloor_err toVal_nat2_fst hls W (by linarith)
  obtain ⟨hi, hhi, hhic⟩ := mulCeiling_err toVal_nat2_snd hhs W (by linarith)
  have hdbl : IsEnclW (Encl.mul W (Encl.nat 2) (Encl.mul W a a)) (2 * (c * c))
      (6 * δ + 48 * u) := by
    refine ⟨lo, hi, hlo, hhi, hlof.le.trans (by linarith),
      (by linarith : 2 * (c * c) ≤ 2 * hs).trans hhic.ge, ?_⟩
    have h1 := hlof.ge
    have h2 := hhic.le
    rw [← hu] at h1 h2
    have hhs1 : hs ≤ 2 := by linarith
    have hls1 : ls ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hhs1 hu0, mul_le_mul_of_nonneg_right hls1 hu0]
  have hone : IsEncl0W (Encl.exact one) 1 0 := isEncl0W_exact toVal_one' zero_le_one
  have hres := hdbl.sub0 hone (M := 2)
    (by rw [abs_of_nonneg (mul_nonneg (by norm_num) (mul_self_nonneg c))]; linarith)
    (by norm_num) (by linarith) (by norm_num) hW
  rw [← hu] at hres
  have e : 2 * (c * c) - 1 = 2 * c ^ 2 - 1 := by ring
  rw [e] at hres
  exact hres.mono (by linarith)

/-! ### The cosine series -/

/-- The terms `m^{2k}/(2k)!` of the cosine series. -/
noncomputable def cosTerm (m : ℝ) (k : ℕ) : ℝ := m ^ (2 * k) / ((2 * k).factorial : ℝ)

theorem cosTerm_zero (m : ℝ) : cosTerm m 0 = 1 := by simp [cosTerm]

theorem cosTerm_succ (m : ℝ) (k : ℕ) :
    cosTerm m (k + 1) = cosTerm m k * (m * m) / ((2 * k + 1) * (2 * k + 2) : ℕ) := by
  unfold cosTerm
  have h : (2 * (k + 1)).factorial = (2 * k).factorial * ((2 * k + 1) * (2 * k + 2)) := by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [h]
  push_cast
  have h1 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * k + 1 : ℝ) * (2 * k + 2)) ≠ 0 := by positivity
  field_simp
  ring

theorem cosTerm_nonneg (m : ℝ) (k : ℕ) : 0 ≤ cosTerm m k := by
  unfold cosTerm
  have : 0 ≤ m ^ (2 * k) := by rw [pow_mul]; positivity
  positivity

theorem cosTerm_antitone {m : ℝ} (hm : |m| ≤ 1) : Antitone (cosTerm m) := by
  refine antitone_nat_of_succ_le fun k => ?_
  rw [cosTerm_succ]
  have hmm : m * m ≤ 1 := by
    have := abs_le.mp hm
    nlinarith [abs_nonneg m, sq_abs m]
  have hn : (1 : ℝ) ≤ ((2 * k + 1) * (2 * k + 2) : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hk := cosTerm_nonneg m k
  calc cosTerm m k * (m * m) / ((2 * k + 1) * (2 * k + 2) : ℕ)
      ≤ cosTerm m k * 1 / 1 :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hmm hk) one_pos hn
    _ = cosTerm m k := by ring

theorem cosTerm_le_one {m : ℝ} (hm : |m| ≤ 1) (k : ℕ) : cosTerm m k ≤ 1 := by
  have := cosTerm_antitone hm (Nat.zero_le k)
  rwa [cosTerm_zero] at this

/-- `2^(n−1) ≤ n!`. -/
theorem two_pow_pred_le_factorial (n : ℕ) : 2 ^ (n - 1) ≤ n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.factorial_succ, Nat.add_sub_cancel]
      calc 2 ^ n = 2 * 2 ^ (n - 1) := by
            rw [← pow_succ']; congr 1; omega
        _ ≤ (n + 1) * n.factorial := Nat.mul_le_mul (by omega) ih

theorem cosTerm_le_half_pow {m : ℝ} (hm : |m| ≤ 1) (k : ℕ) :
    cosTerm m k ≤ (1 / 2 : ℝ) ^ (2 * k - 1) := by
  unfold cosTerm
  have hmk : m ^ (2 * k) ≤ 1 := by
    rw [pow_mul, ← sq_abs]
    exact pow_le_one₀ (by positivity) (by nlinarith [abs_nonneg m])
  have hf : (2 : ℝ) ^ (2 * k - 1) ≤ ((2 * k).factorial : ℝ) := by
    exact_mod_cast two_pow_pred_le_factorial (2 * k)
  have hf0 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
  have h20 : (0 : ℝ) < (2 : ℝ) ^ (2 * k - 1) := by positivity
  calc m ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ 1 / ((2 * k).factorial : ℝ) :=
        div_le_div_of_nonneg_right hmk hf0.le
    _ ≤ 1 / (2 : ℝ) ^ (2 * k - 1) := one_div_le_one_div_of_le h20 hf
    _ = (1 / 2 : ℝ) ^ (2 * k - 1) := by rw [one_div_pow]

/-- The alternating-series tail bound: `|cos m − ∑_{k<n} (−1)^k m^{2k}/(2k)!| ≤ m^{2n}/(2n)!`
for `|m| ≤ 1`. -/
theorem abs_cos_sub_sum_le {m : ℝ} (hm : |m| ≤ 1) (n : ℕ) :
    |Real.cos m - ∑ k ∈ range n, (-1) ^ k * cosTerm m k| ≤ cosTerm m n := by
  have hsum := (Real.hasSum_cos m).tendsto_sum_nat
  have hsum' : Filter.Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * cosTerm m i) Filter.atTop
      (nhds (Real.cos m)) := by
    refine hsum.congr fun n => sum_congr rfl fun i _ => ?_
    unfold cosTerm; ring
  have hanti := cosTerm_antitone hm
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hn : n = 2 * k := by omega
    have h1 := hanti.alternating_series_le_tendsto hsum' k
    have h2 := hanti.tendsto_le_alternating_series hsum' k
    rw [sum_range_succ] at h2
    rw [hn, abs_le]
    constructor
    · have := cosTerm_nonneg m (2 * k); linarith
    · have : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; simp
      rw [this] at h2; linarith
  · have hn : n = 2 * k + 1 := by omega
    have h1 := hanti.alternating_series_le_tendsto hsum' (k + 1)
    have h2 := hanti.tendsto_le_alternating_series hsum' k
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ] at h1
    rw [hn, abs_le]
    constructor
    · have : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; simp
      rw [this] at h1; linarith
    · have := cosTerm_nonneg m (2 * k + 1); linarith

/-- The invariant of `cosSeriesLoop`: `j` more steps from index `i` give the partial sum through
index `i + j` and the term `cosTerm m (i + j)`, the widths growing by `112 · 2^(−W)` per step. -/
theorem cosSeriesLoop_spec {m : ℝ} (hm : |m| ≤ 1) {W : ℕ} (hW : 64 ≤ W) {u : Encl}
    (hu : IsEncl0W u (m * m) (16 * (1 / 2 : ℝ) ^ W)) (j : ℕ) :
    ∀ (i : ℕ) (pos : Bool) (S t : Encl), i + j ≤ W → (pos = true ↔ Even i) →
      IsEncl0W t (cosTerm m i) (80 * (1 / 2 : ℝ) ^ W) →
      IsEnclW S (∑ k ∈ range (i + 1), (-1) ^ k * cosTerm m k)
        ((i : ℝ) * (112 * (1 / 2 : ℝ) ^ W)) →
      IsEnclW (cosSeriesLoop W u j i pos S t).1
          (∑ k ∈ range (i + j + 1), (-1) ^ k * cosTerm m k)
          (((i + j : ℕ) : ℝ) * (112 * (1 / 2 : ℝ) ^ W)) ∧
        IsEncl0W (cosSeriesLoop W u j i pos S t).2 (cosTerm m (i + j))
          (80 * (1 / 2 : ℝ) ^ W) := by
  induction j with
  | zero =>
    intro i pos S t _ _ ht hS
    simp only [cosSeriesLoop, Nat.add_zero]
    exact ⟨hS, ht⟩
  | succ j ih =>
    intro i pos S t hij hpos ht hS
    have hWu := nat_mul_half_pow_le hW
    set uu := (1 / 2 : ℝ) ^ W with huu
    have hu0 : 0 ≤ uu := by positivity
    have hus : uu ≤ 1 / 10 ^ 18 := half_pow_small hW
    have hmm : m * m ≤ 1 := by
      have := abs_le.mp hm
      nlinarith [abs_nonneg m, sq_abs m]
    have hti := cosTerm_le_one hm i
    have hti0 := cosTerm_nonneg m i
    have hti1 := cosTerm_le_one hm (i + 1)
    -- the next term
    have hprod := ht.mul hu hti hmm (by linarith) (by linarith) hW
    rw [← huu] at hprod
    have hn : 0 < (2 * i + 1) * (2 * i + 2) := by positivity
    have hterm := hprod.div_nat hn (by nlinarith) (by nlinarith) hW
    rw [← huu] at hterm
    set t' := Encl.div W (Encl.mul W t u) (Encl.nat ((2 * i + 1) * (2 * i + 2))) with ht'
    have hterm' : IsEncl0W t' (cosTerm m (i + 1)) (80 * uu) := by
      rw [cosTerm_succ]
      refine hterm.mono ?_
      have hn2 : (2 : ℝ) ≤ ((2 * i + 1) * (2 * i + 2) : ℕ) := by
        exact_mod_cast (by nlinarith : 2 ≤ (2 * i + 1) * (2 * i + 2))
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right hn2 hu0, mul_le_mul_of_nonneg_left hus hu0]
    -- the partial sum
    have hSabs : |∑ k ∈ range (i + 1), (-1) ^ k * cosTerm m k| ≤ 2 := by
      have h := abs_cos_sub_sum_le hm (i + 1)
      have hc := Real.abs_cos_le_one m
      calc |∑ k ∈ range (i + 1), (-1) ^ k * cosTerm m k|
          = |Real.cos m - (Real.cos m - ∑ k ∈ range (i + 1), (-1) ^ k * cosTerm m k)| := by
            congr 1; ring
        _ ≤ |Real.cos m| + |Real.cos m - ∑ k ∈ range (i + 1), (-1) ^ k * cosTerm m k| :=
            abs_sub _ _
        _ ≤ 2 := by linarith
    have hiW : (i : ℝ) ≤ W := by exact_mod_cast (by omega : i ≤ W)
    have hSw : (i : ℝ) * (112 * uu) ≤ 1 := by
      have : (i : ℝ) * uu ≤ (W : ℝ) * uu := mul_le_mul_of_nonneg_right hiW hu0
      nlinarith
    have hw' : (i : ℝ) * (112 * uu) + 80 * uu + 8 * (2 + 1) * uu
        ≤ ((i + 1 : ℕ) : ℝ) * (112 * uu) := by
      push_cast; nlinarith
    have hS' : IsEnclW (if pos then Encl.sub W S t' else Encl.add W S t')
        (∑ k ∈ range (i + 1 + 1), (-1) ^ k * cosTerm m k) (((i + 1 : ℕ) : ℝ) * (112 * uu)) := by
      rw [sum_range_succ]
      cases hp : pos with
      | true =>
        have hev : Even i := hpos.mp hp
        rw [pow_succ, hev.neg_one_pow, one_mul, neg_one_mul, ← sub_eq_add_neg]
        simp only [↓reduceIte]
        exact (hS.sub0 hterm' hSabs (hti1.trans (by norm_num)) hSw (by linarith) hW).mono hw'
      | false =>
        have hodd : Odd i :=
          Nat.not_even_iff_odd.mp fun h => absurd (hp.symm.trans (hpos.mpr h)) (by decide)
        have hev : Even (i + 1) := hodd.add_one
        rw [hev.neg_one_pow, one_mul]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact (hS.add0 hterm' hSabs (hti1.trans (by norm_num)) hSw (by linarith) hW).mono hw'
    have hstep : cosSeriesLoop W u (j + 1) i pos S t
        = cosSeriesLoop W u j (i + 1) (!pos) (if pos then Encl.sub W S t' else Encl.add W S t')
          t' := rfl
    rw [hstep]
    have hpos' : (!pos) = true ↔ Even (i + 1) := by
      rw [Nat.even_add_one, ← hpos]
      cases pos <;> simp
    have h := ih (i + 1) (!pos) _ t' (by omega) hpos' hterm' hS'
    have e : i + 1 + j = i + (j + 1) := by omega
    rw [e] at h
    exact h

/-- The width of `cosSeries` at precision `W`. -/
noncomputable def cosSeriesEps (W : ℕ) : ℝ :=
  (W : ℝ) * (112 * (1 / 2 : ℝ) ^ W) + 2 * (1 / 2 : ℝ) ^ (W / 2) + 184 * (1 / 2 : ℝ) ^ W

theorem cosSeriesEps_le {W : ℕ} (hW : 64 ≤ W) : cosSeriesEps W ≤ 1 / 10 ^ 9 := by
  unfold cosSeriesEps
  have h1 := nat_mul_half_pow_le hW
  have h2 : (1 / 2 : ℝ) ^ (W / 2) ≤ (1 / 2 : ℝ) ^ 32 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h3 := half_pow_small hW
  have h4 : (1 / 2 : ℝ) ^ 32 ≤ 1 / 10 ^ 9 / 3 := by norm_num
  linarith

/-- `cosSeries m W` encloses `cos m` for a float `m` with `|m| ≤ 1`. -/
theorem cosSeries_spec {m : AzFloat} {mv : ℝ} (hm : m.toVal = some (mv : EReal)) (hm1 : |mv| ≤ 1)
    {W : ℕ} (hW : 64 ≤ W) : IsEnclW (cosSeries m W) (Real.cos mv) (cosSeriesEps W) := by
  have : NeZero W := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hW
  have hWu := nat_mul_half_pow_le hW
  have habs : m.abs.toVal = some ((|mv| : ℝ) : EReal) := by
    rw [toVal_abs, hm, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hsq : IsEncl0W (Encl.mul W (Encl.exact m.abs) (Encl.exact m.abs)) (mv * mv) (16 * u) := by
    have h := (isEncl0W_exact habs (abs_nonneg mv)).mul (isEncl0W_exact habs (abs_nonneg mv))
      hm1 hm1 zero_le_one zero_le_one hW
    rw [abs_mul_abs_self] at h
    exact h.mono (by rw [← hu]; linarith)
  set N := cosTerms W with hN
  have hNW : N ≤ W := by rw [hN]; unfold cosTerms; omega
  have ht0 : IsEncl0W (Encl.exact one) (cosTerm mv 0) (80 * u) := by
    rw [cosTerm_zero]
    exact (isEncl0W_exact toVal_one' zero_le_one).mono (by positivity)
  have hS0 : IsEnclW (Encl.exact one) (∑ k ∈ range (0 + 1), (-1) ^ k * cosTerm mv k)
      (((0 : ℕ) : ℝ) * (112 * u)) := by
    rw [zero_add, sum_range_one, pow_zero, one_mul, cosTerm_zero, Nat.cast_zero, zero_mul]
    exact (isEncl0W_exact toVal_one' zero_le_one).toW
  obtain ⟨hS, ht⟩ := cosSeriesLoop_spec hm1 hW hsq N 0 true (Encl.exact one) (Encl.exact one)
    (by omega) (by simp) ht0 hS0
  rw [zero_add] at hS ht
  have htail : |Real.cos mv - ∑ k ∈ range (N + 1), (-1) ^ k * cosTerm mv k| ≤ cosTerm mv N :=
    (abs_cos_sub_sum_le hm1 (N + 1)).trans (cosTerm_antitone hm1 (Nat.le_succ N))
  have hSabs : |∑ k ∈ range (N + 1), (-1) ^ k * cosTerm mv k| ≤ 2 := by
    have hc := Real.abs_cos_le_one mv
    have ht1 := cosTerm_le_one hm1 N
    calc |∑ k ∈ range (N + 1), (-1) ^ k * cosTerm mv k|
        = |Real.cos mv - (Real.cos mv - ∑ k ∈ range (N + 1), (-1) ^ k * cosTerm mv k)| := by
          congr 1; ring
      _ ≤ |Real.cos mv| + |Real.cos mv - ∑ k ∈ range (N + 1), (-1) ^ k * cosTerm mv k| :=
          abs_sub _ _
      _ ≤ 2 := by linarith
  have hNW' : (N : ℝ) ≤ W := by exact_mod_cast hNW
  have hNu : (N : ℝ) * (112 * u) ≤ 1 := by
    have : (N : ℝ) * u ≤ (W : ℝ) * u := mul_le_mul_of_nonneg_right hNW' hu0
    nlinarith
  have hres := hS.widen0 ht htail hSabs ((cosTerm_le_one hm1 N).trans (by norm_num)) hNu
    (by linarith) hW
  rw [← hu] at hres
  have hterm := cosTerm_le_half_pow hm1 N
  have hpow : (1 / 2 : ℝ) ^ (2 * N - 1) ≤ (1 / 2 : ℝ) ^ (W / 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by rw [hN]; unfold cosTerms; omega)
  dsimp only [cosSeries]
  refine hres.mono ?_
  unfold cosSeriesEps
  rw [← hu]
  linarith [mul_le_mul_of_nonneg_right hNW' hu0]

/-! ### The bracket -/

/-- `2^ex · 2^(−cosWork ex w) ≤ 2^(−(w+12))`. -/
theorem two_zpow_mul_half_pow_cosWork (ex : AzInt) (w : ℕ) :
    (2 : ℝ) ^ ex.toInt * (1 / 2 : ℝ) ^ cosWork ex w ≤ (1 / 2 : ℝ) ^ (w + 12) := by
  have htoInt : ex.toInt = if ex.sign then (ex.abs.toNat : ℤ) else -(ex.abs.toNat : ℤ) := rfl
  unfold cosWork
  rw [htoInt]
  split_ifs with hs
  · rw [zpow_natCast, pow_add, mul_comm, mul_assoc, ← mul_pow]
    norm_num
  · rw [add_zero]
    have h1 : (2 : ℝ) ^ (-(ex.abs.toNat : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    exact mul_le_of_le_one_left (by positivity) h1

/-- The width of `cosBracket` at working precision `W`. -/
noncomputable def cosEpsW (ex : AzInt) (W : ℕ) : ℝ :=
  216 * (cosSeriesEps W + 8 * (2 : ℝ) ^ ex.toInt * (1 / 2 : ℝ) ^ W + 24 * (1 / 2 : ℝ) ^ W)
    + 3440 * (1 / 2 : ℝ) ^ W

/-- The width of `cosBracket x ex w`. -/
noncomputable def cosEps (ex : AzInt) (w : ℕ) : ℝ := cosEpsW ex (cosWork ex w)

/-- **`cosBracket` encloses `cos x`** for a float `x` with `|x| < 2^ex`, at Ziv level
`w ≥ 64`, with width at most `cosEps ex w`. -/
theorem cosBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (cosBracket x ex w).1.toVal = some (lo : EReal) ∧
      (cosBracket x ex w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.cos xv ∧ Real.cos xv ≤ hi ∧ hi - lo ≤ cosEps ex w := by
  have hW64 : 64 ≤ cosWork ex w := by unfold cosWork; omega
  have hexu := two_zpow_mul_half_pow_cosWork ex w
  simp only [cosBracket]
  set W := cosWork ex w with hWdef
  have : NeZero W := ⟨by omega⟩
  have : NeZero (64 : ℕ) := ⟨by norm_num⟩
  set P := piBracket W with hP
  set y := P.1 <<< AzInt.ofInt 1 with hy
  set r := remExact x.abs y with hr
  set E := (mulPrecRound x.abs (subPrecRound P.2 P.1 64 .Ceiling).1 64 .Ceiling).1 with hE
  set m := r <<< AzInt.ofInt (-3) with hm
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hW64
  have h12 : (1 / 2 : ℝ) ^ (w + 12) ≤ 1 / 4096 := by
    calc (1 / 2 : ℝ) ^ (w + 12) ≤ (1 / 2 : ℝ) ^ 12 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4096 := by norm_num
  have hex' : |xv| ≤ 2 ^ ex.toInt := hex.le
  have hx0 := abs_nonneg xv
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  -- π
  obtain ⟨lv, hv, hlv, hhv, hlv0, hlvπ, hπhv, hwid⟩ := piBracket_spec_width hW64
  rw [← hu] at hwid
  have hlv1 : 1 ≤ lv := by linarith
  have hlv' : P.1.toVal = some (lv : EReal) := hlv
  have hhv' : P.2.toVal = some (hv : EReal) := hhv
  have hyv : y.toVal = some ((2 * lv : ℝ) : EReal) := toVal_shiftLeft_one hlv'
  have h2lv : (0 : ℝ) < 2 * lv := by linarith
  -- the remainder
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hq0 : (0 : ℝ) ≤ |xv| / (2 * lv) := by positivity
  set k : ℤ := ⌊|xv| / (2 * lv)⌋ with hk
  have hrv : r.toVal = some ((|xv| - 2 * lv * k : ℝ) : EReal) := by
    rw [hr, toVal_remExact, habs, hyv, Option.bind_some, Option.bind_some,
      Spec.rem_coe_coe _ _ h2lv.ne', toInt_round_down, ite_eq_left hq0]
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast Int.floor_nonneg.mpr hq0
  have hkle : (k : ℝ) ≤ |xv| / (2 * lv) := Int.floor_le _
  have hkgt : |xv| / (2 * lv) < k + 1 := Int.lt_floor_add_one _
  set rv := |xv| - 2 * lv * k with hrvdef
  have hrv0 : 0 ≤ rv := by
    have := (le_div_iff₀ h2lv).mp hkle; linarith
  have hrvlt : rv < 2 * lv := by
    have := (div_lt_iff₀ h2lv).mp hkgt; linarith
  -- the error of the reduction
  obtain ⟨d, hd, hdc⟩ := subCeiling_err hhv' hlv' 64 (by linarith)
  have hd0 : 0 ≤ d := by linarith [hdc.ge]
  obtain ⟨Ev, hEv, hEvc⟩ := mulCeiling_err habs hd 64 (mul_nonneg hx0 hd0)
  have hEv' : E.toVal = some (Ev : EReal) := hEv
  have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
  have hd1 : d ≤ 2 * (hv - lv) := by
    have := hdc.le
    nlinarith [mul_le_mul_of_nonneg_left h64 (by linarith : 0 ≤ hv - lv)]
  have hd16 : d ≤ 16 * u := by linarith
  have hEv1 : Ev ≤ 2 * (|xv| * d) := by
    have := hEvc.le
    nlinarith [mul_le_mul_of_nonneg_left h64 (mul_nonneg hx0 hd0)]
  have hEv0 : 0 ≤ Ev := le_trans (mul_nonneg hx0 hd0) hEvc.ge
  have hEvle : Ev ≤ 32 * (2 : ℝ) ^ ex.toInt * u := by
    have h1 : |xv| * d ≤ |xv| * (16 * u) := mul_le_mul_of_nonneg_left hd16 hx0
    have h2 : |xv| * u ≤ (2 : ℝ) ^ ex.toInt * u := mul_le_mul_of_nonneg_right hex' hu0
    nlinarith
  have hEvs : Ev ≤ 1 / 128 := by linarith
  have hk2 : 2 * (k : ℝ) ≤ |xv| := by
    have := (le_div_iff₀ h2lv).mp hkle
    nlinarith [mul_le_mul_of_nonneg_left hlv1 hk0]
  have hkπ0 : 0 ≤ 2 * k * (Real.pi - lv) := mul_nonneg (by linarith) (by linarith)
  have hkπ : 2 * k * (Real.pi - lv) ≤ Ev :=
    calc 2 * k * (Real.pi - lv) ≤ |xv| * (Real.pi - lv) :=
          mul_le_mul_of_nonneg_right hk2 (by linarith)
      _ ≤ |xv| * (hv - lv) := mul_le_mul_of_nonneg_left (by linarith) hx0
      _ ≤ |xv| * d := mul_le_mul_of_nonneg_left hdc.ge hx0
      _ ≤ Ev := hEvc.ge
  -- the true reduction
  set rt := rv - 2 * k * (Real.pi - lv) with hrt
  have hcos : Real.cos xv = Real.cos rt := by
    rw [← Real.cos_abs (x := xv), show |xv| = rt + k * (2 * Real.pi) by rw [hrt, hrvdef]; ring,
      Real.cos_add_int_mul_two_pi]
  -- the series at `rv/8`
  have hmv : m.toVal = some ((rv / 8 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hrv (AzInt.ofInt (-3))
    rw [AzInt.toInt_ofInt, show (2 : ℝ) ^ (-3 : ℤ) = 1 / 8 by norm_num, mul_one_div] at h
    exact h
  have hm1 : |rv / 8| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hrv0 (by norm_num)), div_le_one (by norm_num)]
    linarith
  have hser := cosSeries_spec hmv hm1 hW64
  have hE8 : (E <<< AzInt.ofInt (-3)).toVal = some ((Ev / 8 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hEv' (AzInt.ofInt (-3))
    rw [AzInt.toInt_ofInt, show (2 : ℝ) ^ (-3 : ℤ) = 1 / 8 by norm_num, mul_one_div] at h
    exact h
  have hz : |Real.cos (rt / 8) - Real.cos (rv / 8)| ≤ Ev / 8 := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [abs_le]
    constructor <;> linarith
  have hsE := cosSeriesEps_le hW64
  have hC := hser.widen0 (M := 2) (isEncl0W_exact hE8 (div_nonneg hEv0 (by norm_num))) hz
    ((Real.abs_cos_le_one _).trans (by norm_num)) (by linarith) (by linarith) (by norm_num) hW64
  rw [← hu] at hC
  set δ₁ := cosSeriesEps W + Ev / 4 + 24 * u with hδ₁
  have hC' : IsEnclW (Encl.widen W (cosSeries m W) (Encl.exact (E <<< AzInt.ofInt (-3))))
      (Real.cos (rt / 8)) δ₁ := hC.mono (by rw [hδ₁]; linarith)
  have hδ₁s : δ₁ ≤ 1 / 8 := by rw [hδ₁]; linarith
  -- the doublings
  have hcos8 : 0 ≤ Real.cos (rt / 8) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hC2 := cosDouble_spec (enclClamp0_spec hC' hcos8) (Real.cos_le_one _) hδ₁s hW64
  rw [← hu, ← Real.cos_two_mul, show 2 * (rt / 8) = rt / 4 by ring] at hC2
  have hδ₂s : 6 * δ₁ + 80 * u ≤ 1 / 8 := by linarith
  have hcos4 : 0 ≤ Real.cos (rt / 4) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hC4 := cosDouble_spec (enclClamp0_spec hC2 hcos4) (Real.cos_le_one _) hδ₂s hW64
  rw [← hu, ← Real.cos_two_mul, show 2 * (rt / 4) = rt / 2 by ring] at hC4
  have hδ₃s : 6 * (6 * δ₁ + 80 * u) + 80 * u ≤ 1 / 8 := by linarith
  have hfin := cosDouble_spec (enclAbs_spec hC4) (Real.abs_cos_le_one _) hδ₃s hW64
  rw [← hu, sq_abs, ← Real.cos_two_mul, show 2 * (rt / 2) = rt by ring] at hfin
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := hfin
  refine ⟨lo, hi, hlo, hhi, by rw [hcos]; exact h1, by rw [hcos]; exact h2, h3.trans ?_⟩
  show _ ≤ cosEpsW ex W
  unfold cosEpsW
  rw [← hu, hδ₁]
  linarith

/-- `cosEpsW ex W → 0` as `W → ∞`. -/
theorem tendsto_cosEpsW (ex : AzInt) :
    Filter.Tendsto (cosEpsW ex) Filter.atTop (nhds 0) := by
  have h1 := tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hdiv : Filter.Tendsto (fun W : ℕ => W / 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun a ha => by omega⟩
  have h3 := h2.comp hdiv
  have h := ((h1.const_mul (216 * 112)).add (h3.const_mul (216 * 2))).add
    (h2.const_mul (216 * 184 + 216 * 8 * (2 : ℝ) ^ ex.toInt + 216 * 24 + 3440))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun W => ?_
  simp only [Function.comp, cosEpsW, cosSeriesEps]
  ring

/-- `cosEps ex w → 0` as `w → ∞`. -/
theorem tendsto_cosEps (ex : AzInt) : Filter.Tendsto (cosEps ex) Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (cosWork ex) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by unfold cosWork; omega⟩
  exact (tendsto_cosEpsW ex).comp hc

/-- `cosApprox` as a pair of `Roundable`s bracketing `cos x`. -/
theorem cosApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (cosApprox x ex w).1 lv ∧ Rounds (cosApprox x ex w).2 hv ∧
      lv ≤ Real.cos xv ∧ Real.cos xv ≤ hv ∧ hv - lv ≤ cosEps ex w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := cosBracket_spec hx hex hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [cosApprox]
  exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩

/-- `cos x` is irrational for a nonzero finite float `x`. -/
theorem irrational_cos_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.cos xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [hq, Rat.cast_zero]
  rw [hq]
  exact irrational_cos_rat hq0

/-- The Ziv certificate for `cos x`, `x` a nonzero finite float. -/
theorem cosApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cosApprox x ex (w₀ * 2 ^ f)).1 (cosApprox x ex (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (cosApprox x ex) (irrational_cos_of_toVal hx hx0)
    (cosEps ex) (tendsto_cosEps ex) 64 (fun _ hw => cosApprox_spec hx hex hw) w₀ hw₀

end Azurite.AzFloat
