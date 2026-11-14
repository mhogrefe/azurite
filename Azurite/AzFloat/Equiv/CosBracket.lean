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
import Azurite.AzFloat.Equiv.NegRound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Equivalence: the tools of the brackets of `cos x` and `sin x`

* `IsEnclW`/`IsEncl0W`: enclosures with a width bound, and the width-tracking versions of the
  interval operations (`IsEncl0W.mul`, `IsEncl0W.div_nat`, `IsEnclW.sub0`, `IsEnclW.add0`,
  `IsEnclW.widen0`, `enclClamp0_spec`, `enclAbs_spec`, `cosDouble_spec`).
* `cosTerm`: the terms `m^{2k}/(2k)!` of the cosine series (nonnegative, antitone for
  `|m| ≤ 1`).
* `two_zpow_mul_half_pow_cosWork`; `irrational_cos_of_toVal`; `cosTiny?_eq`.

The bracket itself (`cosBracket_spec`) is in `Equiv/SinCosBracket.lean`.
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

/-! ### The reduction precision, irrationality, tiny arguments -/

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

/-- `cosTiny?` answers only for a tiny exponent. -/
theorem cosTiny?_cond {e : AzInt} {p : ℕ} {mode : RoundingMode} {r : AzFloat × Ordering}
    (h : cosTiny? e p mode = some r) : e.sign = false ∧ p + zivGuardBits + 8 ≤ e.abs.toNat := by
  unfold cosTiny? at h
  dsimp only at h
  split_ifs at h with hc
  exact hc

/-- The tiny-argument path answers with the rounding of `cos v`, for any `|v| < 2^e` with an
irrational cosine. -/
theorem cosTiny?_eq {e : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {v : ℝ} (hv : |v| < (2 : ℝ) ^ e.toInt)
    (hirr : Irrational (Real.cos v)) (h : cosTiny? e p mode = some r) :
    r = roundVal p mode (some ((Real.cos v : ℝ) : EReal)) := by
  unfold cosTiny? at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  set t := (2 : ℝ) ^ e.toInt with ht
  have ht0 : 0 < t := by positivity
  have hd : ((one <<< e) <<< e).toVal = some ((1 * t * t : ℝ) : EReal) :=
    toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal toVal_one' e) e
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs toVal_neg_one hd (p + zivGuardBits + 8)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := v)
  have hsq : v ^ 2 ≤ t * t := by
    rw [← sq_abs, sq]
    exact mul_le_mul hv.le hv.le (abs_nonneg v) ht0.le
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe toVal_neg_one)
  rw [fval_of_toVal_coe toVal_neg_one] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hr := roundingPossible_eq' p (-mode) (v := -Real.cos v) hR1 hR2
    (by linarith [Real.cos_le_one v]) (by nlinarith [mul_pos ht0 ht0])
    (Or.inr (not_mem_floatSet_of_irrational p hirr.neg)) hr'
  rw [hr]
  have hneg := roundVal_neg p mode (-Real.cos v)
  rw [neg_neg] at hneg
  exact hneg.symm

end Azurite.AzFloat
