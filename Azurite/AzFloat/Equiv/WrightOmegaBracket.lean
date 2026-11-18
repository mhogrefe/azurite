/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.WrightOmegaBracket
import Azurite.Transcendental.WrightOmega
import Azurite.AzFloat.Equiv.LambertWBracket
import Azurite.AzFloat.Equiv.LnEncl
import Azurite.AzFloat.Equiv.ExpRat
import Azurite.AzFloat.Equiv.NegRound
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: the brackets of the real Wright `ω` function

* `expAt_encl`, `expRatAt_encl`: the enclosure functions of `eˣ`.
* `omegaEncl_spec`: the enclosure around **any** positive candidate contains `ω(x)`.
* `wrightBracket_spec`: the bracket encloses `ω(x)` with a width bound `omegaEps` that tends to
  zero (`tendsto_omegaEps`) — `ω 2^(−w)` from the acceptance test, or the bound of the
  `W₀` bracket at `eˣ`.
* `OmegaTarget`, `omegaSideCert`, `omegaZivCert`: the certificates of the driver for a rational
  `x ≠ 1` (`ω(x)` is irrational, and no grid point `m` has `m eᵐ = eˣ`).
* `wrightOmegaHuge?_eq`: the large-argument path.
-/

open Real Azurite.DLMF Azurite.LambertW Azurite.WrightOmega

namespace Azurite.AzFloat

/-! ### The target -/

theorem expAt_encl {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    XEncl (expAt x) (Real.exp xv) := fun P hP => by
  have : NeZero P := ⟨by omega⟩
  have hf : expPrecRound x P .Floor = roundVal P .Floor (some ((Real.exp xv : ℝ) : EReal)) := by
    rw [expPrecRound_eq_liftVal, liftVal, hx, Option.bind_some, Spec.exp_coe]
  have hc : expPrecRound x P .Ceiling
      = roundVal P .Ceiling (some ((Real.exp xv : ℝ) : EReal)) := by
    rw [expPrecRound_eq_liftVal, liftVal, hx, Option.bind_some, Spec.exp_coe]
  obtain ⟨r₁, h₁, h₁1, h₁2⟩ := roundVal_floor_abs P (Real.exp xv)
  obtain ⟨r₂, h₂, h₂1, h₂2⟩ := roundVal_ceiling_abs P (Real.exp xv)
  refine ⟨r₁, r₂, ?_, ?_, h₁1, h₂1, by linarith⟩
  · show (expPrecRound x P .Floor).1.toVal = _
    rw [hf]; exact h₁
  · show (expPrecRound x P .Ceiling).1.toVal = _
    rw [hc]; exact h₂

theorem expRatAt_encl (q : AzRat) :
    XEncl (expRatAt q) (Real.exp ((AzRat.toRat q : ℚ) : ℝ)) := fun P hP => by
  have : NeZero P := ⟨by omega⟩
  obtain ⟨r₁, h₁, h₁1, h₁2⟩ := roundVal_floor_abs P (Real.exp ((AzRat.toRat q : ℚ) : ℝ))
  obtain ⟨r₂, h₂, h₂1, h₂2⟩ := roundVal_ceiling_abs P (Real.exp ((AzRat.toRat q : ℚ) : ℝ))
  refine ⟨r₁, r₂, ?_, ?_, h₁1, h₂1, by linarith⟩
  · show (expRatPrecRound q P .Floor).1.toVal = _
    rw [expRatPrecRound_eq, Spec.exp_coe]; exact h₁
  · show (expRatPrecRound q P .Ceiling).1.toVal = _
    rw [expRatPrecRound_eq, Spec.exp_coe]; exact h₂

theorem isOne_iff {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    isOne x = true ↔ xv = 1 := by
  unfold isOne
  rw [Bool.and_eq_true, le_eq_true_iff hx toVal_one', le_eq_true_iff toVal_one' hx]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem XEncl.isEncl {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) {P : ℕ}
    (hP : 64 ≤ P) : IsEncl (xAt P) xv := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, -⟩ := hX P hP
  exact ⟨lo, hi, hlo, hhi, h1, h2⟩

/-! ### The enclosure around a candidate -/

theorem toVal_twice {n : AzFloat} {nv : ℝ} (hn : n.toVal = some (nv : EReal)) :
    (n <<< AzInt.ofInt 1).toVal = some ((2 * nv : ℝ) : EReal) := by
  rw [toVal_shiftLeft_of_toVal hn, AzInt.toInt_ofInt]
  norm_num [mul_comm]

/-- The upper end of `[D]·[c₁, c₂]` (`0 ≤ c₁`) from the upper end `D₂` of `[D]`. -/
theorem omegaMul_upper {D F₁ F₂ : AzFloat} {D₂ c₁ c₂ : ℝ} (hD : D.toVal = some (D₂ : EReal))
    (h₁ : F₁.toVal = some (c₁ : EReal)) (h₂ : F₂.toVal = some (c₂ : EReal)) (P : ℕ) [NeZero P] :
    ∃ Uv : ℝ, (if lt zero D = true then (mulPrecRound D F₂ P .Ceiling).1
        else (mulPrecRound D F₁ P .Ceiling).1).toVal = some (Uv : EReal) ∧
      (if 0 < D₂ then D₂ * c₂ else D₂ * c₁) ≤ Uv := by
  by_cases hc : lt zero D = true
  · rw [ite_eq_left hc, ite_eq_left ((lt_eq_true_iff toVal_zero' hD).mp hc)]
    obtain ⟨Uv, hUv, hUv1, -⟩ := mulCeiling_abs hD h₂ P
    exact ⟨Uv, hUv, hUv1⟩
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((lt_eq_true_iff toVal_zero' hD).mpr h))]
    obtain ⟨Uv, hUv, hUv1, -⟩ := mulCeiling_abs hD h₁ P
    exact ⟨Uv, hUv, hUv1⟩

/-- The lower end of `[D]·[c₁, c₂]` (`0 ≤ c₁`) from the lower end `D₁` of `[D]`. -/
theorem omegaMul_lower {D F₁ F₂ : AzFloat} {D₁ c₁ c₂ : ℝ} (hD : D.toVal = some (D₁ : EReal))
    (h₁ : F₁.toVal = some (c₁ : EReal)) (h₂ : F₂.toVal = some (c₂ : EReal)) (P : ℕ) [NeZero P] :
    ∃ Lv : ℝ, (if lt D zero = true then (mulPrecRound D F₂ P .Floor).1
        else (mulPrecRound D F₁ P .Floor).1).toVal = some (Lv : EReal) ∧
      Lv ≤ (if D₁ < 0 then D₁ * c₂ else D₁ * c₁) := by
  by_cases hc : lt D zero = true
  · rw [ite_eq_left hc, ite_eq_left ((lt_eq_true_iff hD toVal_zero').mp hc)]
    obtain ⟨Lv, hLv, hLv1, -⟩ := mulFloor_abs hD h₂ P
    exact ⟨Lv, hLv, hLv1⟩
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((lt_eq_true_iff hD toVal_zero').mpr h))]
    obtain ⟨Lv, hLv, hLv1, -⟩ := mulFloor_abs hD h₁ P
    exact ⟨Lv, hLv, hLv1⟩

/-- **The enclosure around a candidate contains `ω(x)`**, whatever the positive candidate. -/
theorem omegaEncl_spec {X : Encl} {xv : ℝ} (hX : IsEncl X xv) {n : AzFloat} {nv : ℝ}
    (hn : n.toVal = some (nv : EReal)) (hn0 : 0 < nv) {P : ℕ} (hP : 64 ≤ P) :
    IsEncl (omegaEncl X n P) (wrightOmegaReal xv) := by
  have : NeZero P := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ P ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ P ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ P := by positivity
  set ω := wrightOmegaReal xv with hωdef
  have hω : 0 < ω := wrightOmegaReal_pos xv
  have hωx : ω + Real.log ω = xv := dlmf_4_13_1_2_real xv
  have hNE : IsEnclPos (Encl.exact n) nv := ⟨nv, nv, hn, hn, hn0, le_rfl, le_rfl⟩
  have hDe : IsEncl (Encl.sub P (Encl.add P (Encl.exact n) (lnOfEncl (Encl.exact n) P)) X)
      (nv + Real.log nv - xv) :=
    (hNE.encloses0.encloses.add (lnOfEncl_pos hNE hP)).sub hX
  unfold omegaEncl
  simp only
  set D := Encl.sub P (Encl.add P (Encl.exact n) (lnOfEncl (Encl.exact n) P)) X with hDdef
  obtain ⟨D₁, D₂, hD₁, hD₂, hd1, hd2⟩ := hDe
  set d := nv + Real.log nv - xv with hd
  -- `d⁺`, `d⁻`
  have hdp : (maxOf zero D.2).toVal = some ((max 0 D₂ : ℝ) : EReal) := toVal_maxOf toVal_zero' hD₂
  have hnD : (-D.1).toVal = some ((-D₁ : ℝ) : EReal) := by
    rw [toVal_neg, hD₁, Option.map_some, EReal.coe_neg]
  have hdm : (maxOf zero (-D.1)).toVal = some ((max 0 (-D₁) : ℝ) : EReal) :=
    toVal_maxOf toVal_zero' hnD
  have hdp' : max d 0 ≤ max 0 D₂ := by rw [max_comm]; exact max_le_max le_rfl hd2
  have hdm' : max (-d) 0 ≤ max 0 (-D₁) := by
    rw [max_comm]; exact max_le_max le_rfl (by linarith)
  -- `m`
  have hmin : (minOf one n).toVal = some ((min 1 nv : ℝ) : EReal) := toVal_minOf toVal_one' hn
  have hmin0 : 0 ≤ min 1 nv := le_min zero_le_one hn0.le
  obtain ⟨r₁, hr₁, hr₁1, -⟩ := mulCeiling_abs hdp hmin P
  have hr₁0 : 0 ≤ r₁ := (mul_nonneg (le_max_left _ _) hmin0).trans hr₁1
  obtain ⟨m', hm', hm'1, -⟩ := subFloor_abs hn hr₁ P
  have hm : (maxOf zero (subPrecRound n (mulPrecRound (maxOf zero D.2) (minOf one n) P
      .Ceiling).1 P .Floor).1).toVal = some ((max 0 m' : ℝ) : EReal) := toVal_maxOf toVal_zero' hm'
  have hmle : max 0 m' ≤ min nv ω := by
    apply max_le (le_min hn0.le hω.le)
    apply le_min (by linarith)
    have h1 := sub_mul_min_le hn0 hω hωx hd
    have h2 : max d 0 * min 1 nv ≤ max 0 D₂ * min 1 nv := mul_le_mul_of_nonneg_right hdp' hmin0
    linarith
  -- `k` and `M`
  have hk : ∃ kv : ℝ, (if le (maxOf zero (-D.1)) oneHalf = true
      then minOf one (n <<< AzInt.ofInt 1) else one).toVal = some (kv : EReal) ∧ 0 ≤ kv ∧
      ω ≤ nv + max 0 (-D₁) * kv := by
    have hgen : ω ≤ nv + max 0 (-D₁) * 1 := by
      have := le_add hn0 hω hωx hd
      linarith
    by_cases hc : le (maxOf zero (-D.1)) oneHalf = true
    · rw [ite_eq_left hc]
      rw [le_eq_true_iff hdm toVal_oneHalf] at hc
      refine ⟨min 1 (2 * nv), toVal_minOf toVal_one' (toVal_twice hn),
        le_min zero_le_one (by linarith), ?_⟩
      rcases le_total 1 (2 * nv) with h | h
      · rw [min_eq_left h]; exact hgen
      · rw [min_eq_right h]
        have h1 := le_add_mul hn0 hω hωx hd (hdm'.trans hc)
        have h2 : max (-d) 0 * (2 * nv) ≤ max 0 (-D₁) * (2 * nv) :=
          mul_le_mul_of_nonneg_right hdm' (by linarith)
        linarith
    · rw [ite_eq_right hc]
      exact ⟨1, toVal_one', zero_le_one, hgen⟩
  obtain ⟨kv, hkv, hk0, hkω⟩ := hk
  obtain ⟨r₂, hr₂, hr₂1, -⟩ := mulCeiling_abs hdm hkv P
  have hr₂0 : 0 ≤ r₂ := (mul_nonneg (le_max_left _ _) hk0).trans hr₂1
  obtain ⟨Mv, hM, hM1, -⟩ := addCeiling_abs hn hr₂ P
  have hMle : max nv ω ≤ Mv := max_le (by linarith) (by linarith)
  have hM0 : 0 < Mv := lt_of_lt_of_le hn0 ((le_max_left _ _).trans hMle)
  -- `c₁`
  obtain ⟨s₁, hs₁, hs₁1, -⟩ := addCeiling_abs toVal_one' hm P
  have hm0 : 0 ≤ max 0 m' := le_max_left _ _
  have hs₁0 : 0 < s₁ := by linarith
  obtain ⟨c₁, hc₁, hc₁1, hc₁2⟩ := divFloor_abs hm hs₁ hs₁0.ne' P
  have hq₁ : 0 ≤ max 0 m' / s₁ := div_nonneg hm0 hs₁0.le
  have hc₁0 : 0 ≤ c₁ := by
    rw [abs_of_nonneg hq₁] at hc₁2
    nlinarith
  have hc₁le : c₁ ≤ max 0 m' / (1 + max 0 m') :=
    hc₁1.trans (div_le_div_of_nonneg_left hm0 (by linarith) hs₁1)
  -- `c₂`
  obtain ⟨s₂, hs₂, hs₂1, hs₂2⟩ := addFloor_abs toVal_one' hM P
  have hs₂0 : 0 < s₂ := by
    rw [abs_of_pos (by linarith)] at hs₂2
    nlinarith
  obtain ⟨c₂, hc₂, hc₂1, -⟩ := divCeiling_abs hM hs₂ hs₂0.ne' P
  have hc₂le : Mv / (1 + Mv) ≤ c₂ :=
    (div_le_div_of_nonneg_left hM0.le hs₂0 hs₂1).trans hc₂1
  -- the product `[D]·[c]`
  obtain ⟨hlo, hhi⟩ := candidate_encl hn0 hω hωx hd hm0 hmle hMle hc₁0 hc₁le hc₂le hd1 hd2
  obtain ⟨Uv, hUv, hUle⟩ := omegaMul_upper hD₂ hc₁ hc₂ P
  obtain ⟨Lv, hLv, hLle⟩ := omegaMul_lower hD₁ hc₁ hc₂ P
  obtain ⟨lo, hlo', hlo1, -⟩ := subFloor_abs hn hUv P
  obtain ⟨hi, hhi', hhi1, -⟩ := subCeiling_abs hn hLv P
  exact ⟨lo, hi, hlo', hhi', by linarith, by linarith⟩

/-! ### The bracket at a Ziv level -/

/-- The width bound of `wrightBracket` at level `w`. -/
noncomputable def omegaEps (a₀ b₀ ω : ℝ) (w : ℕ) : ℝ :=
  max (ω * (1 / 2 : ℝ) ^ w) (lambertEps a₀ b₀ none w)

theorem tendsto_omegaEps (a₀ b₀ ω : ℝ) (hab : a₀ ≤ b₀) :
    Filter.Tendsto (omegaEps a₀ b₀ ω) Filter.atTop (nhds 0) := by
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ω
  rw [mul_zero] at h1
  have := h1.max (tendsto_lambertEps a₀ b₀ none hab)
  rw [max_self] at this
  exact this

/-- `wrightBracket` encloses `ω(x)`, with width at most `omegaEps a₀ b₀ ω w`. -/
theorem wrightBracket_spec {xAt eAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    (hE : XEncl eAt (Real.exp xv)) {a₀ b₀ : ℝ}
    (ha₀ : (aprioriW0Pos eAt 64).1.toVal = some (a₀ : EReal))
    (hb₀ : (aprioriW0Pos eAt 64).2.toVal = some (b₀ : EReal))
    (haW : a₀ ≤ wrightOmegaReal xv) (hWb : wrightOmegaReal xv ≤ b₀)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt eAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) (w : ℕ) :
    ∃ lo hi : ℝ, (wrightBracket xAt eAt hs w).1.toVal = some (lo : EReal) ∧
      (wrightBracket xAt eAt hs w).2.toVal = some (hi : EReal) ∧ lo ≤ wrightOmegaReal xv ∧
      wrightOmegaReal xv ≤ hi ∧ hi - lo ≤ omegaEps a₀ b₀ (wrightOmegaReal xv) w := by
  have hω := wrightOmegaReal_pos xv
  unfold wrightBracket
  simp only
  split_ifs with hc
  · rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    obtain ⟨⟨hfin, hpos⟩, hle⟩ := hc
    have hn := toVal_of_isFinite hfin
    rw [lt_eq_true_iff toVal_zero' hn] at hpos
    have hP : 64 ≤ omegaWork (omegaCandidate xAt (w / 2 + 8)) w := le_max_left _ _
    obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := omegaEncl_spec (hX.isEncl hP) hn hpos hP
    obtain ⟨dv, hdv, hdv1, -⟩ := subCeiling_abs hhi hlo 64
    have hsh := toVal_shiftLeft_of_toVal hlo (-(AzNat.ofNat w).toAzInt)
    rw [AzInt.toInt_neg, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg, zpow_natCast,
      ← inv_pow, ← one_div] at hsh
    rw [le_eq_true_iff hdv hsh] at hle
    refine ⟨lo, hi, hlo, hhi, h1, h2, le_max_of_le_left ?_⟩
    have : lo * (1 / 2 : ℝ) ^ w ≤ wrightOmegaReal xv * (1 / 2 : ℝ) ^ w :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith
  · obtain ⟨lo, hi, hlo, hhi, h1, h2, hw⟩ := lambertBracket_spec true hE none ha₀ hb₀
      (wrightOmegaReal_mul_exp xv) haW hWb
      ⟨fun _ => by linarith, fun h => (Bool.false_ne_true h.symm).elim⟩ hs w
    exact ⟨lo, hi, hlo, hhi, h1, h2, le_max_of_le_right hw⟩

/-- `wrightApprox` brackets `ω(x)` by `Roundable`s. -/
theorem wrightApprox_spec {xAt eAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    (hE : XEncl eAt (Real.exp xv)) {a₀ b₀ : ℝ}
    (ha₀ : (aprioriW0Pos eAt 64).1.toVal = some (a₀ : EReal))
    (hb₀ : (aprioriW0Pos eAt 64).2.toVal = some (b₀ : EReal))
    (haW : a₀ ≤ wrightOmegaReal xv) (hWb : wrightOmegaReal xv ≤ b₀)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt eAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (wrightApprox xAt eAt hs w).1 lv ∧
      Rounds (wrightApprox xAt eAt hs w).2 hv ∧ lv ≤ wrightOmegaReal xv ∧
      wrightOmegaReal xv ≤ hv ∧ hv - lv ≤ omegaEps a₀ b₀ (wrightOmegaReal xv) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hw⟩ := wrightBracket_spec hX hE ha₀ hb₀ haW hWb hs w
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  exact ⟨lo, hi, hR1, hR2, h1, h2, hw⟩

/-! ### The certificates of the driver -/

/-- A rational target `x ≠ 1` with the enclosure functions of `x` and of `eˣ`. -/
def OmegaTarget (xAt eAt : ℕ → AzFloat × AzFloat) : Prop :=
  ∃ xv : ℝ, XEncl xAt xv ∧ XEncl eAt (Real.exp xv) ∧ (∃ r : ℚ, xv = r) ∧ xv ≠ 1

/-- The side certificate: no grid point `m` has `m eᵐ = eˣ`. -/
theorem omegaSideCert {xAt eAt : ℕ → AzFloat × AzFloat} (h : OmegaTarget xAt eAt)
    (M e' : AzInt) : ∃ k, (sideAt eAt (ofAzInt M <<< e') (64 * 2 ^ k)).isSome = true := by
  obtain ⟨xv, -, hE, ⟨r, hr⟩, h1⟩ := h
  apply exists_sideAt_isSome hE (toVal_gridPoint M e')
  obtain ⟨q, hq⟩ := gridVal_rat M e'
  rw [hq, hr]
  exact mul_exp_ne_exp_rat (by rintro rfl; exact h1 (by rw [hr, Rat.cast_one]))

/-- The Ziv certificate for a rational target `x ≠ 1`. -/
theorem omegaZivCert (p : ℕ) [NeZero p] (mode : RoundingMode) {xAt eAt : ℕ → AzFloat × AzFloat}
    (h : OmegaTarget xAt eAt)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt eAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) :
    ∃ f : ℕ, (roundingPossible
      (wrightApprox xAt eAt hs ((p + zivGuardBits) * 2 ^ f)).1
      (wrightApprox xAt eAt hs ((p + zivGuardBits) * 2 ^ f)).2 p mode).isSome = true := by
  obtain ⟨xv, hX, hE, ⟨r, hr⟩, h1⟩ := h
  obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriW0Pos_spec hE (Real.exp_pos xv) (le_refl 64)
  have hirr : Irrational (wrightOmegaReal xv) := by
    rw [hr]
    exact irrational_wrightOmegaReal (by rintro rfl; exact h1 (by rw [hr, Rat.cast_one]))
  exact exists_isSome_of_irrational_threshold p mode (wrightApprox xAt eAt hs) hirr
    (omegaEps a₀ b₀ (wrightOmegaReal xv)) (tendsto_omegaEps a₀ b₀ _ (haW.trans hWb)) 0
    (fun w _ => wrightApprox_spec hX hE ha₀ hb₀ haW hWb hs w) _
    (by unfold zivGuardBits; omega)

/-! ### Large arguments -/

/-- The large-argument path answers with the rounding of `ω(x)`. -/
theorem wrightOmegaHuge?_eq {nx : Roundable} {nxHi xLo : AzFloat} {e : AzInt} {w p : ℕ}
    [NeZero p] {mode : RoundingMode} {r : AzFloat × Ordering} {xv h l : ℝ}
    (hR : Rounds nx (-xv)) (hH : nxHi.toVal = some (h : EReal)) (hh : -xv ≤ h)
    (hL : xLo.toVal = some (l : EReal)) (hl : l ≤ xv) (hlt : xv < (2 : ℝ) ^ e.toInt)
    (hT : wrightOmegaHuge? nx nxHi xLo e w p mode = some r) :
    r = roundVal p mode (some ((wrightOmegaReal xv : ℝ) : EReal)) := by
  unfold wrightOmegaHuge? at hT
  split_ifs at hT with hc
  obtain ⟨hs, -, hone⟩ := hc
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hT
  have : NeZero (w + 8) := ⟨by omega⟩
  rw [lt_eq_true_iff toVal_one' hL] at hone
  have hx1 : 1 < xv := by linarith
  obtain ⟨hlo, hhi⟩ := bounds_of_one_lt hx1
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  have he0 : (0 : ℝ) ≤ (e.toInt : ℝ) := by
    rw [htoInt, hs]
    simp only [↓reduceIte, Int.cast_natCast]
    positivity
  have hlog : Real.log xv ≤ (e.toInt : ℝ) := by
    have h1 : Real.log xv < Real.log ((2 : ℝ) ^ e.toInt) :=
      Real.log_lt_log (by linarith) hlt
    rw [Real.log_zpow] at h1
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith
  obtain ⟨hi, hhi', hhi1, -⟩ := addCeiling_abs hH (toVal_ofAzInt e) (w + 8)
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi')
  rw [fval_of_toVal_coe hhi'] at hR2
  have hr := roundingPossible_eq' p (-mode) (v := -wrightOmegaReal xv) hR hR2
    (by linarith) (by linarith) (Or.inl fun hEq => absurd hEq (by linarith)) hr'
  rw [hr]
  have hneg := roundVal_neg p mode (-wrightOmegaReal xv)
  rw [neg_neg] at hneg
  exact hneg.symm

end Azurite.AzFloat
