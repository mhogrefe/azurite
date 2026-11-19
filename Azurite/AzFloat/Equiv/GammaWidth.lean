/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.GammaBracket
import Azurite.AzFloat.Equiv.LnGammaEventually
import Azurite.AzFloat.Equiv.ZivSpec

/-!
# The bracket of `Γ` converges

The widths of the pieces of `gammaApprox` (`AzFloat/GammaBracket.lean`), and with them the Ziv
certificate `gammaApprox_isSome_exists`: when `Γ(x)` is irrational, `roundingPossible` accepts
the bracket at some level `w₀ 2^f`.

* `expEnclPos?_width`, `gammaExpEncl_width`: the exponential of a narrow enclosure is delivered
  (not `none`), with width `expOfBracketEps`.
* `gammaStrict_width`, `gammaApproxOf_width`: making the enclosure strict costs a relative
  `2^(−2w)`.
* `gammaCore_pos_eventually`: for `x > 0` the core answers at every large level, with a width
  that tends to `0` (`lnGammaBracketEncl_eventually`).
-/

namespace Azurite.AzFloat

open Filter Topology

variable {a : Encl} {x ε : ℝ}

theorem AEncl.neg (h : AEncl a x ε) : AEncl (Encl.neg a) (-x) ε := by
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := h
  refine ⟨-u, -l, ?_, ?_, by linarith, by linarith, by linarith⟩
  · show (-a.2).toVal = _
    rw [toVal_neg, hu, Option.map_some, EReal.coe_neg]
  · show (-a.1).toVal = _
    rw [toVal_neg, hl, Option.map_some, EReal.coe_neg]

/-- An absolute width small against the value is a relative width. -/
theorem LEncl.ofA (h : AEncl a x ε) (hx : 2 * ε ≤ x) (hx0 : 0 < x) :
    LEncl a x (2 * ε / x) := by
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := h
  have hε : 0 ≤ ε := by linarith
  have hl0 : 0 < l := by linarith
  refine ⟨l, u, hl, hu, hl0, h1, h2, ?_⟩
  have h4 : 1 + 2 * ε / x ≤ Real.exp (2 * ε / x) := by
    linarith [Real.add_one_le_exp (2 * ε / x)]
  have h5 : ε ≤ l * (2 * ε / x) := by
    rw [mul_div_assoc', le_div_iff₀ hx0]
    nlinarith
  calc u ≤ l + ε := by linarith
    _ ≤ l * (1 + 2 * ε / x) := by linarith
    _ ≤ l * Real.exp (2 * ε / x) := mul_le_mul_of_nonneg_left h4 hl0.le

theorem expOfBracketEps_mono (v : ℝ) {δ δ' : ℝ} (h : δ ≤ δ') (w : ℕ) :
    expOfBracketEps v δ w ≤ expOfBracketEps v δ' w := by
  unfold expOfBracketEps
  have := mul_le_mul_of_nonneg_left
    (by linarith : 24 * δ + (1 / 2 : ℝ) ^ w / 4 ≤ 24 * δ' + (1 / 2 : ℝ) ^ w / 4)
    (Real.exp_pos v).le
  linarith

/-- `expEnclPos?` delivers the exponential of a narrow enclosure. -/
theorem expEnclPos?_width {M : Encl} {v ε : ℝ} (hM : AEncl M v ε) (hε : ε ≤ 1 / 2) {w : ℕ}
    (hw : 64 ≤ w) (hpos : expOfBracketEps v ε w < Real.exp v) :
    ∃ b, expEnclPos? M w = some b ∧ IsEnclPos b (Real.exp v) ∧
      AEncl b (Real.exp v) (expOfBracketEps v ε w) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := hM
  obtain ⟨r, hr, -, hr2⟩ := subCeiling_abs hhi hlo 64
  have hr1 : r ≤ 1 := by
    have h0 : 0 ≤ hi - lo := by linarith
    rw [abs_of_nonneg h0] at hr2
    have : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
    nlinarith
  obtain ⟨c, d, hc, hd, hc1, hd1, hcd⟩ :=
    expOfBracket_spec_width hlo hhi h1 h2 (by linarith) hw
  have hcd' := hcd.trans (expOfBracketEps_mono v h3 w)
  have hc0 : 0 < c := by linarith
  refine ⟨expOfBracket M w, ?_, ⟨c, d, hc, hd, hc0, hc1, hd1⟩, ⟨c, d, hc, hd, hc1, hd1, hcd'⟩⟩
  unfold expEnclPos?
  simp only [(le_eq_true_iff hr toVal_one').mpr hr1,
    (lt_eq_true_iff toVal_zero' hc).mpr hc0, ↓reduceIte]

/-- `gammaExpEncl` delivers `exp (± v)`. -/
theorem gammaExpEncl_width {neg : Bool} {L : Encl} {v ε : ℝ} (hL : AEncl L v ε)
    (hε : ε ≤ 1 / 2) {w : ℕ} (hw : 64 ≤ w)
    (hpos : expOfBracketEps (if neg then -v else v) ε w < Real.exp (if neg then -v else v)) :
    ∃ b, gammaExpEncl neg L w = some b ∧ IsEnclPos b (Real.exp (if neg then -v else v)) ∧
      AEncl b (Real.exp (if neg then -v else v))
        (expOfBracketEps (if neg then -v else v) ε w) := by
  unfold gammaExpEncl
  cases neg with
  | false => exact expEnclPos?_width hL hε hw hpos
  | true => exact expEnclPos?_width hL.neg hε hw hpos

theorem toInt_strictShift (w : ℕ) :
    (2 : ℝ) ^ (-(AzNat.ofNat (2 * w)).toAzInt).toInt = (1 / 2 : ℝ) ^ (2 * w) := by
  rw [AzInt.toInt_neg, toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg, zpow_natCast, one_div,
    inv_pow]

/-- `gammaStrict` widens by a relative `2^(−2w)`. -/
theorem gammaStrict_width {b : Encl} {v ε : ℝ} (hb : IsEnclPos b v) (hw : AEncl b v ε) (w : ℕ) :
    IsEnclW (gammaStrict b w) v (ε + 6 * (v + ε) * (1 / 2 : ℝ) ^ (2 * w)) := by
  obtain ⟨lo, hi, hlo, hhi, h0, h1, h2⟩ := hb
  obtain ⟨lo', hi', hlo', hhi', -, -, h3⟩ := hw
  rw [hlo, Option.some.injEq, EReal.coe_eq_coe_iff] at hlo'
  rw [hhi, Option.some.injEq, EReal.coe_eq_coe_iff] at hhi'
  subst hlo' hhi'
  have : NeZero (2 * w + 64) := ⟨by omega⟩
  set k : AzInt := -(AzNat.ofNat (2 * w)).toAzInt with hk
  have hkv : (2 : ℝ) ^ k.toInt = (1 / 2 : ℝ) ^ (2 * w) := toInt_strictShift w
  set t := (1 / 2 : ℝ) ^ (2 * w) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hu : (1 / 2 : ℝ) ^ (2 * w + 64) ≤ t / 2 := by
    rw [pow_add, ht]
    have : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
    nlinarith
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 * w + 64) := by positivity
  obtain ⟨r, hr, hr1, hr2⟩ := subFloor_abs hlo (toVal_shiftLeft_of_toVal hlo k) (2 * w + 64)
  obtain ⟨s, hs, hs1, hs2⟩ := addCeiling_abs hhi (toVal_shiftLeft_of_toVal hhi k) (2 * w + 64)
  rw [hkv] at hr1 hr2 hs1 hs2
  have hlt : 0 ≤ lo * t := by positivity
  have hht : 0 ≤ hi * t := by nlinarith
  have hlole : lo * t ≤ lo := by nlinarith
  have hhile : hi * t ≤ hi := by nlinarith
  rw [abs_of_nonneg (by linarith)] at hr2
  rw [abs_of_nonneg (by nlinarith)] at hs2
  have hhi_le : hi ≤ v + ε := by linarith
  have e1 : (lo - lo * t) * (1 / 2 : ℝ) ^ (2 * w + 64) ≤ lo * (t / 2) :=
    mul_le_mul (by linarith) hu hu0.le h0.le
  have e2 : (hi + hi * t) * (1 / 2 : ℝ) ^ (2 * w + 64) ≤ (2 * hi) * (t / 2) :=
    mul_le_mul (by linarith) hu hu0.le (by linarith)
  have e3 : hi * t ≤ (v + ε) * t := mul_le_mul_of_nonneg_right hhi_le ht0.le
  have e4 : lo * t ≤ hi * t := mul_le_mul_of_nonneg_right (by linarith) ht0.le
  refine ⟨r, s, hr, hs, by linarith, by linarith, ?_⟩
  nlinarith

/-- The bracket of `gammaApproxOf` from an answer of the core, with its width. -/
theorem gammaApproxOf_width {neg : Bool} {b : Encl} {v ε : ℝ}
    (hb : IsEnclPos b ((if neg then -1 else 1) * v))
    (hw : AEncl b ((if neg then -1 else 1) * v) ε) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (gammaApproxOf (some (neg, b)) w).1 lv ∧
      Rounds (gammaApproxOf (some (neg, b)) w).2 hv ∧ lv ≤ v ∧ v ≤ hv ∧
      hv - lv ≤ ε + 6 * (|v| + ε) * (1 / 2 : ℝ) ^ (2 * w) := by
  have h := negSwapApprox_of_isEnclW neg (gammaStrict_width hb hw w)
  have hpos : 0 < (if neg then -1 else 1) * v := by
    obtain ⟨l, u, -, -, h0, h1, -⟩ := hb
    linarith
  have habs : (if neg then -1 else 1) * v = |v| := by
    cases neg with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hpos ⊢
      exact (abs_of_pos hpos).symm
    | true =>
      simp only [↓reduceIte, neg_one_mul] at hpos ⊢
      exact (abs_of_neg (by linarith)).symm
  have hvv : (if neg then -1 else 1) * ((if neg then -1 else 1) * v) = v := by
    cases neg <;> simp
  rw [hvv, habs] at h
  exact h

/-- The core of a bracket of `v` converges: at every large level it answers with a positive
enclosure of `± v`, of a width that tends to `0`. -/
def CoreConv (c : ℕ → Option (Bool × Encl)) (v : ℝ) : Prop :=
  ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (b : Encl),
    c w = some (neg, b) ∧ IsEnclPos b ((if neg then -1 else 1) * v) ∧
      AEncl b ((if neg then -1 else 1) * v) (E w)

/-- **The bracket of a convergent core converges.** -/
theorem gammaApproxOf_bracketConv {c : ℕ → Option (Bool × Encl)} {v : ℝ} (hc : CoreConv c v) :
    BracketConv (fun w => gammaApproxOf (c w) w) v := by
  obtain ⟨E, hE, hev⟩ := hc
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hev
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (2 * w)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  have hε : Tendsto (fun w : ℕ => E w + 6 * (|v| + E w) * (1 / 2 : ℝ) ^ (2 * w)) atTop
      (𝓝 0) := by
    have := hE.add (((hE.const_add |v|).const_mul 6).mul hpow)
    simpa using this
  refine ⟨_, hε, W₀, fun w hw => ?_⟩
  obtain ⟨neg, b, hcw, hb, hwid⟩ := hW₀ w hw
  dsimp only
  rw [hcw]
  exact gammaApproxOf_width hb hwid w

/-- **The Ziv certificate of a convergent core at an irrational value.** -/
theorem gammaApproxOf_isSome_exists {c : ℕ → Option (Bool × Encl)} {v : ℝ} (hc : CoreConv c v)
    (hv : Irrational v) (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaApproxOf (c (w₀ * 2 ^ f)) (w₀ * 2 ^ f)).1
      (gammaApproxOf (c (w₀ * 2 ^ f)) (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  (gammaApproxOf_bracketConv hc).exists_isSome hv.ne_zero p
    (not_mem_floatSet_of_irrational p hv) mode w₀ hw₀

/-- The exponential of a convergent enclosure converges. -/
theorem gammaExpEncl_eventually (neg : Bool) (v : ℝ) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun w => expOfBracketEps (if neg then -v else v) (δ w) w) atTop (𝓝 0) ∧
      ∀ᶠ w in atTop, ∀ L : Encl, AEncl L v (δ w) →
        ∃ b, gammaExpEncl neg L w = some b ∧
          IsEnclPos b (Real.exp (if neg then -v else v)) ∧
          AEncl b (Real.exp (if neg then -v else v))
            (expOfBracketEps (if neg then -v else v) (δ w) w) := by
  set V := if neg then -v else v
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun w => expOfBracketEps V (δ w) w) atTop (𝓝 0) := by
    unfold expOfBracketEps
    have := (tendsto_expEps V).add (((hδ.const_mul 24).add (hpow.div_const 4)).const_mul
      (Real.exp V))
    simpa using this
  refine ⟨ht, ?_⟩
  filter_upwards [hδ.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    ht.eventually (gt_mem_nhds (Real.exp_pos V)), eventually_ge_atTop 64] with w h1 h2 h3 L hL
  exact gammaExpEncl_width hL h1 h3 h2

theorem CoreConv.congr {c c' : ℕ → Option (Bool × Encl)} {v : ℝ} (h : CoreConv c v)
    (hc : ∀ w, c' w = c w) : CoreConv c' v := by
  obtain ⟨E, hE, hev⟩ := h
  exact ⟨E, hE, hev.mono fun w hw => by rw [hc w]; exact hw⟩

theorem half_pow_le_eighth {W : ℕ} (hW : 3 ≤ W) : (1 / 2 : ℝ) ^ W ≤ 1 / 8 := by
  calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 3 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hW
    _ = 1 / 8 := by norm_num

theorem six_le_eight (w : ℕ) : 6 * (1 / 2 : ℝ) ^ (w + 32) ≤ 8 * (1 / 2 : ℝ) ^ w := by
  rw [pow_add]
  have : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have : (1 / 2 : ℝ) ^ 32 ≤ 1 := by norm_num
  nlinarith

/-- **The core of `Γ(x)` and `1/Γ(x)` converges for `x > 0`**, from enclosures `X w` of `x` of
relative width `6 · 2^(−w−32)`. -/
theorem coreConv_pos (recip : Bool) {xv : ℝ} (hpos : 0 < xv) (e : AzInt) (c : ℕ) {X : ℕ → Encl}
    (hX : ∀ w, LEncl (X w) xv (6 * (1 / 2 : ℝ) ^ (w + 32))) :
    CoreConv (fun w => (gammaExpEncl recip (lnGammaBracketEncl (X (w + c)) e (w + c)) w).map
      fun b => (false, b)) (gammaVal recip xv) := by
  obtain ⟨W₀, hW₀⟩ := lnGammaBracketEncl_eventually hpos e
  have hδ : Tendsto (fun w => lgEps xv e (w + c)) atTop (𝓝 0) :=
    (tendsto_lgEps xv e).comp (tendsto_add_atTop_nat _)
  obtain ⟨ht, hev⟩ := gammaExpEncl_eventually recip (Real.log (Real.Gamma xv)) hδ
  have hG := Real.Gamma_pos_of_pos hpos
  have hval : Real.exp (if recip then -Real.log (Real.Gamma xv) else Real.log (Real.Gamma xv))
      = gammaVal recip xv := by
    unfold gammaVal
    cases recip
    · simp [Real.exp_log hG]
    · simp [Real.exp_neg, Real.exp_log hG]
  refine ⟨_, ht, ?_⟩
  filter_upwards [hev, eventually_ge_atTop W₀] with w h1 h2
  have hL := hW₀ (w + c) (by omega) (X (w + c)) _ (hX (w + c)) (by positivity)
    (six_le_eight _)
  obtain ⟨b, hb, hb1, hb2⟩ := h1 _ hL
  rw [hval] at hb1 hb2
  refine ⟨false, b, ?_, by simpa using hb1, by simpa using hb2⟩
  simp [hb]

/-! ### The sine of the reflection formula -/

open Real

theorem round_nearest_eq_or (S : Set EReal) [RoundingTarget S] (r : ℝ) :
    RoundingTarget.round S .Nearest r = RoundingTarget.roundFloor S r ∨
      RoundingTarget.round S .Nearest r = RoundingTarget.roundCeiling S r := by
  unfold RoundingTarget.round
  dsimp only
  split
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact RoundingTarget.tiebreak_mem _ _

/-- Rounding a nonnegative real to nearest gives a nonnegative real. -/
theorem roundVal_nearest_nonneg (w : ℕ) [NeZero w] {r : ℝ} (hr : 0 ≤ r) :
    ∃ v : ℝ, (roundVal w .Nearest (some (r : EReal))).1.toVal = some (v : EReal) ∧ 0 ≤ v := by
  obtain ⟨vf, hf, -, hf0⟩ := roundVal_floor_spec w r
  obtain ⟨vc, hc, hc1⟩ := roundVal_ceiling_spec w r
  rw [(roundVal_coe w .Floor r).1] at hf
  rw [(roundVal_coe w .Ceiling r).1] at hc
  rw [(roundVal_coe w .Nearest r).1]
  rcases round_nearest_eq_or (floatSet w) r with h | h
  · exact ⟨vf, by rw [h]; exact hf, hf0 hr⟩
  · exact ⟨vc, by rw [h]; exact hc, hr.trans hc1⟩

/-- The integer next to `x` is within `1` of it. -/
theorem gammaNearInt_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    |xv - ((gammaNearInt x).toInt : ℝ)| < 1 := by
  obtain ⟨ht, -⟩ := truncToAzInt_spec hx
  rw [abs_sub_comm] at ht
  unfold gammaNearInt
  dsimp only
  split_ifs with hc
  · rw [AzInt.toInt_sub]
    have h1 : ((1 : AzInt).toInt : ℝ) = 1 := by norm_num [show (1 : AzInt).toInt = 1 from rfl]
    push_cast
    rw [h1]
    have hneg : xv - ((truncToAzInt x).toInt : ℝ) < 0 := by
      by_contra hge
      push Not at hge
      have : NeZero 64 := ⟨by norm_num⟩
      have hsub : (subPrecRound x (ofAzInt (truncToAzInt x)) 64 .Nearest).1
          = (roundVal 64 .Nearest (some ((xv - ((truncToAzInt x).toInt : ℝ) : ℝ) : EReal))).1 := by
        rw [subPrecRound_eq_liftVal₂, liftVal₂, hx, toVal_ofAzInt, Option.bind_some,
          Option.bind_some, Spec.sub_coe_coe]
      obtain ⟨v, hv, hv0⟩ := roundVal_nearest_nonneg 64 hge
      rw [← hsub] at hv
      have hh : (-(one <<< AzInt.ofInt (-1))).toVal = some (((-(1 / 2) : ℝ)) : EReal) := by
        rw [toVal_neg, toVal_shiftLeft_of_toVal toVal_one', Option.map_some, AzInt.toInt_ofInt]
        norm_num
      have := (lt_eq_true_iff hv hh).mp hc
      linarith
    rw [abs_lt] at ht ⊢
    constructor <;> linarith
  · exact ht

/-- `gammaFracEncl` answers at a non-integer, with a relative width `6 · 2^(−W)`. -/
theorem gammaFracEncl_some {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (k : AzInt)
    (hd : xv - (k.toInt : ℝ) ≠ 0) {W : ℕ} [NeZero W] (hu : (1 / 2 : ℝ) ^ W ≤ 1 / 8) :
    ∃ (σ : Bool) (A : Encl), gammaFracEncl x k W = some (σ, A) ∧
      LEncl A ((if σ then -1 else 1) * (xv - k.toInt)) (6 * (1 / 2 : ℝ) ^ W) := by
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  obtain ⟨r, hr, hr1, hr2⟩ := subFloor_abs hx (toVal_ofAzInt k) W
  obtain ⟨s, hs, hs1, hs2⟩ := subCeiling_abs hx (toVal_ofAzInt k) W
  set D := Encl.sub W (Encl.exact x) (Encl.exact (ofAzInt k)) with hD
  have hr' : D.1.toVal = some (r : EReal) := hr
  have hs' : D.2.toVal = some (s : EReal) := hs
  unfold gammaFracEncl
  dsimp only
  rw [← hD]
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · rw [abs_of_neg hneg] at hr2 hs2
    obtain ⟨p1, p2⟩ := round_pos_combine (lam := 0) (L := -(xv - k.toInt))
      (H := -(xv - k.toInt)) (rl := -s) (rh := -r) (by linarith) (by simp) hu0 hu
      (by linarith) (by linarith)
    have hs0 : s < 0 := by linarith
    have c1 : lt zero D.1 = false := by
      rw [← Bool.not_eq_true, lt_eq_true_iff toVal_zero' hr']
      linarith
    have c2 : lt D.2 zero = true := (lt_eq_true_iff hs' toVal_zero').mpr hs0
    refine ⟨true, Encl.neg D, by simp only [c1, c2, Bool.false_eq_true, ↓reduceIte],
      -s, -r, ?_, ?_, p1, by simp only [↓reduceIte]; linarith,
      by simp only [↓reduceIte]; linarith, ?_⟩
    · show (-D.2).toVal = _
      rw [toVal_neg, hs']; rfl
    · show (-D.1).toVal = _
      rw [toVal_neg, hr']; rfl
    · simpa using p2
  · rw [abs_of_pos hpos] at hr2 hs2
    obtain ⟨p1, p2⟩ := round_pos_combine (lam := 0) (L := xv - k.toInt)
      (H := xv - k.toInt) (rl := r) (rh := s) hpos (by simp) hu0 hu hr2 hs2
    have c1 : lt zero D.1 = true := (lt_eq_true_iff toVal_zero' hr').mpr p1
    refine ⟨false, D, by simp only [c1, ↓reduceIte], r, s, hr', hs', p1,
      by simpa using hr1, by simpa using hs1, by simpa using p2⟩

/-- An antitone envelope of the width of `sinBracket`. -/
noncomputable def sinEnv (w : ℕ) : ℝ := 89906 * (((w : ℝ) + 16) * (1 / 2 : ℝ) ^ (w + 12))

theorem sinEps_le_sinEnv (ex : AzInt) {w w' : ℕ} (h : w ≤ w') : sinEps ex w' ≤ sinEnv w := by
  have hanti : Antitone fun V : ℕ => ((V : ℝ) + 4) * (1 / 2 : ℝ) ^ V := by
    refine antitone_nat_of_succ_le fun V => ?_
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
    have hV : (0 : ℝ) ≤ V := Nat.cast_nonneg V
    rw [pow_succ]
    push_cast
    nlinarith
  have h1 := hanti (by omega : w + 12 ≤ w' + 12)
  simp only at h1
  push_cast at h1
  unfold sinEps sinCosEps sinCosEpsW sinEnv
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (w' + 12) := by positivity
  have hV : (0 : ℝ) ≤ w' := Nat.cast_nonneg w'
  push_cast
  have h2 : (1 / 2 : ℝ) ^ (w' + 12) ≤ ((w' : ℝ) + 12 + 4) * (1 / 2 : ℝ) ^ (w' + 12) := by
    nlinarith
  have h3 : ((w : ℝ) + 12 + 4) = (w : ℝ) + 16 := by ring
  rw [h3] at h1
  linarith

theorem tendsto_sinEnv : Tendsto sinEnv atTop (𝓝 0) := by
  have h : PB fun w : ℕ => 89906 * (((w : ℝ) + 16) * (1 / 2 : ℝ) ^ 12) :=
    ((PB.natCast.add (PB.const 16)).mul (PB.const _)).const_mul _
  refine h.tendsto.congr fun w => ?_
  unfold sinEnv
  rw [pow_add]
  ring

theorem sinEnv_nonneg (w : ℕ) : 0 ≤ sinEnv w := by
  unfold sinEnv
  positivity

/-- The width of `sinOfEncl`. -/
theorem sinOfEncl_width {Y : Encl} {y lam : ℝ} (hY : LEncl Y y lam) (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1 / 32) (hy : y ≤ 4) {W : ℕ} (hW : 64 ≤ W) {w w' : ℕ} (hw : 64 ≤ w)
    (hww : w ≤ w') (henv : sinEnv w ≤ 1) :
    AEncl (sinOfEncl Y W w') (Real.sin y) (sinEnv w + 32 * lam + 16 * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ W := by positivity
  have hu : (1 / 2 : ℝ) ^ W ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  have hy0 := hY.pos
  obtain ⟨tl, th, hl, hh, p, a1, a2, a3⟩ := hY.toA h0 (by linarith)
  obtain ⟨lo, hi, hlo, hhi, hs1, hs2, hs3⟩ :=
    sinBracket_spec hl (abs_lt_two_zpow_expOf hl) (by omega : 64 ≤ w')
  rw [abs_of_nonneg p] at hs1 hs2
  obtain ⟨r, hr, hr1, hr2⟩ := subCeiling_abs hh hl W
  rw [abs_of_nonneg (by linarith)] at hr2
  have hwid : th - tl ≤ 8 * lam := by nlinarith
  have hr3 : r ≤ 16 * lam := by nlinarith
  have hE : IsEncl0W (Encl.exact (subPrecRound Y.2 Y.1 W .Ceiling).1) r 0 :=
    ⟨r, r, hr, hr, by linarith, le_rfl, le_rfl, by simp⟩
  have hz : |Real.sin y - Real.sin tl| ≤ r := by
    refine (Real.abs_sin_sub_sin_le _ _).trans ?_
    rw [abs_of_nonneg (by linarith)]
    linarith
  obtain ⟨c, d, hc, hd, hc1, hd1, hcd⟩ := IsEnclW.widen0 (M := 1)
    (⟨lo, hi, hlo, hhi, hs1, hs2, hs3⟩ : IsEnclW _ (Real.sin tl) _) hE hz
    (Real.abs_sin_le_one _) (by linarith) ((sinEps_le_sinEnv _ hww).trans henv)
    (by norm_num) hW
  refine ⟨c, d, hc, hd, hc1, hd1, hcd.trans ?_⟩
  have := sinEps_le_sinEnv (expOf Y.1) hww
  linarith

theorem half_pow_le_of_64 {W : ℕ} (hW : 64 ≤ W) : (1 / 2 : ℝ) ^ W ≤ 1 / 2 ^ 64 := by
  calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 64 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hW
    _ = 1 / 2 ^ 64 := by norm_num

/-- `gammaSinOfFrac` answers once the width is below the sine. -/
theorem gammaSinOfFrac_some {σ : Bool} {k : AzInt} {A : Encl} {a : ℝ} {W : ℕ} (hW : 64 ≤ W)
    (hA : LEncl A a (6 * (1 / 2 : ℝ) ^ W)) (ha : a < 1) {w : ℕ} (hw : 64 ≤ w)
    (henv : sinEnv w ≤ 1) (hsmall : sinEnv w + 496 * (1 / 2 : ℝ) ^ W < Real.sin (a * π)) :
    ∃ S, gammaSinOfFrac σ k A W w = some (σ != k.isOdd, S) ∧
      AEncl S (Real.sin (a * π)) (sinEnv w + 496 * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  have hu := half_pow_le_of_64 hW
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ W := by positivity
  have hu8 : (1 / 2 : ℝ) ^ W ≤ 1 / 8 := hu.trans (by norm_num)
  have ha0 := hA.pos
  have hY : LEncl (Encl.mul W A (Encl.pi W)) (a * π) (15 * (1 / 2 : ℝ) ^ W) :=
    (hA.mul hu8 (LEncl.pi hW)).mono (by linarith)
  have hy4 : a * π ≤ 4 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  have hS := (sinOfEncl_width hY (by positivity) (by linarith [hu.trans (by norm_num :
    (1 : ℝ) / 2 ^ 64 ≤ 1 / 480)]) hy4 hW hw
    (Nat.le_add_right w (sinLostBits (Encl.mul W A (Encl.pi W)).1)) henv).mono
    (by linarith : sinEnv w + 32 * (15 * (1 / 2 : ℝ) ^ W) + 16 * (1 / 2 : ℝ) ^ W
      ≤ sinEnv w + 496 * (1 / 2 : ℝ) ^ W)
  refine ⟨_, ?_, hS⟩
  obtain ⟨c, d, hc, hd, hc1, hd1, hcd⟩ := hS
  have hc0 : 0 < c := by linarith
  unfold gammaSinOfFrac
  dsimp only
  rw [(lt_eq_true_iff toVal_zero' hc).mpr hc0]
  rfl

theorem abs_sin_pi_mul (xv : ℝ) (k : ℤ) (h1 : |xv - k| < 1) :
    |Real.sin (π * xv)| = Real.sin (|xv - k| * π) := by
  rw [sin_pi_mul_eq xv k, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hπ := Real.pi_pos
  rcases le_or_gt 0 (xv - k) with h | h
  · rw [abs_of_nonneg h] at h1 ⊢
    rw [mul_comm, abs_of_nonneg]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
  · rw [abs_of_neg h] at h1 ⊢
    have : Real.sin (π * (xv - k)) = -Real.sin (-(xv - k) * π) := by
      rw [← Real.sin_neg]
      congr 1
      ring
    rw [this, abs_neg, abs_of_nonneg]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)

theorem sign_mul_eq_abs {neg : Bool} {t : ℝ} (h : 0 < (if neg then -1 else 1) * t) :
    (if neg then -1 else 1) * t = |t| := by
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h ⊢
    exact (abs_of_pos h).symm
  | true =>
    simp only [↓reduceIte, neg_one_mul] at h ⊢
    exact (abs_of_neg (by linarith)).symm

/-- The sine of the reflection formula converges: at every large level it is a positive
enclosure of `|sin (π x)|`, with its sign, of a width that tends to `0`. -/
def SinConv (S : ℕ → Option (Bool × Encl)) (xv : ℝ) : Prop :=
  ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (S' : Encl),
    S w = some (neg, S') ∧ IsEnclPos S' ((if neg then -1 else 1) * Real.sin (π * xv)) ∧
      AEncl S' |Real.sin (π * xv)| (E w)

/-- **The sine of the reflection formula converges** at a non-integer. -/
theorem gammaSinEncl_conv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hint : ∀ k : ℤ, xv ≠ k) : SinConv (fun w => gammaSinEncl x (w + 16) w) xv := by
  have hk1 := gammaNearInt_spec hx
  have hd : xv - ((gammaNearInt x).toInt : ℝ) ≠ 0 := fun h => hint _ (sub_eq_zero.mp h)
  have hval := abs_sin_pi_mul xv (gammaNearInt x).toInt hk1
  have hspos : 0 < |Real.sin (π * xv)| := by
    rw [hval]
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos (abs_pos.mpr hd) Real.pi_pos)
      (by nlinarith [Real.pi_pos])
  have hpow : Tendsto (fun w : ℕ => 496 * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).comp (tendsto_add_atTop_nat 16)).const_mul 496
    simpa using this
  have hE : Tendsto (fun w => sinEnv w + 496 * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    simpa using tendsto_sinEnv.add hpow
  refine ⟨_, hE, ?_⟩
  filter_upwards [hE.eventually (gt_mem_nhds hspos),
    tendsto_sinEnv.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 64] with w h1 h2 h3
  have hW : 64 ≤ w + 16 := by omega
  have : NeZero (w + 16) := ⟨by omega⟩
  obtain ⟨σ, A, hF, hA⟩ := gammaFracEncl_some hx (gammaNearInt x) hd (W := w + 16)
    ((half_pow_le_of_64 hW).trans (by norm_num))
  rw [sign_mul_eq_abs hA.pos] at hA
  rw [hval] at h1
  obtain ⟨S, hS, hSw⟩ := gammaSinOfFrac_some (σ := σ) (k := gammaNearInt x) hW hA hk1 h3 h2 h1
  have hsome : gammaSinEncl x (w + 16) w = some (σ != (gammaNearInt x).isOdd, S) := by
    unfold gammaSinEncl
    simp only [hF]
    exact hS
  rw [← hval] at hSw
  exact ⟨_, S, hsome, gammaSinEncl_spec hx hW h3 hsome, hSw⟩

/-! ### The reflection formula -/

/-- The reflection formula on relative widths. -/
theorem gammaReflect_width (recip : Bool) {G S : Encl} {neg : Bool} {xv lamS lamG : ℝ}
    (hx1 : xv < 1) {w : ℕ} (hw : 64 ≤ w) (hG : LEncl G (Real.Gamma (-xv + 1)) lamG)
    (hS : LEncl S ((if neg then -1 else 1) * Real.sin (π * xv)) lamS) :
    ∃ b, gammaReflect recip (some G) (some (neg, S)) w = some (neg, b) ∧
      LEncl b ((if neg then -1 else 1) * gammaVal recip xv)
        (lamS + lamG + 15 * (1 / 2 : ℝ) ^ (w + 16)) := by
  have hV : 64 ≤ w + 16 := by omega
  have : NeZero (w + 16) := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ (w + 16) ≤ 1 / 8 := (half_pow_le_of_64 hV).trans (by norm_num)
  have hg0 : 0 < Real.Gamma (-xv + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hs0 := hS.pos
  have hsin0 : Real.sin (π * xv) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs0
    exact lt_irrefl _ hs0
  have hrefl := Real.Gamma_mul_Gamma_one_sub xv
  rw [show (1 : ℝ) - xv = -xv + 1 by ring] at hrefl
  have hGx : Real.Gamma xv = π / (Real.sin (π * xv) * Real.Gamma (-xv + 1)) := by
    rw [eq_div_iff (mul_ne_zero hsin0 hg0.ne'), mul_comm (Real.sin _), ← mul_assoc, hrefl]
    field_simp
  have hT := hS.mul hu8 hG
  have hπ := LEncl.pi hV
  unfold gammaReflect gammaVal
  dsimp only
  cases recip
  · refine ⟨_, rfl, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h := (hπ.div hu8 hT).mono (le_of_eq (by ring :
      3 * (1 / 2 : ℝ) ^ (w + 16) + (lamS + lamG + 6 * (1 / 2 : ℝ) ^ (w + 16))
          + 6 * (1 / 2 : ℝ) ^ (w + 16)
        = lamS + lamG + 15 * (1 / 2 : ℝ) ^ (w + 16)))
    convert h using 1
    rw [hGx]
    cases neg
    · simp
    · simp only [↓reduceIte, neg_one_mul]
      rw [← div_neg, ← neg_mul]
  · refine ⟨_, rfl, ?_⟩
    simp only [↓reduceIte]
    have h := (hT.div hu8 hπ).mono (le_of_eq (by ring :
      (lamS + lamG + 6 * (1 / 2 : ℝ) ^ (w + 16)) + 3 * (1 / 2 : ℝ) ^ (w + 16)
          + 6 * (1 / 2 : ℝ) ^ (w + 16)
        = lamS + lamG + 15 * (1 / 2 : ℝ) ^ (w + 16)))
    convert h using 1
    rw [hGx, inv_div]
    ring

/-- **The core of `Γ(x)` and `1/Γ(x)` converges for a negative non-integer `x`**, from
enclosures `X w` of `1 − x` of relative width `6 · 2^(−w−32)` and a convergent sine. -/
theorem coreConv_reflect (recip : Bool) {xv : ℝ} (hneg : xv < 0) (e' : AzInt) (c : ℕ)
    {X : ℕ → Encl} (hX : ∀ w, LEncl (X w) (-xv + 1) (6 * (1 / 2 : ℝ) ^ (w + 32)))
    {S : ℕ → Option (Bool × Encl)} (hSc : SinConv S xv) :
    CoreConv (fun w => gammaReflect recip
      (gammaExpEncl false (lnGammaBracketEncl (X (w + c)) e' (w + c)) w) (S w) w)
      (gammaVal recip xv) := by
  have hpos1 : 0 < -xv + 1 := by linarith
  obtain ⟨W₀, hW₀⟩ := lnGammaBracketEncl_eventually hpos1 e'
  have hδ : Tendsto (fun w => lgEps (-xv + 1) e' (w + c)) atTop (𝓝 0) :=
    (tendsto_lgEps _ e').comp (tendsto_add_atTop_nat _)
  obtain ⟨htG, hevG⟩ := gammaExpEncl_eventually false (Real.log (Real.Gamma (-xv + 1))) hδ
  simp only [Bool.false_eq_true, ↓reduceIte] at htG hevG
  have hg0 : 0 < Real.Gamma (-xv + 1) := Real.Gamma_pos_of_pos hpos1
  rw [Real.exp_log hg0] at hevG
  obtain ⟨ES, htS, hevS⟩ := hSc
  set g := Real.Gamma (-xv + 1) with hg
  set s := |Real.sin (π * xv)| with hs
  have hs0 : 0 < s := by
    obtain ⟨w, neg, S', -, hSp, -⟩ := hevS.exists
    exact abs_pos.mpr fun h0 => by
      obtain ⟨l, u, -, -, hl0, hl1, -⟩ := hSp
      rw [h0, mul_zero] at hl1
      linarith
  set EG : ℕ → ℝ := fun w => expOfBracketEps (Real.log g) (lgEps (-xv + 1) e' (w + c)) w
    with hEG
  have hpow : Tendsto (fun w : ℕ => 15 * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).comp (tendsto_add_atTop_nat 16)).const_mul 15
    simpa using this
  have hlam : Tendsto (fun w => 2 * ES w / s + 2 * EG w / g + 15 * (1 / 2 : ℝ) ^ (w + 16))
      atTop (𝓝 0) := by
    have := (((htS.const_mul 2).div_const s).add ((htG.const_mul 2).div_const g)).add hpow
    simpa using this
  have hE : Tendsto (fun w => 2 * |gammaVal recip xv|
      * (2 * ES w / s + 2 * EG w / g + 15 * (1 / 2 : ℝ) ^ (w + 16))) atTop (𝓝 0) := by
    simpa using hlam.const_mul (2 * |gammaVal recip xv|)
  refine ⟨_, hE, ?_⟩
  filter_upwards [hevG, hevS, eventually_ge_atTop W₀, eventually_ge_atTop 64,
    htS.eventually (ge_mem_nhds (by positivity : 0 < s / 2)),
    htG.eventually (ge_mem_nhds (by positivity : 0 < g / 2)),
    hlam.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with w h1 h2 h3 h4 h5 h6 h7
  have hL := hW₀ (w + c) (by omega) _ _ (hX (w + c)) (by positivity) (six_le_eight _)
  obtain ⟨G, hG, hGp, hGw⟩ := h1 _ hL
  obtain ⟨neg, S', hS, hSp, hSw⟩ := h2
  have hsv : (if neg then -1 else 1) * Real.sin (π * xv) = s := by
    obtain ⟨l, u, -, -, hl0, hl1, -⟩ := hSp
    exact sign_mul_eq_abs (by linarith)
  have hSL : LEncl S' ((if neg then -1 else 1) * Real.sin (π * xv)) (2 * ES w / s) := by
    rw [hsv]
    exact LEncl.ofA hSw (by linarith) hs0
  have hGL : LEncl G g (2 * EG w / g) := LEncl.ofA hGw (by linarith) hg0
  obtain ⟨b, hb, hbL⟩ := gammaReflect_width recip (by linarith : xv < 1) h4 hGL hSL
  have hcore : gammaReflect recip
      (gammaExpEncl false (lnGammaBracketEncl (X (w + c)) e' (w + c)) w) (S w) w
      = some (neg, b) := by
    rw [hG, hS]
    exact hb
  have hvpos := hbL.pos
  have h8 : 0 ≤ ES w := by
    obtain ⟨l, u, -, -, a1, a2, a3⟩ := hSw
    linarith
  have h9 : 0 ≤ EG w := by
    obtain ⟨l, u, -, -, a1, a2, a3⟩ := hGw
    linarith
  have hA := (hbL.toA (by positivity) h7).toA
  rw [sign_mul_eq_abs hvpos] at hA
  refine ⟨neg, b, hcore, hbL.isEnclPos, ?_⟩
  rw [sign_mul_eq_abs hvpos]
  exact hA

/-- **The core of `Γ(x)` and `1/Γ(x)` converges** at every finite `x` that is not `0` or a
negative integer (`pos` the sign of `x`). -/
theorem gammaCore_conv (recip : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (e : AzInt) {pos : Bool} (hpos : pos = true → 0 < xv)
    (hneg : pos = false → xv < 0 ∧ ∀ k : ℤ, xv ≠ k) :
    CoreConv (gammaCore recip x e pos) (gammaVal recip xv) := by
  cases pos with
  | true =>
    have h0 := hpos rfl
    refine (coreConv_pos recip h0 e (gammaLnBits e) (X := fun _ => Encl.exact x)
      fun w => (LEncl.exact hx h0).mono (by positivity)).congr fun w => ?_
    simp [gammaCore, lnGammaBracket]
  | false =>
    obtain ⟨h0, hint⟩ := hneg rfl
    have hnx : (-x).toVal = some ((-xv : ℝ) : EReal) := by
      rw [toVal_neg, hx, Option.map_some, EReal.coe_neg]
    refine (coreConv_reflect recip h0 ((if e.sign then e else 0) + 1)
      (gammaLnBits ((if e.sign then e else 0) + 1))
      (X := fun w => Encl.add (w + 32) (Encl.exact (-x)) (Encl.exact one)) (fun w => ?_)
      (gammaSinEncl_conv hx hint)).congr fun w => ?_
    · have : NeZero (w + 32) := ⟨by omega⟩
      have hu32 : (1 / 2 : ℝ) ^ (w + 32) ≤ 1 / 8 := half_pow_le_eighth (by omega)
      have := LEncl.add_exact (w := w + 32) (b := Encl.exact one) hu32
        (LEncl.exact hnx (by linarith)) le_rfl toVal_one' toVal_one' zero_le_one
      rwa [zero_add] at this
    · simp [gammaCore]

/-- **The Ziv certificate of `Γ(x)` and `1/Γ(x)` at an irrational value**: some level
`w₀ 2^f` is accepted. -/
theorem gammaApprox_isSome_exists (recip : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (e : AzInt) {pos : Bool} (hpos : pos = true → 0 < xv)
    (hneg : pos = false → xv < 0 ∧ ∀ k : ℤ, xv ≠ k) (hirr : Irrational (gammaVal recip xv))
    (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaApprox recip x e pos (w₀ * 2 ^ f)).1
      (gammaApprox recip x e pos (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  gammaApproxOf_isSome_exists (gammaCore_conv recip hx e hpos hneg) hirr p mode w₀ hw₀

/-- **The bracket of `Γ(x)` and `1/Γ(x)` converges** at every finite `x` that is not `0` or a
negative integer. -/
theorem gammaApprox_bracketConv (recip : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (e : AzInt) {pos : Bool} (hpos : pos = true → 0 < xv)
    (hneg : pos = false → xv < 0 ∧ ∀ k : ℤ, xv ≠ k) :
    BracketConv (gammaApprox recip x e pos) (gammaVal recip xv) :=
  gammaApproxOf_bracketConv (gammaCore_conv recip hx e hpos hneg)

end Azurite.AzFloat
