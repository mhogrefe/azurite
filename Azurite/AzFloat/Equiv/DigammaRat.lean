/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.DigammaRat
import Azurite.AzFloat.Equiv.Digamma
import Azurite.AzFloat.Equiv.GammaRat

/-!
# Equivalence: the digamma function of a rational

`digammaRatPrecRound_eq_or`: `digammaRatPrecRound q p mode` is the correct rounding of
`Spec.digamma q` (`Equiv/Digamma.lean`), or `(nan, .eq)` when the fuel of the Ziv loop runs
out.  The steps: `digammaRatFrac_spec` (the sign and the enclosure of `|q − k|`),
`digammaRatEncl_spec`, `digammaRatTiny?_eq`.
-/

namespace Azurite.AzFloat

open Real

/-- `digammaRatFrac` answers with the sign of `q − k` and a positive enclosure of `|q − k|`,
for an integer `k`. -/
theorem digammaRatFrac_spec (q : AzRat) (W : ℕ) :
    ∃ k : ℤ, ∀ σ A, digammaRatFrac q W = some (σ, A) →
      IsEnclPos A ((if σ then -1 else 1) * (((AzRat.toRat q : ℚ) : ℝ) - k)) := by
  refine ⟨((q.round .Nearest).1).toInt, fun σ A h => ?_⟩
  unfold digammaRatFrac at h
  dsimp only at h
  generalize (q.round .Nearest).1 = k at h ⊢
  have hdv : ((AzRat.toRat (q - k.toAzRat) : ℚ) : ℝ) = ((AzRat.toRat q : ℚ) : ℝ) - k.toInt := by
    rw [AzRat.toRat_sub, AzRat.toRat_toAzRat_int]
    push_cast
    rfl
  split_ifs at h with h0 hs
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := lnGammaRatEncl_spec _ ((toRat_sign_iff _ h0).mp hs) W
    rw [hdv] at this
    simpa [hs] using this
  · have hs' : (q - k.toAzRat).sign = false := by simpa using hs
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hneg := toRat_neg_of_sign_false _ h0 hs'
    have hv : ((AzRat.toRat (-(q - k.toAzRat)) : ℚ) : ℝ)
        = -(((AzRat.toRat q : ℚ) : ℝ) - k.toInt) := by
      rw [AzRat.toRat_neg, Rat.cast_neg, hdv]
    have := lnGammaRatEncl_spec (-(q - k.toAzRat)) (by rw [hv]; rw [hdv] at hneg; linarith) W
    rw [hv] at this
    simpa [hs'] using this

/-- **Every answer of `digammaRatEncl` encloses `ψ(q)`**, for `q > 0` (`pos`) or `q < 0` not an
integer. -/
theorem digammaRatEncl_spec (q : AzRat) {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧
      ∀ n : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ n) (e : AzInt) {w : ℕ} (hw : 64 ≤ w) {b : Encl}
    (h : digammaRatEncl q e pos w = some b) :
    IsEncl b (DLMF.psiR ((AzRat.toRat q : ℚ) : ℝ)) := by
  unfold digammaRatEncl at h
  cases pos with
  | true =>
    rw [ite_eq_left rfl, Option.some.injEq] at h
    subst h
    exact digammaPosEncl_spec (lnGammaRatEncl_spec q (hpos rfl) _) e hw
  | false =>
    rw [ite_eq_right (by simp)] at h
    dsimp only at h
    obtain ⟨hlt, hni⟩ := hneg rfl
    have hv : ((AzRat.toRat (1 - q) : ℚ) : ℝ) = 1 - ((AzRat.toRat q : ℚ) : ℝ) := by
      rw [AzRat.toRat_sub, AzRat.toRat_one]
      push_cast
      rfl
    have hP := digammaPosEncl_spec (lnGammaRatEncl_spec (1 - q) (by rw [hv]; linarith) (w + 32))
      ((if e.sign then e else 0) + 1) hw
    rw [hv] at hP
    obtain ⟨k, hk⟩ := digammaRatFrac_spec q (w + 16)
    exact digammaReflect_spec hni hw hk hP h

/-- A tiny rational is at most `1/4` in absolute value. -/
theorem abs_le_quarter_of_digammaRatIsTiny {q : AzRat} {e : AzInt} {p : ℕ}
    (h : digammaRatIsTiny q e p = true) : |((AzRat.toRat q : ℚ) : ℝ)| ≤ 1 / 4 := by
  unfold digammaRatIsTiny at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨-, hC⟩, hF⟩ := h
  obtain ⟨l, hl, hl1, -⟩ := ofAzRatRound_floor_abs q 64
  obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs q 64
  have hq : (one <<< AzInt.ofInt (-2)).toVal = some (((1 / 4 : ℝ) : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal toVal_one' (AzInt.ofInt (-2)), AzInt.toInt_ofInt]
    norm_num
  have hnq : (-(one <<< AzInt.ofInt (-2))).toVal = some (((-(1 / 4) : ℝ) : ℝ) : EReal) := by
    rw [toVal_neg, hq, Option.map_some, EReal.coe_neg]
  have h1 := (le_eq_true_iff hc hq).mp hC
  have h2 := (le_eq_true_iff hnq hl).mp hF
  rw [abs_le]
  constructor <;> linarith

/-- The tiny-argument path of `ψ(q)` answers with the rounding of `ψ(q)`. -/
theorem digammaRatTiny?_eq (q : AzRat) (h0 : q.num ≠ 0) (e : AzInt) (p : ℕ) [NeZero p]
    (mode : RoundingMode) {r : AzFloat × Ordering} (h : digammaRatTiny? q e p mode = some r) :
    r = roundVal p mode (some ((DLMF.psiR ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) := by
  unfold digammaRatTiny? at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  set xv := ((AzRat.toRat q : ℚ) : ℝ) with hxv
  obtain ⟨hG1, hG2⟩ := psiR_near_zero hx0 (abs_le_quarter_of_digammaRatIsTiny hc)
  obtain ⟨lo, hlo, hlo1, -⟩ := ofAzRatRound_floor_abs q⁻¹ (p + zivGuardBits + 8)
  obtain ⟨hi, hhi, hhi1, -⟩ := ofAzRatRound_ceiling_abs (q⁻¹ + 1 + 1) (p + zivGuardBits + 8)
  have hv1 : ((AzRat.toRat q⁻¹ : ℚ) : ℝ) = 1 / xv := by
    rw [AzRat.toRat_inv]
    push_cast
    rw [one_div]
  have hv2 : ((AzRat.toRat (q⁻¹ + 1 + 1) : ℚ) : ℝ) = 1 / xv + 2 := by
    rw [AzRat.toRat_add, AzRat.toRat_add, AzRat.toRat_one]
    push_cast
    rw [hv1]
    ring
  rw [hv1] at hlo1
  rw [hv2] at hhi1
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hr := roundingPossible_eq p (-mode) (v := -DLMF.psiR xv) hR1 hR2 (by linarith)
    (by linarith) (fun h => absurd h (by linarith)) hr'
  rw [hr]
  have hneg := roundVal_neg p mode (-DLMF.psiR xv)
  rw [neg_neg] at hneg
  exact hneg.symm

/-- The bracket of `ψ(q)` is valid, or rejected. -/
theorem digammaRatApprox_valid_or_none (q : AzRat) (h0 : q.num ≠ 0)
    (hpole : ¬ (q.den = 1 ∧ q.sign = false)) (e : AzInt) {w : ℕ} (hw : 64 ≤ w) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (digammaRatApprox q e q.sign w).1 lv ∧
        Rounds (digammaRatApprox q e q.sign w).2 hv ∧ lv ≤ DLMF.psiR ((AzRat.toRat q : ℚ) : ℝ) ∧
        DLMF.psiR ((AzRat.toRat q : ℚ) : ℝ) ≤ hv ∧
        (lv = DLMF.psiR ((AzRat.toRat q : ℚ) : ℝ) → hv = DLMF.psiR ((AzRat.toRat q : ℚ) : ℝ))) ∨
      roundingPossible (digammaRatApprox q e q.sign w).1 (digammaRatApprox q e q.sign w).2 p
        mode = none := by
  have hnp := gammaRat_not_pole h0 hpole
  exact lnAbsGammaApproxOf_valid_or_none
    (fun _ hc => digammaRatEncl_spec q (fun hs => (toRat_sign_iff q h0).mp hs)
      (fun hs => ⟨toRat_neg_of_sign_false q h0 hs,
        fun n hn => hnp ⟨toRat_neg_of_sign_false q h0 hs, n, hn⟩⟩) _ hw hc) w p mode

open Filter Topology in
/-- **The enclosure of `ψ(q)` converges** at every rational that is positive (`pos`) or
negative and not an integer. -/
theorem digammaRatEncl_conv (q : AzRat) {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧
      ∀ n : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ n) (e : AzInt) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ b : Encl,
      digammaRatEncl q e pos w = some b ∧ AEncl b (DLMF.psiR ((AzRat.toRat q : ℚ) : ℝ)) (E w) := by
  have hmono : ∀ w : ℕ, 6 * (1 / 2 : ℝ) ^ (w + 32 + 32) ≤ 8 * (1 / 2 : ℝ) ^ w := by
    intro w
    have : (1 / 2 : ℝ) ^ (w + 32 + 32) ≤ (1 / 2 : ℝ) ^ w :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    linarith
  cases pos with
  | true =>
    refine ⟨dgE ((AzRat.toRat q : ℚ) : ℝ) e, tendsto_dgE _ e, ?_⟩
    filter_upwards [digammaPosEncl_conv (hpos rfl) e] with w hw
    exact ⟨_, rfl, hw _ _ (lnGammaRatEncl_L q (hpos rfl) (w + 32)) (by positivity) (hmono w)⟩
  | false =>
    obtain ⟨hlt, hni⟩ := hneg rfl
    have hv : ((AzRat.toRat (1 - q) : ℚ) : ℝ) = 1 - ((AzRat.toRat q : ℚ) : ℝ) := by
      rw [AzRat.toRat_sub, AzRat.toRat_one]
      push_cast
      rfl
    have hpos1 : 0 < 1 - ((AzRat.toRat q : ℚ) : ℝ) := by linarith
    have hk1 := abs_sub_round_lt_one q
    have hdv : ((AzRat.toRat (q - (q.round .Nearest).1.toAzRat) : ℚ) : ℝ)
        = ((AzRat.toRat q : ℚ) : ℝ) - (q.round .Nearest).1.toInt := by
      rw [AzRat.toRat_sub, AzRat.toRat_toAzRat_int]
      push_cast
      rfl
    have hd : ((AzRat.toRat q : ℚ) : ℝ) - (((q.round .Nearest).1.toInt : ℤ) : ℝ) ≠ 0 :=
      fun h => hni _ (sub_eq_zero.mp h)
    have h0 : (q - (q.round .Nearest).1.toAzRat).num ≠ 0 := by
      intro h
      apply hd
      rw [← hdv, (AzRat.toRat_eq_zero_iff _).mpr h]
    obtain ⟨E, hE, hev⟩ := digammaReflect_conv (abs_pos.mpr hd) hk1
      (P := fun w => digammaPosEncl (lnGammaRatEncl (1 - q) (w + 32))
        ((if e.sign then e else 0) + 1) w)
      (F := fun w => digammaRatFrac q (w + 16))
      (tendsto_dgE (1 - ((AzRat.toRat q : ℚ) : ℝ)) ((if e.sign then e else 0) + 1))
      (by
        filter_upwards [digammaPosEncl_conv hpos1 ((if e.sign then e else 0) + 1)] with w hw
        have hL := lnGammaRatEncl_L (1 - q) (by rw [hv]; exact hpos1) (w + 32)
        rw [hv] at hL
        exact hw _ _ hL (by positivity) (hmono w))
      (by
        refine Eventually.of_forall fun w => ?_
        have hm : 6 * (1 / 2 : ℝ) ^ (w + 16 + 32) ≤ 6 * (1 / 2 : ℝ) ^ (w + 16) := by
          have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
            (by omega : w + 16 ≤ w + 16 + 32)
          linarith
        cases hs : (q - (q.round .Nearest).1.toAzRat).sign with
        | true =>
          have hp := (toRat_sign_iff _ h0).mp hs
          have hA := (lnGammaRatEncl_L _ hp (w + 16)).mono hm
          rw [hdv] at hp hA
          rw [← abs_of_pos hp] at hA
          refine ⟨false, _, ?_, hA⟩
          unfold digammaRatFrac
          simp only [h0, hs, ↓reduceIte, Bool.not_true]
        | false =>
          have hn := toRat_neg_of_sign_false _ h0 hs
          have hv2 : ((AzRat.toRat (-(q - (q.round .Nearest).1.toAzRat)) : ℚ) : ℝ)
              = -(((AzRat.toRat q : ℚ) : ℝ) - (q.round .Nearest).1.toInt) := by
            rw [AzRat.toRat_neg, Rat.cast_neg, hdv]
          rw [hdv] at hn
          have hA := (lnGammaRatEncl_L (-(q - (q.round .Nearest).1.toAzRat))
            (by rw [hv2]; linarith) (w + 16)).mono hm
          rw [hv2, ← abs_of_neg hn] at hA
          refine ⟨true, _, ?_, hA⟩
          unfold digammaRatFrac
          simp only [h0, hs, ↓reduceIte, Bool.not_false, Bool.false_eq_true])
    refine ⟨E, hE, ?_⟩
    filter_upwards [hev, eventually_ge_atTop 64] with w ⟨b, v, hb, hA⟩ hw
    have hsome : digammaRatEncl q e false w = some b := by
      unfold digammaRatEncl
      rw [ite_eq_right (by simp)]
      exact hb
    exact ⟨b, hsome, hA.of_isEncl (digammaRatEncl_spec q (pos := false) (fun h => by simp at h)
      (fun _ => ⟨hlt, hni⟩) e hw hsome)⟩

/-- **The bracket of `ψ(q)` converges.** -/
theorem digammaRatApprox_bracketConv (q : AzRat) {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧
      ∀ n : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ n) (e : AzInt) :
    BracketConv (digammaRatApprox q e pos) (DLMF.psiR ((AzRat.toRat q : ℚ) : ℝ)) :=
  lnAbsGammaApproxOf_bracketConv (digammaRatEncl_conv q hpos hneg e)

/-- **`ψ` of a rational is correctly rounded, or it is the loop with fuel** off `0` and the
poles. -/
theorem digammaRatPrecRoundFuel_eq_or_loop (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    digammaRatPrecRoundFuel fuel q p mode
        = roundVal p mode (Spec.digamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (q.num ≠ 0 ∧ ¬ (q.den = 1 ∧ q.sign = false) ∧
        digammaRatPrecRoundFuel fuel q p mode
          = zivLoop (digammaRatApprox q (gammaRatExp q) q.sign) p mode fuel
            (digammaRatStart q (gammaRatExp q) p)) := by
  have hp := NeZero.ne p
  unfold digammaRatPrecRoundFuel
  by_cases h0 : q.num = 0
  · left
    rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.digamma_zero, roundVal_bot]
  rw [ite_eq_right h0]
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  by_cases hpole : q.den = 1 ∧ q.sign = false
  · left
    obtain ⟨hneg, hk⟩ := gammaRat_pole h0 hpole
    rw [ite_eq_left hpole, Spec.digamma_coe_of_pole hneg hk, roundVal_none]
  have hnp := gammaRat_not_pole h0 hpole
  rw [ite_eq_right hpole, ite_eq_right hp, Spec.digamma_coe hx0 hnp]
  dsimp only
  split
  · rename_i r hr
    left
    exact digammaRatTiny?_eq q h0 _ p mode hr
  · exact Or.inr ⟨h0, hpole, rfl⟩

/-- **`ψ` of a rational is correctly rounded, or the fuel ran out**, at every fuel. -/
theorem digammaRatPrecRoundFuel_eq_or (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    digammaRatPrecRoundFuel fuel q p mode
        = roundVal p mode (Spec.digamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      digammaRatPrecRoundFuel fuel q p mode = (nan, .eq) := by
  rcases digammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨h0, hpole, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (digammaRatPrecRoundFuel fuel q p mode) (nan, .eq) with hz | hz
    · exact Or.inr hz
    · left
      have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
        h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
      rw [h] at hz ⊢
      rw [Spec.digamma_coe hx0 (gammaRat_not_pole h0 hpole)]
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => digammaRatApprox_valid_or_none q h0 hpole _ hw p mode)
        _ _ (le_max_left _ _) hz

/-- **`ψ` of a rational is correctly rounded unless the fuel runs out.** -/
theorem digammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    digammaRatPrecRound q p mode
        = roundVal p mode (Spec.digamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      digammaRatPrecRound q p mode = (nan, .eq) :=
  digammaRatPrecRoundFuel_eq_or (lnGammaFuel p) q p mode

/-- **The specification of `ψ` for rationals** (`ZivSpec`): sound at every fuel; complete in
the limit of the fuel wherever the value is no rounding boundary; correct at every fuel at
`0` and the poles.  No value of `ψ` at a rational is known to be irrational. -/
theorem digammaRatPrecRoundFuel_zivSpec :
    ZivSpec (fun q : AzRat => Spec.digamma (((AzRat.toRat q : ℚ) : ℝ) : EReal))
      digammaRatPrecRoundFuel
      {q | q.num = 0 ∨ (q.den = 1 ∧ q.sign = false)} ∅ where
  sound := fun fuel q p _ mode => digammaRatPrecRoundFuel_eq_or fuel q p mode
  complete := fun q p _ mode hB => by
    by_cases hgen : q.num ≠ 0 ∧ ¬ (q.den = 1 ∧ q.sign = false)
    · obtain ⟨h0, hpole⟩ := hgen
      have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
        h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
      have hnp := gammaRat_not_pole h0 hpole
      have hval := Spec.digamma_coe hx0 hnp
      have hB' := hB _ hval
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode
        (digammaRatApprox q (gammaRatExp q) q.sign)
        (digammaRatApprox_bracketConv q (fun hs => (toRat_sign_iff q h0).mp hs)
          (fun hs => ⟨toRat_neg_of_sign_false q h0 hs,
            fun n hn => hnp ⟨toRat_neg_of_sign_false q h0 hs, n, hn⟩⟩) _)
        (ne_zero_of_not_mem_floatSet hB') hB' (digammaRatStart q (gammaRatExp q) p)
        (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _))
        (fun w hw => (digammaRatApprox_valid_or_none q h0 hpole _
          (le_trans (le_max_left _ _) hw) p mode).imp_left
            fun ⟨lv, hv', h1, h2, h3, h4, _⟩ => ⟨lv, hv', h1, h2, h3, h4⟩)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases digammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨-, -, h⟩
      · exact h
      · rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases digammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨h0, hpole, -⟩
      · exact h
      · exact absurd ⟨h0, hpole⟩ hgen
  dyadic := fun q hq v hv => by
    exfalso
    by_cases h0 : q.num = 0
    · rw [coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.digamma_zero, Option.some.injEq] at hv
      exact EReal.coe_ne_bot v hv.symm
    · rcases hq with h | hpole
      · exact h0 h
      · obtain ⟨hneg, hk⟩ := gammaRat_pole h0 hpole
        rw [Spec.digamma_coe_of_pole hneg hk] at hv
        exact absurd hv (by simp)
  nondyadic := fun q h => absurd h (Set.notMem_empty _)
  correct := fun q hq fuel p _ mode => by
    rcases digammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨h0, hpole, -⟩
    · exact h
    · exfalso
      rcases hq with hD | hN
      · rcases hD with h | h
        · exact h0 h
        · exact hpole h
      · exact absurd hN (Set.notMem_empty _)

end Azurite.AzFloat
