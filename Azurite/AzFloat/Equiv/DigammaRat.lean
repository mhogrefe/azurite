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

/-- **`ψ` of a rational is correctly rounded unless the fuel runs out.** -/
theorem digammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    digammaRatPrecRound q p mode
        = roundVal p mode (Spec.digamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      digammaRatPrecRound q p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold digammaRatPrecRound
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
  · rcases eq_or_ne (zivLoop (digammaRatApprox q (gammaRatExp q) q.sign) p mode (lnGammaFuel p)
      (digammaRatStart q (gammaRatExp q) p)) (nan, .eq) with hz | hz
    · right; exact hz
    · left
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => lnAbsGammaApproxOf_valid_or_none
          (fun _ hc => digammaRatEncl_spec q (fun hs => (toRat_sign_iff q h0).mp hs)
            (fun hs => ⟨toRat_neg_of_sign_false q h0 hs,
              fun n hn => hnp ⟨toRat_neg_of_sign_false q h0 hs, n, hn⟩⟩) _ hw hc) w p mode)
        _ _ (le_max_left _ _) hz

end Azurite.AzFloat
