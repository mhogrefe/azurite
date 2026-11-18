/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaRat
import Azurite.AzFloat.Equiv.Gamma
import Azurite.AzFloat.Equiv.LnGamma
import Azurite.AzFloat.Equiv.AcoshBracket
import Azurite.AzFloat.Equiv.PowRat
import Azurite.AzFloat.Equiv.LogBaseExact
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Unary
import Azurite.AzRat.Equiv.Mul

/-!
# Equivalence: `Γ` and `1/Γ` of a rational

* `gammaRatSinEncl_spec`, `gammaRatCore_spec`: the pieces on enclosures of rationals.
* `gammaRatTiny?_eq`, `reciprocalGammaRatTiny?_eq`: the tiny-argument paths.
* `gammaRatPrecRound_eq_or`, `reciprocalGammaRatPrecRound_eq_or`: the results are the correctly
  rounded `Spec.gamma q` and `Spec.reciprocalGamma q` unless the fuel runs out (`(nan, .eq)`).
-/

namespace Azurite.AzFloat

open Real

/-- A nonzero rational with the negative sign is negative. -/
theorem toRat_neg_of_sign_false (q : AzRat) (h0 : q.num ≠ 0) (hs : q.sign = false) :
    ((AzRat.toRat q : ℚ) : ℝ) < 0 := by
  have hne : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h))
  refine lt_of_le_of_ne (not_lt.mp fun hpos => ?_) hne
  rw [(toRat_sign_iff q h0).mpr hpos] at hs
  exact Bool.noConfusion hs

/-- `gammaRatSinEncl` answers with the sign and a positive enclosure of `|sin (π q)|`. -/
theorem gammaRatSinEncl_spec (q : AzRat) {W : ℕ} (hW : 64 ≤ W) {w : ℕ} (hw : 64 ≤ w)
    {neg : Bool} {S : Encl} (h : gammaRatSinEncl q W w = some (neg, S)) :
    IsEnclPos S ((if neg then -1 else 1) * Real.sin (π * ((AzRat.toRat q : ℚ) : ℝ))) := by
  unfold gammaRatSinEncl at h
  dsimp only at h
  generalize (q.round .Nearest).1 = k at h
  have hdv : ((AzRat.toRat (q - k.toAzRat) : ℚ) : ℝ) = ((AzRat.toRat q : ℚ) : ℝ) - k.toInt := by
    rw [AzRat.toRat_sub, AzRat.toRat_toAzRat_int]
    push_cast
    rfl
  split_ifs at h with h0 hs
  · refine gammaSinOfFrac_spec ?_ hW hw h
    have := lnGammaRatEncl_spec _ ((toRat_sign_iff _ h0).mp hs) W
    rw [hdv] at this
    simpa [hs] using this
  · have hs' : (q - k.toAzRat).sign = false := by simpa using hs
    refine gammaSinOfFrac_spec ?_ hW hw h
    have hneg := toRat_neg_of_sign_false _ h0 hs'
    have hv : ((AzRat.toRat (-(q - k.toAzRat)) : ℚ) : ℝ)
        = -(((AzRat.toRat q : ℚ) : ℝ) - k.toInt) := by
      rw [AzRat.toRat_neg, Rat.cast_neg, hdv]
    have := lnGammaRatEncl_spec (-(q - k.toAzRat)) (by rw [hv]; rw [hdv] at hneg; linarith) W
    rw [hv] at this
    simpa [hs'] using this

/-- **`gammaRatCore` answers with the sign and a positive enclosure of `|Γ(q)|` or
`|1/Γ(q)|`.** -/
theorem gammaRatCore_spec {recip : Bool} (q : AzRat) {e : AzInt} {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0) {w : ℕ} (hw : 64 ≤ w) {neg : Bool}
    {b : Encl} (h : gammaRatCore recip q e pos w = some (neg, b)) :
    IsEnclPos b ((if neg then -1 else 1) * gammaVal recip ((AzRat.toRat q : ℚ) : ℝ)) := by
  unfold gammaRatCore at h
  cases pos with
  | true =>
    have hx0 := hpos rfl
    rw [ite_eq_left rfl] at h
    dsimp only at h
    obtain ⟨b', hb', hbeq⟩ := Option.map_eq_some_iff.mp h
    rw [Prod.mk.injEq] at hbeq
    obtain ⟨rfl, rfl⟩ := hbeq
    have hL := lnGammaBracketEncl_spec (lnGammaRatEncl_spec q hx0 (w + gammaLnBits e)) e
      (w := w + gammaLnBits e) (by omega)
    simpa using gammaExpEncl_lnGamma hx0 hL hw hb'
  | false =>
    have hx0 := hneg rfl
    rw [ite_eq_right (by simp)] at h
    dsimp only at h
    set e' : AzInt := (if e.sign then e else 0) + 1
    have hv : ((AzRat.toRat (1 - q) : ℚ) : ℝ) = -((AzRat.toRat q : ℚ) : ℝ) + 1 := by
      rw [AzRat.toRat_sub, AzRat.toRat_one]
      push_cast
      ring
    have hX₁ := lnGammaRatEncl_spec (1 - q) (by rw [hv]; linarith) (w + gammaLnBits e')
    rw [hv] at hX₁
    have hL := lnGammaBracketEncl_spec hX₁ e' (w := w + gammaLnBits e') (by omega)
    refine gammaReflect_spec (by linarith) hw (fun G' hG => ?_)
      (fun neg' S' hS => gammaRatSinEncl_spec q (by omega) hw hS) h
    have := gammaExpEncl_lnGamma (recip := false)
      (by linarith : (0 : ℝ) < -((AzRat.toRat q : ℚ) : ℝ) + 1) hL hw hG
    simpa [gammaVal] using this

/-! ### Tiny arguments -/

/-- A tiny rational is at most `1/2` in absolute value. -/
theorem abs_le_half_of_gammaRatIsTiny {q : AzRat} {e : AzInt} {p : ℕ}
    (h : gammaRatIsTiny q e p = true) : |((AzRat.toRat q : ℚ) : ℝ)| ≤ 1 / 2 := by
  unfold gammaRatIsTiny at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨-, hC⟩, hF⟩ := h
  obtain ⟨l, hl, hl1, -⟩ := ofAzRatRound_floor_abs q 64
  obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs q 64
  have hhalf : (one <<< AzInt.ofInt (-1)).toVal = some (((1 / 2 : ℝ) : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal toVal_one' (AzInt.ofInt (-1)), AzInt.toInt_ofInt]
    norm_num
  have hnhalf : (-(one <<< AzInt.ofInt (-1))).toVal = some (((-(1 / 2) : ℝ) : ℝ) : EReal) := by
    rw [toVal_neg, hhalf, Option.map_some, EReal.coe_neg]
  have h1 := (le_eq_true_iff hc hhalf).mp hC
  have h2 := (le_eq_true_iff hnhalf hl).mp hF
  rw [abs_le]
  constructor <;> linarith

/-- The tiny-argument path of `Γ(q)` answers with the rounding of `Γ(q)`. -/
theorem gammaRatTiny?_eq (q : AzRat) (h0 : q.num ≠ 0) (e : AzInt) (p : ℕ) [NeZero p]
    (mode : RoundingMode) {r : AzFloat × Ordering} (h : gammaRatTiny? q e p mode = some r) :
    r = roundVal p mode (some ((Real.Gamma ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) := by
  unfold gammaRatTiny? at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  set xv := ((AzRat.toRat q : ℚ) : ℝ) with hxv
  obtain ⟨hG1, hG2⟩ := gamma_near_zero hx0 (abs_le_half_of_gammaRatIsTiny hc)
  obtain ⟨lo, hlo, hlo1, -⟩ := ofAzRatRound_floor_abs (-q⁻¹) (p + zivGuardBits + 8)
  obtain ⟨hi, hhi, hhi1, -⟩ := ofAzRatRound_ceiling_abs (-q⁻¹ + 1 + 1) (p + zivGuardBits + 8)
  have hv1 : ((AzRat.toRat (-q⁻¹) : ℚ) : ℝ) = -(1 / xv) := by
    rw [AzRat.toRat_neg, AzRat.toRat_inv]
    push_cast
    rw [one_div]
  have hv2 : ((AzRat.toRat (-q⁻¹ + 1 + 1) : ℚ) : ℝ) = -(1 / xv) + 2 := by
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
  have hr := roundingPossible_eq p (-mode) (v := -Real.Gamma xv) hR1 hR2 (by linarith)
    (by linarith) (fun h => absurd h (by linarith)) hr'
  rw [hr]
  have hneg := roundVal_neg p mode (-Real.Gamma xv)
  rw [neg_neg] at hneg
  exact hneg.symm

/-- The tiny-argument path of `1/Γ(q)` answers with the rounding of `1/Γ(q)`. -/
theorem reciprocalGammaRatTiny?_eq (q : AzRat) (h0 : q.num ≠ 0) (e : AzInt) (p : ℕ) [NeZero p]
    (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : reciprocalGammaRatTiny? q e p mode = some r) :
    r = roundVal p mode (some (((Real.Gamma ((AzRat.toRat q : ℚ) : ℝ))⁻¹ : ℝ) : EReal)) := by
  unfold reciprocalGammaRatTiny? at h
  dsimp only at h
  split_ifs at h with hc
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  set xv := ((AzRat.toRat q : ℚ) : ℝ) with hxv
  obtain ⟨hG1, hG2⟩ := inv_gamma_near_zero hx0 (abs_le_half_of_gammaRatIsTiny hc)
  obtain ⟨lo, hlo, hlo1, -⟩ := ofAzRatRound_floor_abs q (p + zivGuardBits + 8)
  obtain ⟨hi, hhi, hhi1, -⟩ := ofAzRatRound_ceiling_abs (q + q * q) (p + zivGuardBits + 8)
  have hv2 : ((AzRat.toRat (q + q * q) : ℚ) : ℝ) = xv + xv ^ 2 := by
    rw [AzRat.toRat_add, AzRat.toRat_mul]
    push_cast
    ring
  rw [hv2] at hhi1
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  exact roundingPossible_eq p mode (v := (Real.Gamma xv)⁻¹) hR1 hR2 (by linarith) (by linarith)
    (fun h' => absurd h' (by linarith)) h

/-! ### The specifications -/

/-- A small positive integer rational, as a natural number. -/
theorem gammaRatSmallInt_spec {q : AzRat} (h0 : q.num ≠ 0) {B : ℕ}
    (h : gammaRatSmallInt q B = true) :
    ∃ n : ℕ, q.num.toNat = n + 1 ∧ ((AzRat.toRat q : ℚ) : ℝ) = (n : ℝ) + 1 := by
  unfold gammaRatSmallInt at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hd, hs⟩, -⟩ := h
  have hn0 : q.num.toNat ≠ 0 := fun h => h0 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
  refine ⟨q.num.toNat - 1, by omega, ?_⟩
  rw [toRat_eq_of_int_den_one q hs hd]
  have : q.num.toNat = (q.num.toNat - 1) + 1 := by omega
  conv_lhs => rw [this]
  push_cast
  ring

/-- A rational pole: a negative integer. -/
theorem gammaRat_pole {q : AzRat} (h0 : q.num ≠ 0) (h : q.den = 1 ∧ q.sign = false) :
    ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = k :=
  ⟨toRat_neg_of_sign_false q h0 h.2, _, coe_toRat_eq_mkNorm_of_den_one q h.1⟩

/-- A rational that is not flagged as a pole is not one. -/
theorem gammaRat_not_pole {q : AzRat} (h0 : q.num ≠ 0) (h : ¬ (q.den = 1 ∧ q.sign = false)) :
    ¬ (((AzRat.toRat q : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = k) := by
  rintro ⟨hneg, hk⟩
  by_cases hd : q.den = 1
  · refine h ⟨hd, ?_⟩
    by_contra hs
    have := (toRat_sign_iff q h0).mp (by simpa using hs)
    linarith
  · exact not_exists_int_of_den_ne_one q hd hk

/-- The Ziv loop of the rational functions is correct when it does not give up. -/
theorem gammaRat_zivLoop (recip : Bool) (q : AzRat) (h0 : q.num ≠ 0) (e : AzInt) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    zivLoop (gammaRatApprox recip q e q.sign) p mode gammaFuel (gammaRatStart q e p)
        = roundVal p mode (some ((gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) ∨
      zivLoop (gammaRatApprox recip q e q.sign) p mode gammaFuel (gammaRatStart q e p)
        = (nan, .eq) := by
  rcases eq_or_ne (zivLoop (gammaRatApprox recip q e q.sign) p mode gammaFuel
    (gammaRatStart q e p)) (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => gammaApproxOf_valid_or_none
        (fun _ _ hc => gammaRatCore_spec q (fun hs => (toRat_sign_iff q h0).mp hs)
          (fun hs => toRat_neg_of_sign_false q h0 hs) hw hc) w p mode)
      _ _ (le_max_left _ _) hz

/-- **`Γ` of a rational is correctly rounded unless the fuel runs out.** -/
theorem gammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaRatPrecRound q p mode
        = roundVal p mode (Spec.gamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      gammaRatPrecRound q p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold gammaRatPrecRound
  by_cases h0 : q.num = 0
  · left
    rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, EReal.coe_zero,
      Spec.gamma_zero, roundVal_top]
  rw [ite_eq_right h0]
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  by_cases hpole : q.den = 1 ∧ q.sign = false
  · left
    obtain ⟨hneg, hk⟩ := gammaRat_pole h0 hpole
    rw [ite_eq_left hpole, Spec.gamma_coe_of_pole hneg hk, roundVal_none]
  rw [ite_eq_right hpole, ite_eq_right hp, Spec.gamma_coe hx0 (gammaRat_not_pole h0 hpole)]
  by_cases hsm : gammaRatSmallInt q (p + 65) = true
  · left
    obtain ⟨n, hn, hval⟩ := gammaRatSmallInt_spec h0 hsm
    rw [ite_eq_left hsm, hn, Nat.add_sub_cancel, hval, Real.Gamma_nat_eq_factorial,
      setPrecRound_eq_roundVal (toVal_ofAzNat _), AzNat.toNat_factorial]
  rw [ite_eq_right hsm]
  dsimp only
  split
  · rename_i r hr
    left
    exact gammaRatTiny?_eq q h0 _ p mode hr
  · exact gammaRat_zivLoop false q h0 _ p mode

/-- **`1/Γ` of a rational is correctly rounded unless the fuel runs out.** -/
theorem reciprocalGammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    reciprocalGammaRatPrecRound q p mode
        = roundVal p mode (Spec.reciprocalGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      reciprocalGammaRatPrecRound q p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold reciprocalGammaRatPrecRound
  rw [Spec.reciprocalGamma_coe]
  by_cases h0 : q.num = 0
  · left
    rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.Gamma_zero, inv_zero,
      EReal.coe_zero, roundVal_zero]
  rw [ite_eq_right h0]
  by_cases hpole : q.den = 1 ∧ q.sign = false
  · left
    obtain ⟨hneg, hk⟩ := gammaRat_pole h0 hpole
    rw [ite_eq_left hpole, Gamma_eq_zero_of_int_nonpos hneg.le hk, inv_zero, EReal.coe_zero,
      roundVal_zero]
  rw [ite_eq_right hpole, ite_eq_right hp]
  by_cases hsm : gammaRatSmallInt q (p + 65) = true
  · left
    obtain ⟨n, hn, hval⟩ := gammaRatSmallInt_spec h0 hsm
    have hf0 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [ite_eq_left hsm, hn, Nat.add_sub_cancel, hval, Real.Gamma_nat_eq_factorial,
      divPrecRound_eq_liftVal₂, liftVal₂, toVal_one', toVal_ofAzNat, Option.bind_some,
      Option.bind_some, AzNat.toNat_factorial, Spec.div_coe_coe _ _ hf0, one_div]
  rw [ite_eq_right hsm]
  dsimp only
  split
  · rename_i r hr
    left
    exact reciprocalGammaRatTiny?_eq q h0 _ p mode hr
  · exact gammaRat_zivLoop true q h0 _ p mode

end Azurite.AzFloat
