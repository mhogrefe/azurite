/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GenPochhammerRat
import Azurite.AzFloat.Equiv.GenPochhammer
import Azurite.AzFloat.Equiv.PochhammerRat
import Azurite.AzFloat.Equiv.BetaRat

/-!
# Equivalence: the generalized Pochhammer symbol of two rationals

`genPochhammerRatPrecRound_eq_or`: `genPochhammerRatPrecRound x y p mode` is the correct
rounding of `Spec.genPochhammerReal x y` (`Equiv/GenPochhammer.lean`), or `(nan, .eq)` when
the fuel of the Ziv loop runs out; `genPochhammerRatPrecRoundFuel_zivSpec` is the full
specification, with the arguments `genPochRatSpecial` at which the fuel cannot run out.
-/

namespace Azurite.AzFloat

open Finset

/-- **`genPochRatNegIntFuel` is correct at every fuel** at the rationals recognized by
`recipPochRatSpecial`. -/
theorem genPochRatNegIntFuel_eq_of_special (fuel : ℕ) {x : AzRat} {n : ℕ} (hn : n ≠ 0)
    (hs : recipPochRatSpecial x n = true) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    genPochRatNegIntFuel fuel x n p mode
      = roundVal p mode (Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ) (-(n : ℝ))) := by
  have hnd := not_isDyadic_recipPochRat hs
  have hne : ∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j) ≠ 0 := fun h0 => hnd (by
    rw [h0, inv_zero]
    exact isDyadic_zero)
  have hpole : ¬ genPochRatPole x n = true := fun h => hne ((genPochRatPole_iff x n).mp h)
  rw [Spec.genPochhammerReal_neg_nat _ hn, ite_eq_right hne]
  unfold genPochRatNegIntFuel
  rw [ite_eq_right hpole, dite_eq_right (NeZero.ne p)]
  by_cases hc : (n ≤ 128 ∧ x.num.size + x.den.size ≤ 2 * p + 1024)
      ∨ pochExactCheap (x.num.size + x.den.size) n p = true
  · rw [ite_eq_left hc]
    exact recipPochIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast den_pos_real x)
      (mkNorm_div_den_eq x) hne p mode
  · rw [ite_eq_right hc, dite_eq_left hs]
    exact zivLoopBacked_eq p mode _ (not_mem_floatSet_of_not_isDyadic p hnd) 64
      (fun w hw => (recipPochRatApprox_valid_or_none x n hw p mode).imp_left
        fun ⟨lv, hv', h1, h2, h3, h4, _⟩ => ⟨lv, hv', h1, h2, h3, h4⟩)
      fuel _ (le_max_left _ _) (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _)) _

/-- **`genPochRatNegIntFuel` is exact or a convergent loop.** -/
theorem genPochRatNegIntFuel_zivCases (x : AzRat) {n : ℕ} (hn : n ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ZivCases (fun fuel => genPochRatNegIntFuel fuel x n p mode)
      (Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ) (-(n : ℝ))) p mode := by
  by_cases hs : recipPochRatSpecial x n = true
  · exact Or.inl fun fuel => genPochRatNegIntFuel_eq_of_special fuel hn hs p mode
  rw [Spec.genPochhammerReal_neg_nat _ hn]
  by_cases hpole : genPochRatPole x n = true
  · refine Or.inl fun fuel => ?_
    show genPochRatNegIntFuel fuel x n p mode = _
    unfold genPochRatNegIntFuel
    rw [ite_eq_left hpole, ite_eq_left ((genPochRatPole_iff x n).mp hpole), roundVal_none]
  have hne : ∏ j ∈ range n, (((AzRat.toRat x : ℚ) : ℝ) - n + j) ≠ 0 :=
    fun h0 => hpole ((genPochRatPole_iff x n).mpr h0)
  rw [ite_eq_right hne]
  by_cases hc : (n ≤ 128 ∧ x.num.size + x.den.size ≤ 2 * p + 1024)
      ∨ pochExactCheap (x.num.size + x.den.size) n p = true
  · refine Or.inl fun fuel => ?_
    show genPochRatNegIntFuel fuel x n p mode = _
    unfold genPochRatNegIntFuel
    rw [ite_eq_right hpole, dite_eq_right (NeZero.ne p), ite_eq_left hc]
    exact recipPochIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast den_pos_real x)
      (mkNorm_div_den_eq x) hne p mode
  · refine (ZivCases.of_core (recipPochRat_coreConv x hne
      (gammaLnBits (expOf (addPrecRound (ofAzRatRound (x - (n : AzRat)).abs 64 .Ceiling).1
        (ofAzNat (AzNat.ofNat n)) 64 .Ceiling).1))) (fun w hw neg b hcw => ?_) p mode).congr
      fun fuel => ?_
    · have := recipPochCoreOf_spec (fun V _ => lnGammaRatEncl_isEncl (x - (n : AzRat)) V)
        (pochRatSplit_le _ n) hw hcw
      rwa [coe_toRat_sub_natCast] at this
    · show genPochRatNegIntFuel fuel x n p mode = _
      unfold genPochRatNegIntFuel
      rw [ite_eq_right hpole, dite_eq_right (NeZero.ne p), ite_eq_right hc, dite_eq_right hs]
      rfl

open Classical in
/-- **The generalized Pochhammer symbol of two rationals is exact or a convergent loop.** -/
theorem genPochhammerRatPrecRoundFuel_zivCases (x y : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ZivCases (fun fuel => genPochhammerRatPrecRoundFuel fuel x y p mode)
      (Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ) ((AzRat.toRat y : ℚ) : ℝ)) p mode := by
  by_cases hd : y.den = 1
  · by_cases hs : y.sign = true ∨ y.num = 0
    · have hyv : ((AzRat.toRat y : ℚ) : ℝ) = (y.num.toNat : ℝ) := by
        rcases hs with hs | h0
        · exact toRat_eq_of_int_den_one y hs hd
        · rw [coe_toRat_eq_zero_of_num_eq_zero y h0, h0, AzNat.toNat_zero, Nat.cast_zero]
      have hv : Spec.pochhammer y.num.toNat (((AzRat.toRat x : ℚ) : ℝ) : EReal)
          = some ((∏ j ∈ range y.num.toNat, (((AzRat.toRat x : ℚ) : ℝ) + j) : ℝ) : EReal) := by
        by_cases hn : y.num.toNat = 0
        · rw [hn, Spec.pochhammer_zero]
          simp
        · exact Spec.pochhammer_coe hn _
      rw [hyv, Spec.genPochhammerReal_nat, ← hv]
      refine (pochhammerRatPrecRoundFuel_zivCases x y.num.toNat p mode).congr fun fuel => ?_
      show genPochhammerRatPrecRoundFuel fuel x y p mode = _
      unfold genPochhammerRatPrecRoundFuel
      rw [ite_eq_left hd, ite_eq_left hs]
    · have hs' := hs
      push Not at hs'
      obtain ⟨hsf, h0⟩ := hs'
      have hsf' : y.sign = false := by simpa using hsf
      have hn : y.num.toNat ≠ 0 := fun h =>
        h0 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
      have hyv : ((AzRat.toRat y : ℚ) : ℝ) = -(y.num.toNat : ℝ) := by
        rw [coe_toRat_eq_mkNorm_of_den_one y hd, AzNat.toInt_mkNorm, hsf']
        simp
      rw [hyv]
      refine (genPochRatNegIntFuel_zivCases x hn p mode).congr fun fuel => ?_
      show genPochhammerRatPrecRoundFuel fuel x y p mode = _
      unfold genPochhammerRatPrecRoundFuel
      rw [ite_eq_left hd, ite_eq_right hs]
  have hni : ¬ ∃ k : ℤ, ((AzRat.toRat y : ℚ) : ℝ) = k := not_exists_int_of_den_ne_one y hd
  have hsum : ((AzRat.toRat (x + y) : ℚ) : ℝ)
      = ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) := by
    rw [AzRat.toRat_add]; push_cast; rfl
  have hspec : Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ) ((AzRat.toRat y : ℚ) : ℝ) =
      if ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) ≤ 0
          ∧ ∃ k : ℤ, ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) = k then none
      else some ((Real.Gamma (((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ))
        / Real.Gamma ((AzRat.toRat x : ℚ) : ℝ) : ℝ) : EReal) := by
    unfold Spec.genPochhammerReal
    rw [ite_eq_right hni]
  rw [hspec]
  by_cases hxp : x.den = 1 ∧ (x.num = 0 ∨ x.sign = false)
  · refine Or.inl fun fuel => ?_
    show genPochhammerRatPrecRoundFuel fuel x y p mode = _
    unfold genPochhammerRatPrecRoundFuel
    rw [ite_eq_right hd, ite_eq_left hxp]
    obtain ⟨hle, k, hk⟩ := (nonpos_int_iff x).mp hxp
    have hns : ¬ (((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) ≤ 0
        ∧ ∃ k : ℤ, ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) = k) := by
      rintro ⟨-, j, hj⟩
      exact hni ⟨j - k, by push_cast; linarith⟩
    rw [ite_eq_right hns, gamma_eq_zero_of_nonpos_int hle hk, div_zero, EReal.coe_zero,
      roundVal_zero]
  by_cases hs : (x + y).den = 1 ∧ ((x + y).num = 0 ∨ (x + y).sign = false)
  · refine Or.inl fun fuel => ?_
    show genPochhammerRatPrecRoundFuel fuel x y p mode = _
    unfold genPochhammerRatPrecRoundFuel
    have := (nonpos_int_iff (x + y)).mp hs
    rw [hsum] at this
    rw [ite_eq_right hd, ite_eq_right hxp, ite_eq_left hs, ite_eq_left this, roundVal_none]
  have hns : ¬ (((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) ≤ 0
      ∧ ∃ k : ℤ, ((AzRat.toRat x : ℚ) : ℝ) + ((AzRat.toRat y : ℚ) : ℝ) = k) := by
    intro h
    rw [← hsum] at h
    exact hs ((nonpos_int_iff (x + y)).mpr h)
  rw [ite_eq_right hns]
  have hxa : ¬ (((AzRat.toRat x : ℚ) : ℝ) ≤ 0 ∧ ∃ k : ℤ, ((AzRat.toRat x : ℚ) : ℝ) = k) :=
    fun h => hxp ((nonpos_int_iff x).mpr h)
  have hconv := gammaQuotEnclOf_coreConv (argConv_rat x (beta_sum_cases hxa))
    (argConv_rat (x + y) (beta_sum_cases (by rw [hsum]; exact hns)))
    (ex := gammaRatExp x) (es := gammaRatExp (x + y))
    (fun W σ k E _ hF => gammaRatFrac_spec x hF)
    (fun W σ k E _ hF => gammaRatFrac_spec (x + y) hF)
  rw [hsum] at hconv
  refine (ZivCases.of_core hconv (fun w hw neg b hc => ?_) p mode).congr fun fuel => ?_
  · have := gammaQuotEnclOf_spec (fun V _ => lnGammaRatEncl_isEncl x V)
      (fun V _ => lnGammaRatEncl_isEncl (x + y) V)
      (fun W σ k E _ hF => gammaRatFrac_spec x hF)
      (fun W σ k E _ hF => gammaRatFrac_spec (x + y) hF) hw hc
    rwa [hsum] at this
  · show genPochhammerRatPrecRoundFuel fuel x y p mode = _
    unfold genPochhammerRatPrecRoundFuel
    rw [ite_eq_right hd, ite_eq_right hxp, ite_eq_right hs, ite_eq_right (NeZero.ne p)]
    rfl

/-- The specification without the non-dyadic values. -/
theorem genPochhammerRatPrecRoundFuel_zivSpec_base :
    ZivSpec (fun xy : AzRat × AzRat =>
        Spec.genPochhammerReal ((AzRat.toRat xy.1 : ℚ) : ℝ) ((AzRat.toRat xy.2 : ℚ) : ℝ))
      (fun fuel xy p mode => genPochhammerRatPrecRoundFuel fuel xy.1 xy.2 p mode)
      {xy | ∀ v : ℝ, Spec.genPochhammerReal ((AzRat.toRat xy.1 : ℚ) : ℝ)
        ((AzRat.toRat xy.2 : ℚ) : ℝ) = some (v : EReal) → v = 0} ∅ :=
  ZivSpec.of_zivCases fun xy p _ mode =>
    genPochhammerRatPrecRoundFuel_zivCases xy.1 xy.2 p mode

/-- The arguments at which `Γ(x + y)/Γ(x)` is known not to be dyadic: an integer `y ≠ 0` and
an `x` whose denominator is not a power of two — with `y ≤ −4` when `y` is negative. -/
def genPochRatSpecial (x y : AzRat) : Prop :=
  y.den = 1 ∧ y.num ≠ 0 ∧
    ((y.sign = true ∧ pochRatSpecial x = true) ∨
      (y.sign = false ∧ recipPochRatSpecial x y.num.toNat = true))

/-- **The value at the arguments of `genPochRatSpecial` is not dyadic, and the function is
correct there at every fuel.** -/
theorem genPochhammerRat_of_special {x y : AzRat} (h : genPochRatSpecial x y) :
    (∃ v : ℝ, Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ) ((AzRat.toRat y : ℚ) : ℝ)
        = some (v : EReal) ∧ ¬ IsDyadic v) ∧
      ∀ (fuel : ℕ) (p : ℕ) [NeZero p] (mode : RoundingMode),
        genPochhammerRatPrecRoundFuel fuel x y p mode
          = roundVal p mode (Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ)
            ((AzRat.toRat y : ℚ) : ℝ)) := by
  obtain ⟨hd, h0, hcase⟩ := h
  have hn : y.num.toNat ≠ 0 := fun h' =>
    h0 (AzNat.toNat_injective (by rw [h', AzNat.toNat_zero]))
  rcases hcase with ⟨hs, hc⟩ | ⟨hs, hc⟩
  · have hyv : ((AzRat.toRat y : ℚ) : ℝ) = (y.num.toNat : ℝ) := toRat_eq_of_int_den_one y hs hd
    rw [hyv, Spec.genPochhammerReal_nat]
    refine ⟨⟨_, rfl, not_isDyadic_pochRat hc hn⟩, fun fuel p _ mode => ?_⟩
    have := pochhammerRatPrecRoundFuel_eq_of_special fuel y.num.toNat hc p mode
    rw [Spec.pochhammer_coe hn] at this
    rw [← this]
    unfold genPochhammerRatPrecRoundFuel
    rw [ite_eq_left hd, ite_eq_left (Or.inl hs)]
  · have hyv : ((AzRat.toRat y : ℚ) : ℝ) = -(y.num.toNat : ℝ) := by
      rw [coe_toRat_eq_mkNorm_of_den_one y hd, AzNat.toInt_mkNorm, hs]
      simp
    have hnd := not_isDyadic_recipPochRat hc
    have hne : ∏ j ∈ range y.num.toNat, (((AzRat.toRat x : ℚ) : ℝ) - y.num.toNat + j) ≠ 0 :=
      fun h' => hnd (by
      rw [h', inv_zero]
      exact isDyadic_zero)
    rw [hyv]
    refine ⟨⟨_, by rw [Spec.genPochhammerReal_neg_nat _ hn, ite_eq_right hne], hnd⟩,
      fun fuel p _ mode => ?_⟩
    rw [← genPochRatNegIntFuel_eq_of_special fuel hn hc p mode]
    unfold genPochhammerRatPrecRoundFuel
    have hns : ¬ (y.sign = true ∨ y.num = 0) := by
      rintro (h' | h')
      · rw [hs] at h'
        cases h'
      · exact h0 h'
    rw [ite_eq_left hd, ite_eq_right hns]

/-- **The specification of the generalized Pochhammer symbol of two rationals** (`ZivSpec`):
sound at every fuel; complete in the limit of the fuel wherever the value is no rounding
boundary; correct at every fuel where the value is undefined (a pole) or `0`, and at the
arguments of `genPochRatSpecial`, where it is a fraction that is not dyadic. -/
theorem genPochhammerRatPrecRoundFuel_zivSpec :
    ZivSpec (fun xy : AzRat × AzRat =>
        Spec.genPochhammerReal ((AzRat.toRat xy.1 : ℚ) : ℝ) ((AzRat.toRat xy.2 : ℚ) : ℝ))
      (fun fuel xy p mode => genPochhammerRatPrecRoundFuel fuel xy.1 xy.2 p mode)
      {xy | ∀ v : ℝ, Spec.genPochhammerReal ((AzRat.toRat xy.1 : ℚ) : ℝ)
        ((AzRat.toRat xy.2 : ℚ) : ℝ) = some (v : EReal) → v = 0}
      {xy | genPochRatSpecial xy.1 xy.2} :=
  genPochhammerRatPrecRoundFuel_zivSpec_base.withN
    (fun _ hxy => (genPochhammerRat_of_special hxy).1)
    (fun _ hxy fuel p _ mode => (genPochhammerRat_of_special hxy).2 fuel p mode)

/-- **The generalized Pochhammer symbol of two rationals is correctly rounded, or the fuel ran
out**, at every fuel. -/
theorem genPochhammerRatPrecRoundFuel_eq_or (fuel : ℕ) (x y : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    genPochhammerRatPrecRoundFuel fuel x y p mode
        = roundVal p mode (Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ)
          ((AzRat.toRat y : ℚ) : ℝ)) ∨
      genPochhammerRatPrecRoundFuel fuel x y p mode = (nan, .eq) :=
  (genPochhammerRatPrecRoundFuel_zivCases x y p mode).sound fuel

/-- **The generalized Pochhammer symbol of two rationals is correctly rounded, or the fuel ran
out.** -/
theorem genPochhammerRatPrecRound_eq_or (x y : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    genPochhammerRatPrecRound x y p mode
        = roundVal p mode (Spec.genPochhammerReal ((AzRat.toRat x : ℚ) : ℝ)
          ((AzRat.toRat y : ℚ) : ℝ)) ∨
      genPochhammerRatPrecRound x y p mode = (nan, .eq) :=
  genPochhammerRatPrecRoundFuel_eq_or (gammaFuel p) x y p mode

end Azurite.AzFloat
