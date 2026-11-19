/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaRat
import Azurite.AzFloat.Equiv.Beta
import Azurite.AzFloat.Equiv.GammaRat
import Azurite.AzFloat.Equiv.PowRat

/-!
# Equivalence: the Beta function of two rationals

`betaRatPrecRound_eq_or`: `betaRatPrecRound a b p mode` is the correct rounding of
`Spec.beta a b` (`Equiv/Beta.lean`), or `(nan, .eq)` when the fuel of the Ziv loop runs out.
The steps: `lnGammaRatEncl_isEncl`, `gammaRatFrac_spec`, `betaRatPole_iff`,
`sum_nonpos_int_iff`, `betaRatSmallInt?_eq`.
-/

namespace Azurite.AzFloat

open Real

/-- The roundings of a rational enclose it. -/
theorem lnGammaRatEncl_isEncl (q : AzRat) (w : ℕ) :
    IsEncl (lnGammaRatEncl q w) ((AzRat.toRat q : ℚ) : ℝ) := by
  have : NeZero (w + 32) := ⟨by omega⟩
  obtain ⟨l, hl, hl1, -⟩ := ofAzRatRound_floor_abs q (w + 32)
  obtain ⟨h, hh, hh1, -⟩ := ofAzRatRound_ceiling_abs q (w + 32)
  exact ⟨l, h, hl, hh, hl1, hh1⟩

/-- `gammaRatFrac` answers with the sign of `q − k` and a positive enclosure of `|q − k|`. -/
theorem gammaRatFrac_spec (q : AzRat) {W : ℕ} {σ : Bool} {k : AzInt} {A : Encl}
    (h : gammaRatFrac q W = some (σ, k, A)) :
    IsEnclPos A ((if σ then -1 else 1) * (((AzRat.toRat q : ℚ) : ℝ) - k.toInt)) := by
  unfold gammaRatFrac at h
  dsimp only at h
  generalize (q.round .Nearest).1 = k' at h
  have hdv : ((AzRat.toRat (q - k'.toAzRat) : ℚ) : ℝ)
      = ((AzRat.toRat q : ℚ) : ℝ) - k'.toInt := by
    rw [AzRat.toRat_sub, AzRat.toRat_toAzRat_int]
    push_cast
    rfl
  split_ifs at h with h0 hs
  · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have := lnGammaRatEncl_spec _ ((toRat_sign_iff _ h0).mp hs) W
    rw [hdv] at this
    simpa [hs] using this
  · have hs' : (q - k'.toAzRat).sign = false := by simpa using hs
    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hneg := toRat_neg_of_sign_false _ h0 hs'
    have hv : ((AzRat.toRat (-(q - k'.toAzRat)) : ℚ) : ℝ)
        = -(((AzRat.toRat q : ℚ) : ℝ) - k'.toInt) := by
      rw [AzRat.toRat_neg, Rat.cast_neg, hdv]
    have := lnGammaRatEncl_spec (-(q - k'.toAzRat)) (by rw [hv]; rw [hdv] at hneg; linarith) W
    rw [hv] at this
    simpa [hs'] using this

/-- `betaRatPole` decides whether a rational is a negative integer. -/
theorem betaRatPole_iff (q : AzRat) :
    betaRatPole q = true ↔
      ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = k := by
  unfold betaRatPole
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Bool.not_eq_true']
  by_cases h0 : q.num = 0
  · have hz := coe_toRat_eq_zero_of_num_eq_zero q h0
    constructor
    · rintro ⟨⟨hne, -⟩, -⟩; exact absurd h0 hne
    · rintro ⟨hlt, -⟩; rw [hz] at hlt; exact absurd hlt (lt_irrefl _)
  · constructor
    · rintro ⟨⟨-, hd⟩, hs⟩
      exact gammaRat_pole h0 ⟨hd, hs⟩
    · intro h
      by_contra hcon
      exact gammaRat_not_pole h0 (fun hp => hcon ⟨⟨h0, hp.1⟩, hp.2⟩) h

/-- A rational is a non-positive integer exactly when its denominator is `1` and it is `0` or
negative. -/
theorem nonpos_int_iff (s : AzRat) :
    (s.den = 1 ∧ (s.num = 0 ∨ s.sign = false)) ↔
      ((AzRat.toRat s : ℚ) : ℝ) ≤ 0 ∧ ∃ k : ℤ, ((AzRat.toRat s : ℚ) : ℝ) = k := by
  constructor
  · rintro ⟨hd, h⟩
    refine ⟨?_, _, coe_toRat_eq_mkNorm_of_den_one s hd⟩
    rcases h with h0 | hs
    · rw [coe_toRat_eq_zero_of_num_eq_zero s h0]
    · by_cases h0 : s.num = 0
      · rw [coe_toRat_eq_zero_of_num_eq_zero s h0]
      · exact (toRat_neg_of_sign_false s h0 hs).le
  · rintro ⟨hle, hk⟩
    have hd : s.den = 1 := by
      by_contra hd
      exact not_exists_int_of_den_ne_one s hd hk
    refine ⟨hd, ?_⟩
    by_cases h0 : s.num = 0
    · exact Or.inl h0
    · right
      by_contra hs
      have := (toRat_sign_iff s h0).mp (by simpa using hs)
      linarith

/-- **The exact path answers with the rounding of `B(a, b)`.** -/
theorem betaRatSmallInt?_eq {a b : AzRat} (ha0 : a.num ≠ 0) (hnp : betaRatPole a ≠ true)
    (p : ℕ) [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : betaRatSmallInt? a b p mode = some r) :
    r = roundVal p mode (some ((Real.Gamma ((AzRat.toRat a : ℚ) : ℝ)
      * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
      / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ)) : ℝ) : EReal)) := by
  unfold betaRatSmallInt? at h
  split_ifs at h with hc
  obtain ⟨hd, hs, hb0, -, -⟩ := hc
  rw [Option.some.injEq] at h
  subst h
  have hbv : ((AzRat.toRat b : ℚ) : ℝ) = (b.num.toNat : ℕ) := by
    rw [coe_toRat_eq_mkNorm_of_den_one b hd, AzNat.toInt_mkNorm, hs]
    simp
  have hn1 : 1 ≤ b.num.toNat :=
    Nat.one_le_iff_ne_zero.mpr fun h0 =>
      hb0 (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero]))
  have hden : (0 : ℝ) < a.den.toNat := den_pos_real a
  have hN : ((AzInt.mkNorm a.sign a.num).toInt : ℝ) / ((a.den.toAzInt).toInt : ℝ)
      = ((AzRat.toRat a : ℚ) : ℝ) := by
    rw [coe_toRat_eq_sign_mul, AzNat.toInt_mkNorm, AzRat.toInt_toAzInt']
    cases a.sign <;> simp [neg_div]
  have hx0 : ((AzRat.toRat a : ℚ) : ℝ) ≠ 0 := fun h' =>
    ha0 ((AzRat.toRat_eq_zero_iff a).mp (by exact_mod_cast h'))
  rw [hbv]
  exact betaIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast hden) hN
    (ne_neg_nat_of_not_pole hx0 (fun hp => hnp ((betaRatPole_iff a).mpr hp))) hn1 p mode

/-- **`B` of two rationals is correctly rounded, or the fuel ran out.** -/
theorem betaRatPrecRound_eq_or (a b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    betaRatPrecRound a b p mode = roundVal p mode (Spec.beta
        (((AzRat.toRat a : ℚ) : ℝ) : EReal) (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      betaRatPrecRound a b p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  set av := ((AzRat.toRat a : ℚ) : ℝ) with hav
  set bv := ((AzRat.toRat b : ℚ) : ℝ) with hbv
  unfold betaRatPrecRound
  by_cases hpole : (betaRatPole a || betaRatPole b) = true
  · left
    rw [ite_eq_left hpole]
    rw [Bool.or_eq_true, betaRatPole_iff, betaRatPole_iff] at hpole
    rw [Spec.beta_coe_of_pole hpole, roundVal_none]
  rw [ite_eq_right hpole]
  have hpa : betaRatPole a ≠ true := fun h => hpole (by rw [h, Bool.true_or])
  have hpb : betaRatPole b ≠ true := fun h => hpole (by rw [h, Bool.or_true])
  rw [Bool.or_eq_true, betaRatPole_iff, betaRatPole_iff] at hpole
  have hz : ∀ q : AzRat, q.num = 0 ↔ ((AzRat.toRat q : ℚ) : ℝ) = 0 := fun q =>
    ⟨coe_toRat_eq_zero_of_num_eq_zero q, fun h =>
      (AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h)⟩
  by_cases hzero : a.num = 0 ∨ b.num = 0
  · left
    rw [ite_eq_left hzero]
    rw [hz a, hz b] at hzero
    rw [Spec.beta_coe_of_zero hpole hzero, roundVal_top]
  rw [ite_eq_right hzero, ite_eq_right hp]
  have ha0 : a.num ≠ 0 := fun h => hzero (Or.inl h)
  have hb0 : b.num ≠ 0 := fun h => hzero (Or.inr h)
  rw [hz a, hz b] at hzero
  rw [Spec.beta_coe hpole hzero]
  split
  · next r hr => left; exact betaRatSmallInt?_eq ha0 hpa p mode hr
  split
  · next r hr =>
    left
    have := betaRatSmallInt?_eq hb0 hpb p mode hr
    rw [this, mul_comm (Real.Gamma _), add_comm]
  have hsum : ((AzRat.toRat (a + b) : ℚ) : ℝ) = av + bv := by
    rw [AzRat.toRat_add]; push_cast; rfl
  by_cases hs : (a + b).den = 1 ∧ ((a + b).num = 0 ∨ (a + b).sign = false)
  · left
    rw [ite_eq_left hs]
    obtain ⟨hle, k, hk⟩ := (nonpos_int_iff (a + b)).mp hs
    rw [hsum] at hle hk
    rw [gamma_eq_zero_of_nonpos_int hle hk, div_zero, EReal.coe_zero, roundVal_zero]
  rw [ite_eq_right hs]
  rcases eq_or_ne (zivLoop (betaRatApprox a b (a + b)) p mode (gammaFuel p) (max 64 (p + 32)))
    (nan, .eq) with hzv | hzv
  · right; exact hzv
  · left
    refine zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => gammaApproxOf_valid_or_none (fun _ _ hc => ?_) w p mode)
      _ _ (le_max_left _ _) hzv
    have := betaEnclOf_spec (fun V _ => lnGammaRatEncl_isEncl a V)
      (fun V _ => lnGammaRatEncl_isEncl b V) (fun V _ => lnGammaRatEncl_isEncl (a + b) V)
      (fun W σ k E _ hF => gammaRatFrac_spec a hF) (fun W σ k E _ hF => gammaRatFrac_spec b hF)
      (fun W σ k E _ hF => gammaRatFrac_spec (a + b) hF) hw hc
    rwa [hsum] at this

end Azurite.AzFloat
