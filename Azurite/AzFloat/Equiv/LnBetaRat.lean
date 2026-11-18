/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBetaRat
import Azurite.AzFloat.Equiv.LnBeta
import Azurite.AzFloat.Equiv.BetaRat
import Azurite.AzFloat.Equiv.LnRat

/-!
# Equivalence: `ln B(a, b)` and `ln |B(a, b)|` with the sign of `B(a, b)`, for two rationals

`lnAbsBetaRatPrecRound_main`: off the special values the result is `(nan, .eq)`, or the
rounding of `ln |B(a, b)|` with the sign of `B(a, b)`.  From it:
**`lnAbsBetaRatPrecRound_eq_or`** (against `Spec.lnAbsBeta`, `Equiv/LnBeta.lean`) and
**`lnAbsBetaRatPrecRound_sign`**.
-/

namespace Azurite.AzFloat

open Real

/-- `negLnAbsRat q` is the rounding of `−ln |q|`, `q ≠ 0`. -/
theorem negLnAbsRat_eq (q : AzRat) (h0 : q.num ≠ 0) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    negLnAbsRat q p mode
      = roundVal p mode (some ((-Real.log |((AzRat.toRat q : ℚ) : ℝ)| : ℝ) : EReal)) := by
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  unfold negLnAbsRat
  dsimp only
  have hv : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]; push_cast; rfl
  rw [lnRatPrecRound_eq, hv, Spec.log_coe _ (abs_pos.mpr hx0), roundVal_neg]

/-- **`lnAbsBetaRatPrecRound` off the special values**: `(nan, .eq)`, or the rounding of
`ln |B|` with the sign of `B`. -/
theorem lnAbsBetaRatPrecRound_main (a b : AzRat) (ha0 : a.num ≠ 0) (hb0 : b.num ≠ 0)
    (hpa : betaRatPole a ≠ true) (hpb : betaRatPole b ≠ true)
    (hs : ¬ ((a + b).den = 1 ∧ ((a + b).num = 0 ∨ (a + b).sign = false))) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsBetaRatPrecRound a b p mode).1 = (nan, .eq) ∨
      ((lnAbsBetaRatPrecRound a b p mode).1 = roundVal p mode
          (some ((Real.log |Real.Gamma ((AzRat.toRat a : ℚ) : ℝ)
            * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
            / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ))| : ℝ) : EReal))
        ∧ ((lnAbsBetaRatPrecRound a b p mode).2 = true
          ↔ 0 < Real.Gamma ((AzRat.toRat a : ℚ) : ℝ) * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
            / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ)))) := by
  have hp := NeZero.ne p
  set av := ((AzRat.toRat a : ℚ) : ℝ) with hav
  set bv := ((AzRat.toRat b : ℚ) : ℝ) with hbv
  have hax0 : av ≠ 0 := fun h' => ha0 (by
    rw [hav] at h'
    exact (AzRat.toRat_eq_zero_iff a).mp (by exact_mod_cast h'))
  have hbx0 : bv ≠ 0 := fun h' => hb0 (by
    rw [hbv] at h'
    exact (AzRat.toRat_eq_zero_iff b).mp (by exact_mod_cast h'))
  have hna : ¬ (av < 0 ∧ ∃ k : ℤ, av = k) := fun h => hpa ((betaRatPole_iff a).mpr h)
  have hnb : ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k) := fun h => hpb ((betaRatPole_iff b).mpr h)
  have hsum : ((AzRat.toRat (a + b) : ℚ) : ℝ) = av + bv := by
    rw [AzRat.toRat_add]; push_cast; rfl
  unfold lnAbsBetaRatPrecRound
  have hpole : ¬ (betaRatPole a || betaRatPole b) = true := by
    rw [Bool.or_eq_true]; exact fun h => h.elim hpa hpb
  rw [ite_eq_right hpole, ite_eq_right (fun h => h.elim ha0 hb0), ite_eq_right hs,
    ite_eq_right hp]
  have hone : ∀ q : AzRat, (q.sign = true ∧ q.num = q.den) → ((AzRat.toRat q : ℚ) : ℝ) = 1 :=
    fun q h => by
      have := (coe_toRat_eq_one_iff q).mpr h
      rwa [← EReal.coe_one, EReal.coe_eq_coe_iff] at this
  by_cases hb1 : b.sign = true ∧ b.num = b.den
  · right
    have hb1v : bv = 1 := hone b hb1
    rw [ite_eq_left hb1, hb1v, gamma_mul_gamma_one_div hax0 hna, log_abs_one_div]
    exact ⟨negLnAbsRat_eq a ha0 p mode, by
      show a.sign = true ↔ _
      rw [toRat_sign_iff a ha0, one_div, inv_pos]⟩
  rw [ite_eq_right hb1]
  by_cases ha1 : a.sign = true ∧ a.num = a.den
  · right
    have hv : Real.Gamma 1 * Real.Gamma bv / Real.Gamma (1 + bv) = 1 / bv := by
      rw [mul_comm, add_comm]
      exact gamma_mul_gamma_one_div hbx0 hnb
    have ha1v : av = 1 := hone a ha1
    rw [ite_eq_left ha1, ha1v, hv, log_abs_one_div]
    exact ⟨negLnAbsRat_eq b hb0 p mode, by
      show b.sign = true ↔ _
      rw [toRat_sign_iff b hb0, one_div, inv_pos]⟩
  rw [ite_eq_right ha1]
  refine lnAbsLoop_spec (w₀ := 64) (fun w hw neg L hc => ?_) p mode _ _ (le_max_left _ _)
  have := lnAbsBetaEncl_spec (fun V _ => lnGammaRatEncl_isEncl a V)
    (fun V _ => lnGammaRatEncl_isEncl b V) (fun V _ => lnGammaRatEncl_isEncl (a + b) V)
    (fun W σ k E _ hF => gammaRatFrac_spec a hF) (fun W σ k E _ hF => gammaRatFrac_spec b hF)
    (fun W σ k E _ hF => gammaRatFrac_spec (a + b) hF) (by omega) hw hc
  rwa [hsum] at this

/-- **`ln |B|` of two rationals is correctly rounded, or the fuel ran out.** -/
theorem lnAbsBetaRatPrecRound_eq_or (a b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsBetaRatPrecRound a b p mode).1 = roundVal p mode (Spec.lnAbsBeta
        (((AzRat.toRat a : ℚ) : ℝ) : EReal) (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      (lnAbsBetaRatPrecRound a b p mode).1 = (nan, .eq) := by
  set av := ((AzRat.toRat a : ℚ) : ℝ) with hav
  set bv := ((AzRat.toRat b : ℚ) : ℝ) with hbv
  unfold Spec.lnAbsBeta
  by_cases hpole : (betaRatPole a || betaRatPole b) = true
  · left
    unfold lnAbsBetaRatPrecRound
    rw [ite_eq_left hpole]
    rw [Bool.or_eq_true, betaRatPole_iff, betaRatPole_iff] at hpole
    rw [Spec.beta_coe_of_pole hpole, Option.map_none, roundVal_none]
  have hpa : betaRatPole a ≠ true := fun h => hpole (by rw [h, Bool.true_or])
  have hpb : betaRatPole b ≠ true := fun h => hpole (by rw [h, Bool.or_true])
  have hpole' := hpole
  rw [Bool.or_eq_true, betaRatPole_iff, betaRatPole_iff] at hpole'
  have hz : ∀ q : AzRat, q.num = 0 ↔ ((AzRat.toRat q : ℚ) : ℝ) = 0 := fun q =>
    ⟨coe_toRat_eq_zero_of_num_eq_zero q, fun h =>
      (AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h)⟩
  by_cases hzero : a.num = 0 ∨ b.num = 0
  · left
    unfold lnAbsBetaRatPrecRound
    rw [ite_eq_right hpole, ite_eq_left hzero]
    rw [hz a, hz b] at hzero
    rw [Spec.beta_coe_of_zero hpole' hzero, Option.map_some, Spec.lnAbsE_top, roundVal_top]
  have ha0 : a.num ≠ 0 := fun h => hzero (Or.inl h)
  have hb0 : b.num ≠ 0 := fun h => hzero (Or.inr h)
  have hzero' := hzero
  rw [hz a, hz b] at hzero'
  rw [Spec.beta_coe hpole' hzero', Option.map_some]
  push Not at hzero'
  have hsum : ((AzRat.toRat (a + b) : ℚ) : ℝ) = av + bv := by
    rw [AzRat.toRat_add]; push_cast; rfl
  by_cases hs : (a + b).den = 1 ∧ ((a + b).num = 0 ∨ (a + b).sign = false)
  · left
    unfold lnAbsBetaRatPrecRound
    rw [ite_eq_right hpole, ite_eq_right hzero, ite_eq_left hs]
    obtain ⟨hle, k, hk⟩ := (nonpos_int_iff (a + b)).mp hs
    rw [hsum] at hle hk
    rw [gamma_eq_zero_of_nonpos_int hle hk, div_zero, Spec.lnAbsE_zero, roundVal_bot]
  · have hs' : ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k) := by
      rw [← hsum]; exact fun h => hs ((nonpos_int_iff (a + b)).mpr h)
    rw [Spec.lnAbsE_coe (beta_ne_zero hzero'.1 hzero'.2 (fun h => hpole' (Or.inl h))
      (fun h => hpole' (Or.inr h)) hs')]
    rcases lnAbsBetaRatPrecRound_main a b ha0 hb0 hpa hpb hs p mode with h | h
    · exact Or.inr h
    · exact Or.inl h.1

/-- **The sign component is the sign of `B(a, b)`** whenever the value is not `NaN`, where `B`
is finite and not `0`. -/
theorem lnAbsBetaRatPrecRound_sign (a b : AzRat) (ha0 : a.num ≠ 0) (hb0 : b.num ≠ 0)
    (hpa : betaRatPole a ≠ true) (hpb : betaRatPole b ≠ true)
    (hs : ¬ ((a + b).den = 1 ∧ ((a + b).num = 0 ∨ (a + b).sign = false))) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (hne : (lnAbsBetaRatPrecRound a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsBetaRatPrecRound a b p mode).2 = true
      ↔ 0 < Real.Gamma ((AzRat.toRat a : ℚ) : ℝ) * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
        / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ)) := by
  rcases lnAbsBetaRatPrecRound_main a b ha0 hb0 hpa hpb hs p mode with h | h
  · exact absurd h hne
  · exact h.2

/-- **`ln B` of two rationals is correctly rounded, or the fuel ran out** (`NaN` where
`B < 0`). -/
theorem lnBetaRatPrecRound_eq_or (a b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnBetaRatPrecRound a b p mode = roundVal p mode (Spec.lnBeta
        (((AzRat.toRat a : ℚ) : ℝ) : EReal) (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      lnBetaRatPrecRound a b p mode = (nan, .eq) := by
  unfold lnBetaRatPrecRound
  dsimp only
  by_cases hs : (lnAbsBetaRatPrecRound a b p mode).2 = true
  · rw [ite_eq_left hs]
    rcases lnAbsBetaRatPrecRound_eq_or a b p mode with h | h
    · by_cases hnan : (lnAbsBetaRatPrecRound a b p mode).1 = (nan, .eq)
      · exact Or.inr hnan
      left
      rw [h]
      congr 1
      refine Spec.lnAbsBeta_eq_lnBeta fun v hv => ?_
      by_contra hneg
      push Not at hneg
      obtain ⟨av, bv, hav, hbv, ha0, hb0, hpa, hpb, hsum, rfl⟩ := Spec.beta_neg_cases hv hneg
      rw [EReal.coe_eq_coe_iff] at hav hbv
      subst hav hbv
      have hz : ∀ q : AzRat, q.num = 0 → ((AzRat.toRat q : ℚ) : ℝ) = 0 :=
        coe_toRat_eq_zero_of_num_eq_zero
      have hsumv : ((AzRat.toRat (a + b) : ℚ) : ℝ)
          = ((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) := by
        rw [AzRat.toRat_add]; push_cast; rfl
      have := (lnAbsBetaRatPrecRound_sign a b (fun h0 => ha0 (hz a h0))
        (fun h0 => hb0 (hz b h0)) (fun hp => hpa ((betaRatPole_iff a).mp hp))
        (fun hp => hpb ((betaRatPole_iff b).mp hp))
        (fun hd => hsum (by rw [← hsumv]; exact (nonpos_int_iff (a + b)).mp hd)) p mode
        hnan).mp hs
      linarith
    · exact Or.inr h
  · rw [ite_eq_right hs]
    exact Or.inr rfl

end Azurite.AzFloat
