/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaRat
import Azurite.AzFloat.Equiv.Beta
import Azurite.AzFloat.Equiv.BetaRatCertificate
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

/-- The bracket of `B(a, b)` for rationals is valid, or rejected. -/
theorem betaRatApprox_valid_or_none (a b : AzRat) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (betaRatApprox a b (a + b) w).1 lv ∧
        Rounds (betaRatApprox a b (a + b) w).2 hv ∧
        lv ≤ Real.Gamma ((AzRat.toRat a : ℚ) : ℝ) * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
          / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ)) ∧
        Real.Gamma ((AzRat.toRat a : ℚ) : ℝ) * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
          / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ)) ≤ hv ∧
        (lv = Real.Gamma ((AzRat.toRat a : ℚ) : ℝ) * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
            / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ)) →
          hv = Real.Gamma ((AzRat.toRat a : ℚ) : ℝ) * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
            / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ)))) ∨
      roundingPossible (betaRatApprox a b (a + b) w).1 (betaRatApprox a b (a + b) w).2 p mode
        = none := by
  have hsum : ((AzRat.toRat (a + b) : ℚ) : ℝ)
      = ((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) := by
    rw [AzRat.toRat_add]; push_cast; rfl
  refine gammaApproxOf_valid_or_none (fun _ _ hc => ?_) w p mode
  have := betaEnclOf_spec (fun V _ => lnGammaRatEncl_isEncl a V)
    (fun V _ => lnGammaRatEncl_isEncl b V) (fun V _ => lnGammaRatEncl_isEncl (a + b) V)
    (fun W σ k E _ hF => gammaRatFrac_spec a hF) (fun W σ k E _ hF => gammaRatFrac_spec b hF)
    (fun W σ k E _ hF => gammaRatFrac_spec (a + b) hF) hw hc
  rwa [hsum] at this

/-- **`B` of two rationals is correctly rounded, or it is the loop with fuel** in the general
case. -/
theorem betaRatPrecRoundFuel_eq_or_loop (fuel : ℕ) (a b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    betaRatPrecRoundFuel fuel a b p mode = roundVal p mode (Spec.beta
        (((AzRat.toRat a : ℚ) : ℝ) : EReal) (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      (¬ ((((AzRat.toRat a : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat a : ℚ) : ℝ) = k) ∨
          (((AzRat.toRat b : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat b : ℚ) : ℝ) = k)) ∧
        ((AzRat.toRat a : ℚ) : ℝ) ≠ 0 ∧ ((AzRat.toRat b : ℚ) : ℝ) ≠ 0 ∧
        ¬ (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) ≤ 0 ∧
          ∃ k : ℤ, ((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) = k) ∧
        betaRatSpecial a b (a + b) = false ∧
        betaRatPrecRoundFuel fuel a b p mode
          = zivLoop (betaRatApprox a b (a + b)) p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  set av := ((AzRat.toRat a : ℚ) : ℝ) with hav
  set bv := ((AzRat.toRat b : ℚ) : ℝ) with hbv
  unfold betaRatPrecRoundFuel
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
  rw [ite_eq_right hzero, dite_eq_right hp]
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
    rw [dite_eq_left hs]
    obtain ⟨hle, k, hk⟩ := (nonpos_int_iff (a + b)).mp hs
    rw [hsum] at hle hk
    rw [gamma_eq_zero_of_nonpos_int hle hk, div_zero, EReal.coe_zero, roundVal_zero]
  rw [dite_eq_right hs]
  by_cases hc : betaRatSpecial a b (a + b) = true
  · left
    rw [dite_eq_left hc]
    exact zivLoopBacked_eq p mode (betaRatApprox a b (a + b))
      (not_mem_floatSet_of_irrational p (irrational_beta_of_ratSpecial hc hs)) 64
      (fun w hw => (betaRatApprox_valid_or_none a b hw p mode).imp_left
        fun ⟨lv, hv, h1, h2, h3, h4, _⟩ => ⟨lv, hv, h1, h2, h3, h4⟩)
      fuel _ (le_max_left _ _) (by omega) _
  · right
    rw [dite_eq_right hc]
    push Not at hzero
    refine ⟨hpole, hzero.1, hzero.2, fun h => hs ((nonpos_int_iff (a + b)).mpr ?_),
      by simpa using hc, rfl⟩
    rw [hsum]
    exact h

/-- **`B` of two rationals is correctly rounded, or the fuel ran out**, at every fuel. -/
theorem betaRatPrecRoundFuel_eq_or (fuel : ℕ) (a b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    betaRatPrecRoundFuel fuel a b p mode = roundVal p mode (Spec.beta
        (((AzRat.toRat a : ℚ) : ℝ) : EReal) (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      betaRatPrecRoundFuel fuel a b p mode = (nan, .eq) := by
  rcases betaRatPrecRoundFuel_eq_or_loop fuel a b p mode with h | ⟨hpole, ha0, hb0, -, -, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (betaRatPrecRoundFuel fuel a b p mode) (nan, .eq) with hz | hz
    · exact Or.inr hz
    · left
      rw [h] at hz ⊢
      rw [Spec.beta_coe hpole (by push Not; exact ⟨ha0, hb0⟩)]
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => betaRatApprox_valid_or_none a b hw p mode) _ _ (le_max_left _ _) hz

/-- **`B` of two rationals is correctly rounded, or the fuel ran out.** -/
theorem betaRatPrecRound_eq_or (a b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    betaRatPrecRound a b p mode = roundVal p mode (Spec.beta
        (((AzRat.toRat a : ℚ) : ℝ) : EReal) (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      betaRatPrecRound a b p mode = (nan, .eq) :=
  betaRatPrecRoundFuel_eq_or (gammaFuel p) a b p mode

/-- The completeness of `betaRatPrecRoundFuel` in the general case. -/
theorem betaRat_complete_aux (ab : AzRat × AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hB : ∀ v : ℝ, Spec.beta (((AzRat.toRat ab.1 : ℚ) : ℝ) : EReal)
        (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal) = some (v : EReal) →
      ((v : ℝ) : EReal) ∉ floatSet (p + 1))
    (hgen : ¬ ((((AzRat.toRat ab.1 : ℚ) : ℝ) < 0 ∧
          ∃ k : ℤ, ((AzRat.toRat ab.1 : ℚ) : ℝ) = k) ∨
        (((AzRat.toRat ab.2 : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat ab.2 : ℚ) : ℝ) = k)) ∧
        ((AzRat.toRat ab.1 : ℚ) : ℝ) ≠ 0 ∧ ((AzRat.toRat ab.2 : ℚ) : ℝ) ≠ 0 ∧
        ¬ (((AzRat.toRat ab.1 : ℚ) : ℝ) + ((AzRat.toRat ab.2 : ℚ) : ℝ) ≤ 0 ∧
          ∃ k : ℤ, ((AzRat.toRat ab.1 : ℚ) : ℝ) + ((AzRat.toRat ab.2 : ℚ) : ℝ) = k)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → betaRatPrecRoundFuel fuel ab.1 ab.2 p mode
      = roundVal p mode (Spec.beta (((AzRat.toRat ab.1 : ℚ) : ℝ) : EReal)
        (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal)) := by
  obtain ⟨hpole, ha0, hb0, hs⟩ := hgen
  have hval := Spec.beta_coe hpole (by push Not; exact ⟨ha0, hb0⟩)
  have hB' := hB _ hval
  obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (betaRatApprox ab.1 ab.2 (ab.1 + ab.2))
    (betaRatApprox_bracketConv ab.1 ab.2 (beta_arg_cases ha0 fun h => hpole (Or.inl h))
      (beta_arg_cases hb0 fun h => hpole (Or.inr h)) (beta_sum_cases hs))
    (ne_zero_of_not_mem_floatSet hB') hB' (max 64 (p + 32)) (by omega)
    (fun w hw =>
      (betaRatApprox_valid_or_none ab.1 ab.2 (le_trans (le_max_left _ _) hw) p mode).imp_left
        fun ⟨lv, hv, h1, h2, h3, h4, _⟩ => ⟨lv, hv, h1, h2, h3, h4⟩)
  refine ⟨F, fun fuel hfuel => ?_⟩
  rcases betaRatPrecRoundFuel_eq_or_loop fuel ab.1 ab.2 p mode with h | ⟨-, -, -, -, -, h⟩
  · exact h
  · rw [h, hval]
    exact hF fuel hfuel

/-- **The specification of `B` for rationals** (`ZivSpec`): sound at every fuel; complete in
the limit of the fuel wherever the value is no rounding boundary; and correct at every fuel
on the special values (`NaN`, `+∞`, the zeros) and on the arguments recognized by
`betaRatSpecial`, where the value is irrational: `a + b` a positive integer, or the
denominators of `a` and `b` both in `{2, 4}` or both in `{2, 3, 6}`. -/
theorem betaRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun ab : AzRat × AzRat => Spec.beta (((AzRat.toRat ab.1 : ℚ) : ℝ) : EReal)
        (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal))
      (fun fuel ab p mode => betaRatPrecRoundFuel fuel ab.1 ab.2 p mode)
      {ab | (((AzRat.toRat ab.1 : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat ab.1 : ℚ) : ℝ) = k) ∨
        (((AzRat.toRat ab.2 : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat ab.2 : ℚ) : ℝ) = k) ∨
        ((AzRat.toRat ab.1 : ℚ) : ℝ) = 0 ∨ ((AzRat.toRat ab.2 : ℚ) : ℝ) = 0 ∨
        (((AzRat.toRat ab.1 : ℚ) : ℝ) + ((AzRat.toRat ab.2 : ℚ) : ℝ) ≤ 0 ∧
          ∃ k : ℤ, ((AzRat.toRat ab.1 : ℚ) : ℝ) + ((AzRat.toRat ab.2 : ℚ) : ℝ) = k)}
      {ab | betaRatSpecial ab.1 ab.2 (ab.1 + ab.2) = true ∧
        ¬ ((ab.1 + ab.2).den = 1 ∧ ((ab.1 + ab.2).num = 0 ∨ (ab.1 + ab.2).sign = false))} where
  sound := fun fuel ab p _ mode => betaRatPrecRoundFuel_eq_or fuel ab.1 ab.2 p mode
  complete := fun ab p _ mode hB => by
    by_cases hgen : ¬ ((((AzRat.toRat ab.1 : ℚ) : ℝ) < 0 ∧
          ∃ k : ℤ, ((AzRat.toRat ab.1 : ℚ) : ℝ) = k) ∨
        (((AzRat.toRat ab.2 : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat ab.2 : ℚ) : ℝ) = k)) ∧
        ((AzRat.toRat ab.1 : ℚ) : ℝ) ≠ 0 ∧ ((AzRat.toRat ab.2 : ℚ) : ℝ) ≠ 0 ∧
        ¬ (((AzRat.toRat ab.1 : ℚ) : ℝ) + ((AzRat.toRat ab.2 : ℚ) : ℝ) ≤ 0 ∧
          ∃ k : ℤ, ((AzRat.toRat ab.1 : ℚ) : ℝ) + ((AzRat.toRat ab.2 : ℚ) : ℝ) = k)
    · exact betaRat_complete_aux ab p mode hB hgen
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases betaRatPrecRoundFuel_eq_or_loop fuel ab.1 ab.2 p mode with
        h' | ⟨h1, h2, h3, h4, -, -⟩
      · exact h'
      · exact absurd ⟨h1, h2, h3, h4⟩ hgen
  dyadic := fun ab hab v hv => by
    rcases Spec.beta_eq_coe_cases hv with rfl | ⟨av, bv, ha, hb, hpole, hzero, rfl⟩
    · exact isDyadic_zero
    · rw [EReal.coe_eq_coe_iff] at ha hb
      rw [← ha, ← hb] at hpole hzero ⊢
      rcases hab with h | h | h | h | ⟨hle, k, hk⟩
      · exact absurd (Or.inl h) hpole
      · exact absurd (Or.inr h) hpole
      · exact absurd (Or.inl h) hzero
      · exact absurd (Or.inr h) hzero
      · rw [gamma_eq_zero_of_nonpos_int hle hk, div_zero]
        exact isDyadic_zero
  nondyadic := fun ab h => by
    obtain ⟨hc, hs⟩ := h
    obtain ⟨hda, hdb, -⟩ := betaRatSpecial_spec hc
    have hirr := irrational_beta_of_ratSpecial hc hs
    have hna := not_exists_int_of_den_ne_one ab.1 hda
    have hnb := not_exists_int_of_den_ne_one ab.2 hdb
    have hpole : ¬ ((((AzRat.toRat ab.1 : ℚ) : ℝ) < 0 ∧
          ∃ k : ℤ, ((AzRat.toRat ab.1 : ℚ) : ℝ) = k) ∨
        (((AzRat.toRat ab.2 : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat ab.2 : ℚ) : ℝ) = k)) := by
      rintro (h | h)
      · exact hna h.2
      · exact hnb h.2
    have hzero : ¬ (((AzRat.toRat ab.1 : ℚ) : ℝ) = 0 ∨ ((AzRat.toRat ab.2 : ℚ) : ℝ) = 0) := by
      rintro (h | h)
      · exact hna ⟨0, by simpa using h⟩
      · exact hnb ⟨0, by simpa using h⟩
    exact ⟨_, Spec.beta_coe hpole hzero, not_isDyadic_of_irrational hirr⟩
  correct := fun ab hab fuel p _ mode => by
    rcases betaRatPrecRoundFuel_eq_or_loop fuel ab.1 ab.2 p mode with
      h | ⟨hpole, ha0, hb0, hs, hc, -⟩
    · exact h
    · exfalso
      rcases hab with hD | hN
      · rcases hD with h | h | h | h | h
        · exact hpole (Or.inl h)
        · exact hpole (Or.inr h)
        · exact ha0 h
        · exact hb0 h
        · exact hs h
      · rw [hN.1] at hc
        exact Bool.noConfusion hc

end Azurite.AzFloat
