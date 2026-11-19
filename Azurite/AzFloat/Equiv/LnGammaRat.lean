/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGammaRat
import Azurite.AzFloat.Equiv.LnGamma
import Azurite.AzFloat.Equiv.AcoshBracket
import Azurite.AzFloat.Equiv.GammaRat
import Azurite.AzNat.Equiv.Parity

/-!
# Equivalence: `ln Γ` of a rational

`lnGammaRatEncl_spec` (the two directed roundings enclose a positive rational, with a positive
lower end), `lnGammaRatBracket_spec`, and `lnGammaRatPrecRound_eq_or`:
`lnGammaRatPrecRound q p mode` is the correctly rounded `Spec.lnGamma q` unless the fuel runs
out (`(nan, .eq)`).
-/

namespace Azurite.AzFloat

/-- **`lnGammaRatBracket q w` encloses `ln Γ(q)`** for a rational `q > 0` (`w ≥ 64`). -/
theorem lnGammaRatBracket_spec (q : AzRat) (hq : 0 < ((AzRat.toRat q : ℚ) : ℝ)) {w : ℕ}
    (hw : 64 ≤ w) :
    IsEncl (lnGammaRatBracket q w) (Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ))) :=
  lnGammaBracketEncl_spec (lnGammaRatEncl_spec q hq w) _ hw

/-- The bracket of `ln Γ(q)` is valid from 64 bits on. -/
theorem lnGammaRatApprox_valid (q : AzRat) (hpos : 0 < ((AzRat.toRat q : ℚ) : ℝ)) {w : ℕ}
    (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (lnGammaRatApprox q w).1 lv ∧ Rounds (lnGammaRatApprox q w).2 hv ∧
      lv ≤ Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)) ∧
      Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)) ≤ hv ∧
      (lv = Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)) →
        hv = Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ))) := by
  obtain ⟨lv, hv', hl, hh, hlo, hhi⟩ :=
    lnGammaApproxOf_spec (lnGammaRatBracket_spec q hpos hw) w
  exact ⟨lv, hv', hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩

/-- **The branches of `lnGammaRatPrecRoundFuel`**: the correctly rounded value, whatever the
fuel, or — at a positive rational that is not an integer — the fuel loop. -/
theorem lnGammaRatPrecRoundFuel_eq_or_loop (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnGammaRatPrecRoundFuel fuel q p mode
        = roundVal p mode (Spec.lnGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (q.den ≠ 1 ∧ 0 < ((AzRat.toRat q : ℚ) : ℝ) ∧
        lnGammaRatPrecRoundFuel fuel q p mode
          = zivLoop (lnGammaRatApprox q) p mode fuel
            (max 64 (p + 32 + lnGammaRatCancelBits q))) := by
  have hp := NeZero.ne p
  unfold lnGammaRatPrecRoundFuel
  by_cases h0 : q.num = 0
  · left
    rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, EReal.coe_zero,
      Spec.lnGamma_zero, roundVal_top]
  rw [dite_eq_right h0]
  by_cases hs : q.sign = false
  · left
    have hneg : ((AzRat.toRat q : ℚ) : ℝ) < 0 := by
      have hne : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
      refine lt_of_le_of_ne (not_lt.mp fun hpos => ?_) hne
      rw [(toRat_sign_iff q h0).mpr hpos] at hs
      exact Bool.noConfusion hs
    rw [dite_eq_left hs, Spec.lnGamma_coe_of_neg hneg, roundVal_none]
  rw [dite_eq_right hs]
  have hs' : q.sign = true := by simpa using hs
  have hpos : 0 < ((AzRat.toRat q : ℚ) : ℝ) := (toRat_sign_iff q h0).mp hs'
  rw [Spec.lnGamma_coe_of_pos hpos]
  by_cases h12 : (q - 1).num = 0 ∨ (q - 1 - 1).num = 0
  · left
    rw [dite_eq_left h12]
    have hval : ((AzRat.toRat q : ℚ) : ℝ) = 1 ∨ ((AzRat.toRat q : ℚ) : ℝ) = 2 := by
      rcases h12 with h | h
      · left
        have := (AzRat.toRat_eq_zero_iff (q - 1)).mpr h
        rw [AzRat.toRat_sub, AzRat.toRat_one] at this
        push_cast at this
        linarith
      · right
        have := (AzRat.toRat_eq_zero_iff (q - 1 - 1)).mpr h
        rw [AzRat.toRat_sub, AzRat.toRat_sub, AzRat.toRat_one] at this
        push_cast at this
        linarith
    have hz : Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)) = 0 := by
      rcases hval with h | h <;> rw [h]
      · rw [Real.Gamma_one, Real.log_one]
      · rw [Real.Gamma_two, Real.log_one]
    rw [hz, EReal.coe_zero, roundVal_zero]
  rw [dite_eq_right h12, dite_eq_right hp]
  by_cases hI : q.den = 1
  · left
    rw [dite_eq_left hI]
    obtain ⟨n, hn, hval⟩ := lnGammaRatInt_spec h0 hs' h12 hI
    have hirr := irrational_log_gamma_nat hn
    rw [← hval] at hirr
    refine zivLoopCertified_eq_or_none p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
      (by omega) (fun w hw => Or.inl ?_) _
    obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
      lnGammaRatApprox_valid q hpos (le_trans (le_max_left _ _) hw)
    exact ⟨lv, hv', hl, hh, hlo, hhi⟩
  · rw [dite_eq_right hI]
    exact Or.inr ⟨hI, hpos, rfl⟩

/-- **`ln Γ` of a rational with explicit fuel is correctly rounded unless the fuel runs
out**, which does not happen at an integer. -/
theorem lnGammaRatPrecRoundFuel_eq_or (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnGammaRatPrecRoundFuel fuel q p mode
        = roundVal p mode (Spec.lnGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (lnGammaRatPrecRoundFuel fuel q p mode = (nan, .eq) ∧ q.den ≠ 1) := by
  rcases lnGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨hI, hpos, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (zivLoop (lnGammaRatApprox q) p mode fuel
      (max 64 (p + 32 + lnGammaRatCancelBits q))) (nan, .eq) with hz | hz
    · exact Or.inr ⟨h.trans hz, hI⟩
    · left
      rw [h, Spec.lnGamma_coe_of_pos hpos]
      exact zivLoop_eq_of_ne_nan_threshold p mode _ _ 64
        (fun w hw => lnGammaRatApprox_valid q hpos hw) _ _ (le_max_left _ _) hz

/-- **`ln Γ` of a rational is correctly rounded unless the fuel runs out.** -/
theorem lnGammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnGammaRatPrecRound q p mode
        = roundVal p mode (Spec.lnGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      lnGammaRatPrecRound q p mode = (nan, .eq) :=
  (lnGammaRatPrecRoundFuel_eq_or (lnGammaFuel p) q p mode).imp_right And.left

/-- **`ln Γ` of an integer rational is correctly rounded, unconditionally.** -/
theorem lnGammaRatPrecRound_eq_of_den_one (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (h : q.den = 1) :
    lnGammaRatPrecRound q p mode
      = roundVal p mode (Spec.lnGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  rcases lnGammaRatPrecRoundFuel_eq_or (lnGammaFuel p) q p mode with h' | ⟨-, h'⟩
  · exact h'
  · exact absurd h h'

/-- The fuel loop of `ln Γ` at a positive rational is correct for every large enough fuel
when the value is no rounding boundary. -/
theorem lnGammaRat_zivLoop_eventually (q : AzRat) (hpos : 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 64 ≤ w₀)
    (hB : ((Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)) : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel →
      zivLoop (lnGammaRatApprox q) p mode fuel w₀
        = roundVal p mode
          (some ((Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)) : ℝ) : EReal)) :=
  zivLoop_eventually_eq p mode _ (lnGammaRatApprox_bracketConv q hpos)
    (ne_zero_of_not_mem_floatSet hB) hB w₀ (by omega) (fun w hw => Or.inl (by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := lnGammaRatApprox_valid q hpos (le_trans hw₀ hw)
      exact ⟨lv, hv', hl, hh, hlo, hhi⟩))

/-- **The specification of `ln Γ` of a rational** (`ZivSpec`): correct at every fuel at the
rationals that are not positive or are `1` or `2` (exact values) and at the integers from `3`
on (`ln (n − 1)!` is irrational). -/
theorem lnGammaRatPrecRoundFuel_zivSpec :
    ZivSpec (fun q : AzRat => Spec.lnGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal))
      lnGammaRatPrecRoundFuel
      {q | ((AzRat.toRat q : ℚ) : ℝ) ≤ 0 ∨ ((AzRat.toRat q : ℚ) : ℝ) = 1 ∨
        ((AzRat.toRat q : ℚ) : ℝ) = 2}
      {q | ∃ n : ℕ, 3 ≤ n ∧ ((AzRat.toRat q : ℚ) : ℝ) = n} where
  sound := fun fuel q p _ mode =>
    (lnGammaRatPrecRoundFuel_eq_or fuel q p mode).imp_right And.left
  complete := fun q p _ mode hB => by
    by_cases hpos : 0 < ((AzRat.toRat q : ℚ) : ℝ)
    · have hval := Spec.lnGamma_coe_of_pos hpos
      obtain ⟨F, hF⟩ := lnGammaRat_zivLoop_eventually q hpos p mode
        (max 64 (p + 32 + lnGammaRatCancelBits q)) (le_max_left _ _) (hB _ hval)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases lnGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨-, -, h⟩
      · exact h
      · rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases lnGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨-, hpos', -⟩
      · exact h
      · exact absurd hpos' hpos
  dyadic := fun q hq v hv =>
    isDyadic_of_lnGamma (fun t ht => by
      have : ((AzRat.toRat q : ℚ) : ℝ) = t := by exact_mod_cast ht
      rw [← this]
      exact hq) hv
  nondyadic := fun q hq => by
    obtain ⟨n, hn, hq⟩ := hq
    refine ⟨_, ?_, not_isDyadic_of_irrational (irrational_log_gamma_nat hn)⟩
    rw [hq, Spec.lnGamma_coe_of_pos (by positivity)]
  correct := fun q hq fuel p _ mode => by
    rcases lnGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨hI, hpos, -⟩
    · exact h
    · exfalso
      have hint := not_exists_int_of_den_ne_one q hI
      rcases hq with (h | h | h) | ⟨n, -, hn⟩
      · exact absurd hpos (not_lt.mpr h)
      · exact hint ⟨1, by rw [h]; simp⟩
      · exact hint ⟨2, by rw [h]; simp⟩
      · exact hint ⟨n, by rw [hn]; simp⟩

/-!
# `ln |Γ(q)|` and the sign of `Γ(q)` for an `AzRat`: correctness

* `lnAbsGammaRatNegEncl_spec`: the reflection formula at a rational.
* `Gamma_pos_iff_floor_odd`: the sign of `Γ` at a negative rational that is not an integer.
* **`lnAbsGammaRatPrecRound_eq_or`**: the value is correctly rounded, or `NaN` (the fuel).
* **`lnAbsGammaRatPrecRound_sign`**: the sign is that of `Γ(q)` away from the poles.
-/

section

open Real

/-- **`lnAbsGammaRatNegEncl` answers with an enclosure of `ln |Γ(q)|`**, `q < 0`. -/
theorem lnAbsGammaRatNegEncl_spec (q : AzRat) (hq0 : ((AzRat.toRat q : ℚ) : ℝ) < 0)
    (e : AzInt) {w : ℕ} (hw : 64 ≤ w) {b : Encl} (h : lnAbsGammaRatNegEncl q e w = some b) :
    IsEncl b (Real.log |Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)|) := by
  unfold lnAbsGammaRatNegEncl at h
  dsimp only at h
  have hv : ((AzRat.toRat (1 - q) : ℚ) : ℝ) = -((AzRat.toRat q : ℚ) : ℝ) + 1 := by
    rw [AzRat.toRat_sub, AzRat.toRat_one]
    push_cast
    ring
  have hX₁ := lnGammaRatEncl_spec (1 - q) (by rw [hv]; linarith) w
  rw [hv] at hX₁
  exact lnAbsGammaReflect_spec hq0 hw
    (fun _ _ hS => gammaRatSinEncl_spec q (W := w + 16) (by omega) hw hS)
    (lnGammaBracketEncl_spec hX₁ ((if e.sign then e else 0) + 1) hw) h

/-- **The sign of `Γ` at a negative rational that is not an integer**: positive exactly when
`⌊|q|⌋` is odd. -/
theorem Gamma_pos_iff_floor_odd (q : AzRat) (h0 : q.num ≠ 0) (hs : q.sign = false)
    (hd : q.den ≠ 1) :
    (q.num / q.den).isOdd = true ↔ 0 < Real.Gamma ((AzRat.toRat q : ℚ) : ℝ) := by
  have hneg := toRat_neg_of_sign_false q h0 hs
  have hni := not_exists_int_of_den_ne_one q hd
  have hdR : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  have habs := abs_coe_toRat q
  rw [abs_of_neg hneg] at habs
  set n := q.num.toNat / q.den.toNat with hn
  have hdm := Nat.div_add_mod q.num.toNat q.den.toNat
  have hmod := Nat.mod_lt q.num.toNat (AzRat.den_toNat_pos q)
  set r := q.num.toNat % q.den.toNat with hr
  have hnum : (q.num.toNat : ℝ) = q.den.toNat * n + r := by exact_mod_cast hdm.symm
  have hval : ((AzRat.toRat q : ℚ) : ℝ) = -((n : ℝ) + r / q.den.toNat) := by
    have : (q.num.toNat : ℝ) / q.den.toNat = (n : ℝ) + r / q.den.toNat := by
      rw [hnum]
      field_simp
    linarith
  have hr0 : (0 : ℝ) < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · refine absurd ⟨-(n : ℤ), ?_⟩ hni
      rw [hval, h]
      push_cast
      ring
    · exact_mod_cast h
  have hrd : (r : ℝ) / q.den.toNat < 1 := by
    rw [div_lt_one hdR]
    exact_mod_cast hmod
  have hrp : (0 : ℝ) < r / q.den.toNat := div_pos hr0 hdR
  rw [AzNat.isOdd_iff, AzNat.toNat_div, ← hn]
  have hodd : Odd n ↔ Odd (-(n : ℤ)) := by
    rw [odd_neg]
    exact (Int.odd_coe_nat n).symm
  rw [hodd]
  exact Gamma_pos_iff_odd hneg (k := -(n : ℤ)) (by rw [hval]; push_cast; linarith)
    (by rw [hval]; push_cast; linarith)

/-- **The bracket of `ln |Γ(q)|` converges** at a negative rational that is not an
integer. -/
theorem lnAbsGammaRatApprox_bracketConv (q : AzRat) (hneg : ((AzRat.toRat q : ℚ) : ℝ) < 0)
    (hint : ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k) (e : AzInt) :
    BracketConv (lnAbsGammaRatApprox q e)
      (Real.log |Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)|) := by
  have hv : ((AzRat.toRat (1 - q) : ℚ) : ℝ) = -((AzRat.toRat q : ℚ) : ℝ) + 1 := by
    rw [AzRat.toRat_sub, AzRat.toRat_one]
    push_cast
    ring
  refine lnAbsGammaApproxOf_bracketConv (lnAbsGammaReflect_conv hneg
    ((if e.sign then e else 0) + 1) (X := fun w => lnGammaRatEncl (1 - q) w) (fun w => ?_)
    (gammaRatSinEncl_conv q hint))
  have := lnGammaRatEncl_L (1 - q) (by rw [hv]; linarith) w
  rwa [hv] at this

/-- **The branches of `lnAbsGammaRatPrecRoundFuel`**: the correctly rounded value, whatever
the fuel, or — at a rational that is not an integer — a fuel loop. -/
theorem lnAbsGammaRatPrecRoundFuel_eq_or_loop (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsGammaRatPrecRoundFuel fuel q p mode).1
        = roundVal p mode (Spec.lnAbsGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (q.den ≠ 1 ∧
        ((0 < ((AzRat.toRat q : ℚ) : ℝ) ∧ (lnAbsGammaRatPrecRoundFuel fuel q p mode).1
            = zivLoop (lnGammaRatApprox q) p mode fuel
              (max 64 (p + 32 + lnGammaRatCancelBits q))) ∨
          (((AzRat.toRat q : ℚ) : ℝ) < 0 ∧ (lnAbsGammaRatPrecRoundFuel fuel q p mode).1
            = zivLoop (lnAbsGammaRatApprox q (gammaRatExp q)) p mode fuel
              (max 64 (p + 32))))) := by
  have hp := NeZero.ne p
  unfold lnAbsGammaRatPrecRoundFuel
  by_cases h0 : q.num = 0
  · left
    rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0,
      Spec.lnAbsGamma_coe_of_pole le_rfl ⟨0, by simp⟩, roundVal_top]
  rw [ite_eq_right h0]
  by_cases hs : q.sign = true
  · have hpos := (toRat_sign_iff q h0).mp hs
    rw [ite_eq_left hs, Spec.lnAbsGamma_coe_of_pos hpos]
    rcases lnGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨hI, -, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hI, Or.inl ⟨hpos, h⟩⟩
  rw [ite_eq_right hs]
  have hs' : q.sign = false := by simpa using hs
  have hneg := toRat_neg_of_sign_false q h0 hs'
  by_cases hd : q.den = 1
  · left
    rw [ite_eq_left hd, Spec.lnAbsGamma_coe_of_pole hneg.le (gammaRat_pole h0 ⟨hd, hs'⟩).2,
      roundVal_top]
  rw [ite_eq_right hd, ite_eq_right hp]
  exact Or.inr ⟨hd, Or.inr ⟨hneg, rfl⟩⟩

/-- **`ln |Γ|` of a rational with explicit fuel is correctly rounded unless the fuel runs
out**, which does not happen at an integer. -/
theorem lnAbsGammaRatPrecRoundFuel_eq_or (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsGammaRatPrecRoundFuel fuel q p mode).1
        = roundVal p mode (Spec.lnAbsGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      ((lnAbsGammaRatPrecRoundFuel fuel q p mode).1 = (nan, .eq) ∧ q.den ≠ 1) := by
  rcases lnAbsGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with
    h | ⟨hI, ⟨hpos, h⟩ | ⟨hneg, h⟩⟩
  · exact Or.inl h
  · rcases eq_or_ne (zivLoop (lnGammaRatApprox q) p mode fuel
      (max 64 (p + 32 + lnGammaRatCancelBits q))) (nan, .eq) with hz | hz
    · exact Or.inr ⟨h.trans hz, hI⟩
    · left
      rw [h, Spec.lnAbsGamma_coe_of_pos hpos, Spec.lnGamma_coe_of_pos hpos]
      exact zivLoop_eq_of_ne_nan_threshold p mode _ _ 64
        (fun w hw => lnGammaRatApprox_valid q hpos hw) _ _ (le_max_left _ _) hz
  · rcases eq_or_ne (zivLoop (lnAbsGammaRatApprox q (gammaRatExp q)) p mode fuel
      (max 64 (p + 32))) (nan, .eq) with hz | hz
    · exact Or.inr ⟨h.trans hz, hI⟩
    · left
      rw [h, Spec.lnAbsGamma_coe (fun hc => not_exists_int_of_den_ne_one q hI hc.2)]
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => lnAbsGammaApproxOf_valid_or_none
          (fun _ hc => lnAbsGammaRatNegEncl_spec q hneg _ hw hc) w p mode)
        _ _ (le_max_left _ _) hz

/-- **`ln |Γ|` of a rational is correctly rounded unless the fuel runs out.** -/
theorem lnAbsGammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsGammaRatPrecRound q p mode).1
        = roundVal p mode (Spec.lnAbsGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (lnAbsGammaRatPrecRound q p mode).1 = (nan, .eq) :=
  (lnAbsGammaRatPrecRoundFuel_eq_or (lnGammaFuel p) q p mode).imp_right And.left

/-- **The specification of `ln |Γ|` of a rational** (`ZivSpec`, for the rounded value):
correct at every fuel at the poles and at `1` and `2` (exact values) and at the integers from
`3` on. -/
theorem lnAbsGammaRatPrecRoundFuel_zivSpec :
    ZivSpec (fun q : AzRat => Spec.lnAbsGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal))
      (fun fuel q p mode => (lnAbsGammaRatPrecRoundFuel fuel q p mode).1)
      {q | (((AzRat.toRat q : ℚ) : ℝ) ≤ 0 ∧ ∃ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = k) ∨
        ((AzRat.toRat q : ℚ) : ℝ) = 1 ∨ ((AzRat.toRat q : ℚ) : ℝ) = 2}
      {q | ∃ n : ℕ, 3 ≤ n ∧ ((AzRat.toRat q : ℚ) : ℝ) = n} where
  sound := fun fuel q p _ mode =>
    (lnAbsGammaRatPrecRoundFuel_eq_or fuel q p mode).imp_right And.left
  complete := fun q p _ mode hB => by
    by_cases hI : q.den = 1
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases lnAbsGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨hI', -⟩
      · exact h
      · exact absurd hI hI'
    have hint : ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k := fun k hk =>
      not_exists_int_of_den_ne_one q hI ⟨k, hk⟩
    rcases lt_trichotomy ((AzRat.toRat q : ℚ) : ℝ) 0 with hneg | hz | hpos
    · have hval := Spec.lnAbsGamma_coe
        (fun hc : ((AzRat.toRat q : ℚ) : ℝ) ≤ 0 ∧ ∃ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = k =>
          not_exists_int_of_den_ne_one q hI hc.2)
      have hB' := hB _ hval
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode _
        (lnAbsGammaRatApprox_bracketConv q hneg hint (gammaRatExp q))
        (ne_zero_of_not_mem_floatSet hB') hB' (max 64 (p + 32)) (by omega) (fun w hw => by
          rcases lnAbsGammaApproxOf_valid_or_none
            (fun _ hc => lnAbsGammaRatNegEncl_spec q hneg (gammaRatExp q)
              (le_trans (le_max_left _ _) hw) hc) w p mode with
            ⟨lv, hv', h1, h2, h3, h4, -⟩ | hn
          · exact Or.inl ⟨lv, hv', h1, h2, h3, h4⟩
          · exact Or.inr hn)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases lnAbsGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with
        h | ⟨-, ⟨hpos, -⟩ | ⟨-, h⟩⟩
      · exact h
      · exact absurd hneg (not_lt.mpr hpos.le)
      · rw [h, hval]
        exact hF fuel hfuel
    · exact absurd hz (by simpa using hint 0)
    · have hval : Spec.lnAbsGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)
          = some ((Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)) : ℝ) : EReal) := by
        rw [Spec.lnAbsGamma_coe_of_pos hpos, Spec.lnGamma_coe_of_pos hpos]
      obtain ⟨F, hF⟩ := lnGammaRat_zivLoop_eventually q hpos p mode
        (max 64 (p + 32 + lnGammaRatCancelBits q)) (le_max_left _ _) (hB _ hval)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases lnAbsGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with
        h | ⟨-, ⟨-, h⟩ | ⟨hneg, -⟩⟩
      · exact h
      · rw [h, hval]
        exact hF fuel hfuel
      · exact absurd hneg (not_lt.mpr hpos.le)
  dyadic := fun q hq v hv =>
    isDyadic_of_lnAbsGamma (fun t ht => by
      have : ((AzRat.toRat q : ℚ) : ℝ) = t := by exact_mod_cast ht
      rw [← this]
      exact hq) hv
  nondyadic := fun q hq => by
    obtain ⟨n, hn, hq⟩ := hq
    refine ⟨_, ?_, not_isDyadic_of_irrational (irrational_log_gamma_nat hn)⟩
    have hpos : (0 : ℝ) < n := by positivity
    rw [hq, Spec.lnAbsGamma_coe_of_pos hpos, Spec.lnGamma_coe_of_pos hpos]
  correct := fun q hq fuel p _ mode => by
    rcases lnAbsGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨hI, -⟩
    · exact h
    · exfalso
      have hint := not_exists_int_of_den_ne_one q hI
      rcases hq with (⟨-, h⟩ | h | h) | ⟨n, -, hn⟩
      · exact hint h
      · exact hint ⟨1, by rw [h]; simp⟩
      · exact hint ⟨2, by rw [h]; simp⟩
      · exact hint ⟨n, by rw [hn]; simp⟩

/-- **The sign component is the sign of `Γ(q)`** at every rational that is not a pole. -/
theorem lnAbsGammaRatPrecRound_sign (q : AzRat)
    (hnp : ¬ (((AzRat.toRat q : ℚ) : ℝ) ≤ 0 ∧ ∃ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = k)) (p : ℕ)
    (mode : RoundingMode) :
    (lnAbsGammaRatPrecRound q p mode).2 = true
      ↔ 0 < Real.Gamma ((AzRat.toRat q : ℚ) : ℝ) := by
  unfold lnAbsGammaRatPrecRound lnAbsGammaRatPrecRoundFuel
  by_cases h0 : q.num = 0
  · have hz := coe_toRat_eq_zero_of_num_eq_zero q h0
    exact absurd ⟨hz.le, 0, by rw [hz]; simp⟩ hnp
  rw [ite_eq_right h0]
  by_cases hs : q.sign = true
  · rw [ite_eq_left hs]
    simp only [true_iff]
    exact Real.Gamma_pos_of_pos ((toRat_sign_iff q h0).mp hs)
  rw [ite_eq_right hs]
  have hs' : q.sign = false := by simpa using hs
  by_cases hd : q.den = 1
  · obtain ⟨hneg, hk⟩ := gammaRat_pole h0 ⟨hd, hs'⟩
    exact absurd ⟨hneg.le, hk⟩ hnp
  rw [ite_eq_right hd]
  exact Gamma_pos_iff_floor_odd q h0 hs' hd

end

end Azurite.AzFloat
