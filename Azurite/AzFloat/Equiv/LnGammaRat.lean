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

/-- **`ln Γ` of a rational is correctly rounded unless the fuel runs out.** -/
theorem lnGammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnGammaRatPrecRound q p mode
        = roundVal p mode (Spec.lnGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      lnGammaRatPrecRound q p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold lnGammaRatPrecRound
  by_cases h0 : q.num = 0
  · left
    rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, EReal.coe_zero,
      Spec.lnGamma_zero, roundVal_top]
  rw [ite_eq_right h0]
  by_cases hs : q.sign = false
  · left
    have hneg : ((AzRat.toRat q : ℚ) : ℝ) < 0 := by
      have hne : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
      refine lt_of_le_of_ne (not_lt.mp fun hpos => ?_) hne
      rw [(toRat_sign_iff q h0).mpr hpos] at hs
      exact Bool.noConfusion hs
    rw [ite_eq_left hs, Spec.lnGamma_coe_of_neg hneg, roundVal_none]
  rw [ite_eq_right hs]
  have hpos : 0 < ((AzRat.toRat q : ℚ) : ℝ) :=
    (toRat_sign_iff q h0).mp (by simpa using hs)
  rw [Spec.lnGamma_coe_of_pos hpos]
  by_cases h12 : (q - 1).num = 0 ∨ (q - 1 - 1).num = 0
  · left
    rw [ite_eq_left h12]
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
  rw [ite_eq_right h12, ite_eq_right hp]
  rcases eq_or_ne (zivLoop (lnGammaRatApprox q) p mode lnGammaFuel
    (max 64 (p + 32 + lnGammaRatCancelBits q))) (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_threshold p mode _ _ 64
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi⟩ :=
          lnGammaApproxOf_spec (lnGammaRatBracket_spec q hpos hw) w
        exact ⟨lv, hv', hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
      _ _ (le_max_left _ _) hz

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

/-- **`ln |Γ|` of a rational is correctly rounded unless the fuel runs out.** -/
theorem lnAbsGammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsGammaRatPrecRound q p mode).1
        = roundVal p mode (Spec.lnAbsGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (lnAbsGammaRatPrecRound q p mode).1 = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold lnAbsGammaRatPrecRound
  by_cases h0 : q.num = 0
  · left
    rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0,
      Spec.lnAbsGamma_coe_of_pole le_rfl ⟨0, by simp⟩, roundVal_top]
  rw [ite_eq_right h0]
  by_cases hs : q.sign = true
  · rw [ite_eq_left hs, Spec.lnAbsGamma_coe_of_pos ((toRat_sign_iff q h0).mp hs)]
    exact lnGammaRatPrecRound_eq_or q p mode
  rw [ite_eq_right hs]
  have hs' : q.sign = false := by simpa using hs
  have hneg := toRat_neg_of_sign_false q h0 hs'
  by_cases hd : q.den = 1
  · left
    rw [ite_eq_left hd, Spec.lnAbsGamma_coe_of_pole hneg.le (gammaRat_pole h0 ⟨hd, hs'⟩).2,
      roundVal_top]
  rw [ite_eq_right hd, ite_eq_right hp,
    Spec.lnAbsGamma_coe (fun hc => not_exists_int_of_den_ne_one q hd hc.2)]
  dsimp only
  rcases eq_or_ne (zivLoop (lnAbsGammaRatApprox q (gammaRatExp q)) p mode lnGammaFuel
    (max 64 (p + 32))) (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => lnAbsGammaApproxOf_valid_or_none
        (fun _ hc => lnAbsGammaRatNegEncl_spec q hneg _ hw hc) w p mode)
      _ _ (le_max_left _ _) hz

/-- **The sign component is the sign of `Γ(q)`** at every rational that is not a pole. -/
theorem lnAbsGammaRatPrecRound_sign (q : AzRat)
    (hnp : ¬ (((AzRat.toRat q : ℚ) : ℝ) ≤ 0 ∧ ∃ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = k)) (p : ℕ)
    (mode : RoundingMode) :
    (lnAbsGammaRatPrecRound q p mode).2 = true
      ↔ 0 < Real.Gamma ((AzRat.toRat q : ℚ) : ℝ) := by
  unfold lnAbsGammaRatPrecRound
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
