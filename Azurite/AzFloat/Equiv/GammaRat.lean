/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaRat
import Azurite.AzFloat.Equiv.GammaRatBracket
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

* The pieces on enclosures of rationals are in `Equiv/GammaRatBracket.lean`.
* `gammaRatTiny?_eq`, `reciprocalGammaRatTiny?_eq`: the tiny-argument paths.
* `gammaRatPrecRound_eq_or`, `reciprocalGammaRatPrecRound_eq_or`: the results are the correctly
  rounded `Spec.gamma q` and `Spec.reciprocalGamma q` unless the fuel runs out (`(nan, .eq)`).
* `gammaRatPrecRound_eq_of_special`, `reciprocalGammaRatPrecRound_eq_of_special`: no `NaN` for
  the denominators `2, 3, 4, 6` (`gammaRatSpecial`, `gammaRatSpecial_iff`), where the loops
  are certified.
-/

namespace Azurite.AzFloat

open Real

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

/-- The brackets of the rational functions are valid from 64 bits on. -/
theorem gammaRatApprox_valid (recip : Bool) (q : AzRat) (h0 : q.num ≠ 0) (e : AzInt) (p : ℕ)
    [NeZero p] (mode : RoundingMode) (w : ℕ) (hw : 64 ≤ w) :
    (∃ lv hv : ℝ, Rounds (gammaRatApprox recip q e q.sign w).1 lv ∧
        Rounds (gammaRatApprox recip q e q.sign w).2 hv ∧
        lv ≤ gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) ∧
        gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) ≤ hv) ∨
      roundingPossible (gammaRatApprox recip q e q.sign w).1
        (gammaRatApprox recip q e q.sign w).2 p mode = none := by
  rcases gammaApproxOf_valid_or_none (v := gammaVal recip ((AzRat.toRat q : ℚ) : ℝ))
    (c := gammaRatCore recip q e q.sign w)
    (fun _ _ hc' => gammaRatCore_spec q (fun hs => (toRat_sign_iff q h0).mp hs)
      (fun hs => toRat_neg_of_sign_false q h0 hs) hw hc') w p mode
    with ⟨lv, hv', h1, h2, h3, h4, -⟩ | hn
  · exact Or.inl ⟨lv, hv', h1, h2, h3, h4⟩
  · exact Or.inr hn

/-- The Ziv loop of the rational functions is correct when it does not give up. -/
theorem gammaRat_zivLoop (recip : Bool) (q : AzRat) (h0 : q.num ≠ 0) (e : AzInt) (p : ℕ)
    [NeZero p] (mode : RoundingMode) (fuel : ℕ) :
    zivLoop (gammaRatApprox recip q e q.sign) p mode fuel (gammaRatStart q e p)
        = roundVal p mode (some ((gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) ∨
      zivLoop (gammaRatApprox recip q e q.sign) p mode fuel (gammaRatStart q e p)
        = (nan, .eq) := by
  rcases eq_or_ne (zivLoop (gammaRatApprox recip q e q.sign) p mode fuel
    (gammaRatStart q e p)) (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => gammaApproxOf_valid_or_none
        (fun _ _ hc => gammaRatCore_spec q (fun hs => (toRat_sign_iff q h0).mp hs)
          (fun hs => toRat_neg_of_sign_false q h0 hs) hw hc) w p mode)
      _ _ (le_max_left _ _) hz

/-- `isUnitFraction` recognizes `1/d`. -/
theorem isUnitFraction_spec {q : AzRat} {d : ℕ} (h : isUnitFraction q d = true) :
    ((AzRat.toRat q : ℚ) : ℝ) = 1 / d := by
  unfold isUnitFraction at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hs, hn⟩, hd⟩ := h
  rw [AzRat.toRat_cast_eq, hs, hn, hd, AzNat.toNat_ofNat, AzNat.toNat_one]
  simp

/-- **The certified loop at a rational with denominator `2, 3, 4, 6`** gives the correctly
rounded value. -/
theorem gammaRatCertified_eq (recip : Bool) (q : AzRat) (hc : gammaRatSpecial q = true)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaRatCertified recip q hc p mode
      = roundVal p mode (some ((gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) := by
  have h0 := num_ne_zero_of_gammaRatSpecial hc
  unfold gammaRatCertified
  refine zivLoopCertified_eq_or_none p mode _ _
    (not_mem_floatSet_of_irrational p (irrational_gammaVal recip _ (gammaRatSpecial_spec hc)))
    _ (by omega) (fun w hw => ?_) _
  rcases gammaApproxOf_valid_or_none (v := gammaVal recip ((AzRat.toRat q : ℚ) : ℝ))
    (c := gammaRatCore recip q (gammaRatExp q) q.sign w)
    (fun _ _ hc' => gammaRatCore_spec q (fun hs => (toRat_sign_iff q h0).mp hs)
      (fun hs => toRat_neg_of_sign_false q h0 hs) (le_trans (le_max_left _ _) hw) hc') w p mode
    with ⟨lv, hv', h1, h2, h3, h4, -⟩ | hn
  · exact Or.inl ⟨lv, hv', h1, h2, h3, h4⟩
  · exact Or.inr hn

/-- **The constants path at a rational with denominator `2, 3, 4, 6`** answers with the
correctly rounded value or with `(nan, .eq)`. -/
theorem gammaRatSpecialFast_eq_or (recip : Bool) {q : AzRat} (hc : gammaRatSpecial q = true)
    (p : ℕ) [NeZero p] (mode : RoundingMode) {res : AzFloat × Ordering}
    (h : gammaSpecialFast? recip q.sign q.num q.den.toNat p mode = some res) :
    res = roundVal p mode (some ((gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) ∨
      res = (nan, .eq) := by
  have hden := gammaRatSpecial_spec hc
  rw [show (AzRat.toRat q).den = q.den.toNat from rfl] at hden
  have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
  have hg : Nat.gcd (q.num.toNat % q.den.toNat) q.den.toNat = 1 := by
    rw [← Nat.gcd_rec]
    exact hcop.symm
  have hd2 : 2 ≤ q.den.toNat := by rcases hden with h | h | h | h <;> omega
  have hr0 : q.num.toNat % q.den.toNat ≠ 0 := by
    intro h0
    rw [h0, Nat.gcd_zero_left] at hg
    omega
  have := gammaSpecialFast?_eq_or recip q.sign hden hr0 (Or.inl hg) p mode h
  have hval : (if q.sign then (1 : ℝ) else -1) * ((q.num.toNat : ℝ) / (q.den.toNat : ℝ))
      = ((AzRat.toRat q : ℚ) : ℝ) := by
    rw [AzRat.toRat_cast_eq]
    cases q.sign
    · simp only [Bool.false_eq_true, ↓reduceIte]
      push_cast
      ring
    · simp only [↓reduceIte]
      push_cast
      ring
  rwa [hval] at this

/-- **The certified loop at a positive integer rational beyond the factorial bound** gives
the correctly rounded value. -/
theorem gammaRatCertInt_eq (recip : Bool) {q : AzRat} {p : ℕ} [NeZero p] (h0 : q.num ≠ 0)
    (hpole : ¬ (q.den = 1 ∧ q.sign = false))
    (hsm : ¬ gammaRatSmallInt q (gammaIntBound p) = true) (hI : q.den = 1) (e : AzInt)
    (mode : RoundingMode)
    (h : ∃ f : ℕ, (roundingPossible
      (gammaRatApprox recip q e q.sign (max 64 (p + 32) * 2 ^ f)).1
      (gammaRatApprox recip q e q.sign (max 64 (p + 32) * 2 ^ f)).2 p mode).isSome = true) :
    zivLoopCertified (gammaRatApprox recip q e q.sign) p mode (max 64 (p + 32)) h
      = roundVal p mode (some ((gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) := by
  obtain ⟨-, n, hn, hval⟩ := gammaRatBigInt_spec h0 hpole hsm hI
  refine zivLoopCertified_eq_or_none p mode _ _ ?_ _ (by omega)
    (fun w hw => gammaRatApprox_valid recip q h0 e p mode w (le_trans (le_max_left _ _) hw)) h
  rw [hval]
  exact gammaVal_int_not_boundary recip p hn

/-- **The branches of `gammaRatPrecRoundFuel`**: the correctly rounded value, whatever the
fuel, or — at a rational that is not an integer and whose denominator is none of
`2, 3, 4, 6` — the fuel loop on `gammaRatApprox`. -/
theorem gammaRatPrecRoundFuel_eq_or_loop (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    gammaRatPrecRoundFuel fuel q p mode
        = roundVal p mode (Spec.gamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (gammaRatSpecial q = false ∧ q.den ≠ 1 ∧ q.num ≠ 0 ∧
        gammaRatPrecRoundFuel fuel q p mode
          = zivLoop (gammaRatApprox false q (gammaRatExp q) q.sign) p mode fuel
            (gammaRatStart q (gammaRatExp q) p)) := by
  have hp := NeZero.ne p
  unfold gammaRatPrecRoundFuel
  by_cases h0 : q.num = 0
  · left
    rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, EReal.coe_zero,
      Spec.gamma_zero, roundVal_top]
  rw [dite_eq_right h0]
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  by_cases hpole : q.den = 1 ∧ q.sign = false
  · left
    obtain ⟨hneg, hk⟩ := gammaRat_pole h0 hpole
    rw [dite_eq_left hpole, Spec.gamma_coe_of_pole hneg hk, roundVal_none]
  rw [dite_eq_right hpole, dite_eq_right hp, Spec.gamma_coe hx0 (gammaRat_not_pole h0 hpole)]
  by_cases hsm : gammaRatSmallInt q (gammaIntBound p) = true
  · left
    obtain ⟨n, hn, hval⟩ := gammaRatSmallInt_spec h0 hsm
    rw [dite_eq_left hsm, hn, Nat.add_sub_cancel, hval, Real.Gamma_nat_eq_factorial,
      setPrecRound_eq_roundVal (toVal_ofAzNat _), AzNat.toNat_factorial]
  rw [dite_eq_right hsm]
  by_cases hc : gammaRatSpecial q = true
  · left
    simp only [hc, ↓reduceDIte]
    have hcert := gammaRatCertified_eq false q hc p mode
    rw [show gammaVal false ((AzRat.toRat q : ℚ) : ℝ) = Real.Gamma ((AzRat.toRat q : ℚ) : ℝ)
      from rfl] at hcert
    split
    · rename_i r hr
      exact nanOrElse_eq (gammaRatSpecialFast_eq_or false hc p mode hr) hcert
    · exact hcert
  have hc' : gammaRatSpecial q = false := by simpa using hc
  rw [dite_eq_right hc]
  by_cases hI : q.den = 1
  · left
    rw [dite_eq_left hI]
    exact gammaRatCertInt_eq false h0 hpole hsm hI _ mode _
  rw [dite_eq_right hI]
  dsimp only
  split
  · rename_i r hr
    left
    exact gammaRatTiny?_eq q h0 _ p mode hr
  · exact Or.inr ⟨hc', hI, h0, rfl⟩

/-- **`Γ` of a rational with explicit fuel is correctly rounded unless the fuel runs out**,
which happens neither at an integer nor for the denominators `2, 3, 4, 6`. -/
theorem gammaRatPrecRoundFuel_eq_or (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    gammaRatPrecRoundFuel fuel q p mode
        = roundVal p mode (Spec.gamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (gammaRatPrecRoundFuel fuel q p mode = (nan, .eq) ∧ gammaRatSpecial q = false ∧
        q.den ≠ 1) := by
  rcases gammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨hc, hI, h0, h⟩
  · exact Or.inl h
  · rcases gammaRat_zivLoop false q h0 (gammaRatExp q) p mode fuel with hz | hz
    · left
      have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
        h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
      rw [h, hz, Spec.gamma_coe hx0 (gammaRat_not_pole h0 (fun hp => hI hp.1))]
      rfl
    · exact Or.inr ⟨h.trans hz, hc, hI⟩

/-- **`Γ` of a rational is correctly rounded unless the fuel runs out**, which does not happen
for the denominators `2, 3, 4, 6`. -/
theorem gammaRatPrecRound_eq_or' (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaRatPrecRound q p mode
        = roundVal p mode (Spec.gamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (gammaRatPrecRound q p mode = (nan, .eq) ∧ gammaRatSpecial q = false) :=
  (gammaRatPrecRoundFuel_eq_or (gammaFuel p) q p mode).imp_right fun h => ⟨h.1, h.2.1⟩

/-- **`Γ` of a rational is correctly rounded unless the fuel runs out.** -/
theorem gammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaRatPrecRound q p mode
        = roundVal p mode (Spec.gamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      gammaRatPrecRound q p mode = (nan, .eq) :=
  (gammaRatPrecRound_eq_or' q p mode).imp_right And.left

/-- **`Γ` of an integer rational is correctly rounded, unconditionally.** -/
theorem gammaRatPrecRound_eq_of_den_one (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (h : q.den = 1) :
    gammaRatPrecRound q p mode
      = roundVal p mode (Spec.gamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  rcases gammaRatPrecRoundFuel_eq_or (gammaFuel p) q p mode with h' | ⟨-, -, h'⟩
  · exact h'
  · exact absurd h h'

/-- **`Γ` of a rational with denominator `2, 3, 4` or `6` is correctly rounded,
unconditionally**: there `Γ(q)` is irrational by Chudnovsky's theorem
(`Azurite.Chudnovsky.irrational_gamma_of_den`) and the Ziv loop carries no fuel. -/
theorem gammaRatPrecRound_eq_of_special (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (h : gammaRatSpecial q = true) :
    gammaRatPrecRound q p mode
      = roundVal p mode (Spec.gamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  rcases gammaRatPrecRound_eq_or' q p mode with h' | ⟨-, h'⟩
  · exact h'
  · rw [h] at h'
    exact Bool.noConfusion h'

/-- `gammaRatSpecial` recognizes the denominators `2, 3, 4, 6`. -/
theorem gammaRatSpecial_iff (q : AzRat) :
    gammaRatSpecial q = true ↔ (AzRat.toRat q).den = 2 ∨ (AzRat.toRat q).den = 3 ∨
      (AzRat.toRat q).den = 4 ∨ (AzRat.toRat q).den = 6 := by
  refine ⟨gammaRatSpecial_spec, fun h => ?_⟩
  have hden : (AzRat.toRat q).den = q.den.toNat := rfl
  rw [hden] at h
  unfold gammaRatSpecial
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  have key : ∀ n : ℕ, q.den.toNat = n → q.den = AzNat.ofNat n := fun n hn =>
    AzNat.toNat_injective (by rw [hn, AzNat.toNat_ofNat])
  rcases h with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl (key _ h)))
  · exact Or.inl (Or.inl (Or.inr (key _ h)))
  · exact Or.inl (Or.inr (key _ h))
  · exact Or.inr (key _ h)

/-- **The branches of `reciprocalGammaRatPrecRoundFuel`**, as for
`gammaRatPrecRoundFuel_eq_or_loop`. -/
theorem reciprocalGammaRatPrecRoundFuel_eq_or_loop (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    reciprocalGammaRatPrecRoundFuel fuel q p mode
        = roundVal p mode (Spec.reciprocalGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (gammaRatSpecial q = false ∧ q.den ≠ 1 ∧ q.num ≠ 0 ∧
        reciprocalGammaRatPrecRoundFuel fuel q p mode
          = zivLoop (gammaRatApprox true q (gammaRatExp q) q.sign) p mode fuel
            (gammaRatStart q (gammaRatExp q) p)) := by
  have hp := NeZero.ne p
  unfold reciprocalGammaRatPrecRoundFuel
  rw [Spec.reciprocalGamma_coe]
  by_cases h0 : q.num = 0
  · left
    rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.Gamma_zero, inv_zero,
      EReal.coe_zero, roundVal_zero]
  rw [dite_eq_right h0]
  by_cases hpole : q.den = 1 ∧ q.sign = false
  · left
    obtain ⟨hneg, hk⟩ := gammaRat_pole h0 hpole
    rw [dite_eq_left hpole, Gamma_eq_zero_of_int_nonpos hneg.le hk, inv_zero, EReal.coe_zero,
      roundVal_zero]
  rw [dite_eq_right hpole, dite_eq_right hp]
  by_cases hsm : gammaRatSmallInt q (gammaIntBound p) = true
  · left
    obtain ⟨n, hn, hval⟩ := gammaRatSmallInt_spec h0 hsm
    have hf0 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [dite_eq_left hsm, hn, Nat.add_sub_cancel, hval, Real.Gamma_nat_eq_factorial,
      divPrecRound_eq_liftVal₂, liftVal₂, toVal_one', toVal_ofAzNat, Option.bind_some,
      Option.bind_some, AzNat.toNat_factorial, Spec.div_coe_coe _ _ hf0, one_div]
  rw [dite_eq_right hsm]
  by_cases hc : gammaRatSpecial q = true
  · left
    simp only [hc, ↓reduceDIte]
    split
    · rename_i r hr
      exact nanOrElse_eq (gammaRatSpecialFast_eq_or true hc p mode hr)
        (gammaRatCertified_eq true q hc p mode)
    · exact gammaRatCertified_eq true q hc p mode
  have hc' : gammaRatSpecial q = false := by simpa using hc
  rw [dite_eq_right hc]
  by_cases hI : q.den = 1
  · left
    rw [dite_eq_left hI]
    exact gammaRatCertInt_eq true h0 hpole hsm hI _ mode _
  rw [dite_eq_right hI]
  dsimp only
  split
  · rename_i r hr
    left
    exact reciprocalGammaRatTiny?_eq q h0 _ p mode hr
  · exact Or.inr ⟨hc', hI, h0, rfl⟩

/-- **`1/Γ` of a rational with explicit fuel is correctly rounded unless the fuel runs
out**, which happens neither at an integer nor for the denominators `2, 3, 4, 6`. -/
theorem reciprocalGammaRatPrecRoundFuel_eq_or (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    reciprocalGammaRatPrecRoundFuel fuel q p mode
        = roundVal p mode (Spec.reciprocalGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (reciprocalGammaRatPrecRoundFuel fuel q p mode = (nan, .eq) ∧
        gammaRatSpecial q = false ∧ q.den ≠ 1) := by
  rcases reciprocalGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨hc, hI, h0, h⟩
  · exact Or.inl h
  · rcases gammaRat_zivLoop true q h0 (gammaRatExp q) p mode fuel with hz | hz
    · left
      rw [h, hz, Spec.reciprocalGamma_coe]
      rfl
    · exact Or.inr ⟨h.trans hz, hc, hI⟩

/-- **`1/Γ` of a rational is correctly rounded unless the fuel runs out**, which does not
happen for the denominators `2, 3, 4, 6`. -/
theorem reciprocalGammaRatPrecRound_eq_or' (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    reciprocalGammaRatPrecRound q p mode
        = roundVal p mode (Spec.reciprocalGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (reciprocalGammaRatPrecRound q p mode = (nan, .eq) ∧ gammaRatSpecial q = false) :=
  (reciprocalGammaRatPrecRoundFuel_eq_or (gammaFuel p) q p mode).imp_right
    fun h => ⟨h.1, h.2.1⟩

/-- **`1/Γ` of a rational is correctly rounded unless the fuel runs out.** -/
theorem reciprocalGammaRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    reciprocalGammaRatPrecRound q p mode
        = roundVal p mode (Spec.reciprocalGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      reciprocalGammaRatPrecRound q p mode = (nan, .eq) :=
  (reciprocalGammaRatPrecRound_eq_or' q p mode).imp_right And.left

/-- **`1/Γ` of an integer rational is correctly rounded, unconditionally.** -/
theorem reciprocalGammaRatPrecRound_eq_of_den_one (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (h : q.den = 1) :
    reciprocalGammaRatPrecRound q p mode
      = roundVal p mode (Spec.reciprocalGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  rcases reciprocalGammaRatPrecRoundFuel_eq_or (gammaFuel p) q p mode with h' | ⟨-, -, h'⟩
  · exact h'
  · exact absurd h h'

/-- **`1/Γ` of a rational with denominator `2, 3, 4` or `6` is correctly rounded,
unconditionally.** -/
theorem reciprocalGammaRatPrecRound_eq_of_special (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (h : gammaRatSpecial q = true) :
    reciprocalGammaRatPrecRound q p mode
      = roundVal p mode (Spec.reciprocalGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  rcases reciprocalGammaRatPrecRound_eq_or' q p mode with h' | ⟨-, h'⟩
  · exact h'
  · rw [h] at h'
    exact Bool.noConfusion h'

/-! ### The specifications as fuel-bound functions -/

/-- The loop of the rational functions is correct for every large enough fuel when the value
is no rounding boundary (at a rational that is not an integer). -/
theorem gammaRat_zivLoop_eventually (recip : Bool) (q : AzRat) (h0 : q.num ≠ 0)
    (hI : q.den ≠ 1) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hB : ((gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel →
      zivLoop (gammaRatApprox recip q (gammaRatExp q) q.sign) p mode fuel
          (gammaRatStart q (gammaRatExp q) p)
        = roundVal p mode (some ((gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) := by
  have hni : ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k := fun k hk =>
    not_exists_int_of_den_ne_one q hI ⟨k, hk⟩
  have hG0 : Real.Gamma ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 :=
    Real.Gamma_ne_zero fun n hn => hni (-(n : ℤ)) (by rw [hn]; push_cast; rfl)
  have hv0 : gammaVal recip ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := by
    cases recip
    · exact hG0
    · exact inv_ne_zero hG0
  have hstart : 64 ≤ gammaRatStart q (gammaRatExp q) p := le_max_left _ _
  exact zivLoop_eventually_eq p mode (gammaRatApprox recip q (gammaRatExp q) q.sign)
    (gammaRatApprox_bracketConv recip q _ (fun hs => (toRat_sign_iff q h0).mp hs)
      (fun hs => ⟨toRat_neg_of_sign_false q h0 hs, hni⟩))
    hv0 hB _ (by omega)
    (fun w hw => gammaRatApprox_valid recip q h0 _ p mode w (le_trans hstart hw))

/-- **The specification of `Γ` of a rational** (`ZivSpec`): sound at every fuel; complete in
the limit of the fuel wherever the value is no rounding boundary; and correct at every fuel
at the integers (exact values) and for the denominators `2, 3, 4, 6` (irrational values, by
Chudnovsky's theorem). -/
theorem gammaRatPrecRoundFuel_zivSpec :
    ZivSpec (fun q : AzRat => Spec.gamma (((AzRat.toRat q : ℚ) : ℝ) : EReal))
      gammaRatPrecRoundFuel {q | q.den = 1} {q | gammaRatSpecial q = true} where
  sound := fun fuel q p _ mode => (gammaRatPrecRoundFuel_eq_or fuel q p mode).imp_right And.left
  complete := fun q p _ mode hB => by
    by_cases hgen : q.den ≠ 1 ∧ q.num ≠ 0
    · obtain ⟨hI, h0⟩ := hgen
      have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
        h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
      have hval := Spec.gamma_coe hx0 (gammaRat_not_pole h0 (fun hp => hI hp.1))
      obtain ⟨F, hF⟩ := gammaRat_zivLoop_eventually false q h0 hI p mode (hB _ hval)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases gammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨-, -, -, h⟩
      · exact h
      · rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases gammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨-, hI, h0, -⟩
      · exact h
      · exact absurd ⟨hI, h0⟩ hgen
  dyadic := fun q hq v hv => by
    have hq : q.den = 1 := hq
    rw [coe_toRat_eq_mkNorm_of_den_one q hq] at hv
    exact isDyadic_of_gamma_int _ hv
  nondyadic := fun q hq => by
    have hq : gammaRatSpecial q = true := hq
    have h0 := num_ne_zero_of_gammaRatSpecial hq
    have hden := gammaRatSpecial_spec hq
    have hne : (AzRat.toRat q).den ≠ 1 := by
      rcases hden with h | h | h | h <;> rw [h] <;> norm_num
    have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
      h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
    exact ⟨_, Spec.gamma_coe hx0 (fun h => by
        obtain ⟨k, hk⟩ := h.2
        exact ne_int_of_den_ne_one hne k hk),
      not_isDyadic_of_irrational (irrational_gammaVal false _ hden)⟩
  correct := fun q hq fuel p _ mode => by
    rcases gammaRatPrecRoundFuel_eq_or fuel q p mode with h | ⟨-, hc, hI⟩
    · exact h
    · rcases hq with hD | hN
      · exact absurd hD hI
      · have hN' : gammaRatSpecial q = true := hN
        rw [hc] at hN'
        exact Bool.noConfusion hN'

/-- **The specification of `1/Γ` of a rational** (`ZivSpec`): correct at every fuel at the
integers (`0`, `1`, `1/2` up to `3`; from `4` on `1/(n − 1)!` is not dyadic) and for the
denominators `2, 3, 4, 6`. -/
theorem reciprocalGammaRatPrecRoundFuel_zivSpec :
    ZivSpec (fun q : AzRat => Spec.reciprocalGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal))
      reciprocalGammaRatPrecRoundFuel
      {q | q.den = 1 ∧ ((AzRat.toRat q : ℚ) : ℝ) ≤ 3}
      {q | gammaRatSpecial q = true ∨ (q.den = 1 ∧ 4 ≤ ((AzRat.toRat q : ℚ) : ℝ))} where
  sound := fun fuel q p _ mode =>
    (reciprocalGammaRatPrecRoundFuel_eq_or fuel q p mode).imp_right And.left
  complete := fun q p _ mode hB => by
    by_cases hgen : q.den ≠ 1 ∧ q.num ≠ 0
    · obtain ⟨hI, h0⟩ := hgen
      have hval := Spec.reciprocalGamma_coe ((AzRat.toRat q : ℚ) : ℝ)
      obtain ⟨F, hF⟩ := gammaRat_zivLoop_eventually true q h0 hI p mode (hB _ hval)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases reciprocalGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨-, -, -, h⟩
      · exact h
      · rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases reciprocalGammaRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨-, hI, h0, -⟩
      · exact h
      · exact absurd ⟨hI, h0⟩ hgen
  dyadic := fun q hq v hv => by
    obtain ⟨hd, h3⟩ : q.den = 1 ∧ ((AzRat.toRat q : ℚ) : ℝ) ≤ 3 := hq
    rw [Spec.reciprocalGamma_coe, Option.some.injEq, EReal.coe_eq_coe_iff] at hv
    rw [← hv]
    rw [coe_toRat_eq_mkNorm_of_den_one q hd] at h3 ⊢
    exact isDyadic_reciprocalGamma_int (by exact_mod_cast h3)
  nondyadic := fun q hq => by
    refine ⟨_, Spec.reciprocalGamma_coe _, ?_⟩
    rcases hq with hq | ⟨hd, h4⟩
    · exact not_isDyadic_of_irrational
        (irrational_gammaVal true _ (gammaRatSpecial_spec hq))
    · rw [coe_toRat_eq_mkNorm_of_den_one q hd] at h4 ⊢
      exact not_isDyadic_reciprocalGamma_int (by exact_mod_cast h4)
  correct := fun q hq fuel p _ mode => by
    rcases reciprocalGammaRatPrecRoundFuel_eq_or fuel q p mode with h | ⟨-, hc, hI⟩
    · exact h
    · rcases hq with hD | hN | hN
      · exact absurd hD.1 hI
      · rw [hc] at hN
        exact Bool.noConfusion hN
      · exact absurd hN.1 hI

end Azurite.AzFloat
