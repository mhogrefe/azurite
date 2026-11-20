/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBeta
import Azurite.AzFloat.Equiv.Beta
import Azurite.AzFloat.Equiv.LnGamma
import Azurite.AzFloat.Equiv.Ln
import Azurite.AzFloat.Equiv.NegRound

/-!
# Equivalence: `ln B(a, b)`, and `ln |B(a, b)|` with the sign of `B(a, b)`

`Spec.lnAbsBeta a b = (Spec.beta a b).map Spec.lnAbsE`: the logarithm of the absolute value of
`Spec.beta` (`Equiv/Beta.lean`), `+∞` at `±∞` and `−∞` at `0`.

* `lnAbsLoop_spec`: the loop, for any core whose answers are the sign of `v` and an enclosure
  of `ln |v|`, returns `(nan, .eq)` or the rounding of `ln |v|` with the sign of `v`.
* `lnAbsBetaRealFuel_main`, **`lnAbsBetaPrecRoundFuel_eq_or`** (the value: correctly rounded, or
  `(nan, .eq)` when the fuel runs out), **`lnAbsBetaPrecRoundFuel_sign`** (the sign, whenever the
  value is not `NaN`).
* `Spec.lnBeta a b = (Spec.beta a b).bind Spec.log` and **`lnBetaPrecRoundFuel_eq_or`**, from
  `Spec.lnAbsBeta_eq_lnBeta` (the two agree where `B` is not a negative real).
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- `ln |v|` on the extended reals: `+∞` at `±∞`, `−∞` at `0`. -/
noncomputable def lnAbsE (v : EReal) : EReal :=
  if v = ⊤ ∨ v = ⊥ then ⊤ else if v.toReal = 0 then ⊥ else ((Real.log |v.toReal| : ℝ) : EReal)

theorem lnAbsE_top : lnAbsE ⊤ = ⊤ := by simp [lnAbsE]

theorem lnAbsE_zero : lnAbsE ((0 : ℝ) : EReal) = ⊥ := by
  unfold lnAbsE
  rw [ite_eq_right (by simp), EReal.toReal_coe, ite_eq_left rfl]

theorem lnAbsE_coe {v : ℝ} (hv : v ≠ 0) : lnAbsE (v : EReal) = ((Real.log |v| : ℝ) : EReal) := by
  unfold lnAbsE
  rw [ite_eq_right (by simp), EReal.toReal_coe, ite_eq_right hv]

/-- `ln |B|` on the extended reals: the logarithm of the absolute value of `Spec.beta`. -/
noncomputable def lnAbsBeta (a b : EReal) : Option EReal := (beta a b).map lnAbsE

end Spec

/-! ### The loop -/

/-- A level that answers gives the rounding of `ln |v|` and the sign of `v`. -/
theorem lnAbsStep_spec {core : ℕ → Option (Bool × Encl)} {v : ℝ} {w : ℕ}
    (hcore : ∀ neg L, core w = some (neg, L) →
      0 < (if neg then -1 else 1) * v ∧ IsEncl L (Real.log ((if neg then -1 else 1) * v)))
    (p : ℕ) [NeZero p] (mode : RoundingMode) {r : (AzFloat × Ordering) × Bool}
    (h : lnAbsStep core p mode w = some r) :
    r.1 = roundVal p mode (some ((Real.log |v| : ℝ) : EReal)) ∧ (r.2 = true ↔ 0 < v) := by
  unfold lnAbsStep at h
  split at h
  · exact absurd h (by simp)
  · rename_i neg L hc
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hpos, hL⟩ := hcore neg L hc
    have habs : (if neg = true then (-1 : ℝ) else 1) * v = |v| := by
      cases neg
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hpos ⊢
        exact (abs_of_pos hpos).symm
      · simp only [↓reduceIte, neg_one_mul] at hpos ⊢
        exact (abs_of_neg (by linarith)).symm
    rw [habs] at hL
    obtain ⟨lv, hv, h1, h2, h3, h4⟩ := lnGammaApproxOf_spec hL w
    refine ⟨roundingPossible_eq p mode h1 h2 h3.le h4 (fun h' => absurd h' h3.ne) hr', ?_⟩
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hpos
      simpa using hpos
    · simp only [↓reduceIte, neg_one_mul] at hpos
      simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_lt]
      linarith

/-- **The loop returns `(nan, .eq)`, or the rounding of `ln |v|` with the sign of `v`.** -/
theorem lnAbsLoop_spec {core : ℕ → Option (Bool × Encl)} {v : ℝ} {w₀ : ℕ}
    (hcore : ∀ w, w₀ ≤ w → ∀ neg L, core w = some (neg, L) →
      0 < (if neg then -1 else 1) * v ∧ IsEncl L (Real.log ((if neg then -1 else 1) * v)))
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ∀ (fuel w : ℕ), w₀ ≤ w →
      (lnAbsLoop core p mode fuel w).1 = (nan, .eq) ∨
        ((lnAbsLoop core p mode fuel w).1 = roundVal p mode (some ((Real.log |v| : ℝ) : EReal))
          ∧ ((lnAbsLoop core p mode fuel w).2 = true ↔ 0 < v))
  | 0, w, hw => by
    rw [lnAbsLoop]
    cases hs : lnAbsStep core p mode w with
    | none => left; rfl
    | some r => right; exact lnAbsStep_spec (hcore w hw) p mode hs
  | fuel + 1, w, hw => by
    rw [lnAbsLoop]
    cases hs : lnAbsStep core p mode w with
    | none => exact lnAbsLoop_spec hcore p mode fuel (2 * w) (by omega)
    | some r => right; exact lnAbsStep_spec (hcore w hw) p mode hs

/-! ### `−ln |x|` -/

/-- `negLnAbs x` is the rounding of `−ln |x|`, `x ≠ 0`. -/
theorem negLnAbs_eq {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    negLnAbs x p mode = roundVal p mode (some ((-Real.log |xv| : ℝ) : EReal)) := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  unfold negLnAbs
  dsimp only
  rw [lnPrecRound_eq_liftVal, liftVal, habs, Option.bind_some,
    Spec.log_coe _ (abs_pos.mpr hx0), roundVal_neg]

/-- `ln |1/x| = −ln |x|`. -/
theorem log_abs_one_div (x : ℝ) : Real.log |1 / x| = -Real.log |x| := by
  rw [abs_div, abs_one, one_div, Real.log_inv]

/-! ### The driver -/

/-- `B(a, b) ≠ 0` off the special values. -/
theorem beta_ne_zero {av bv : ℝ} (ha0 : av ≠ 0) (hb0 : bv ≠ 0)
    (hpa : ¬ (av < 0 ∧ ∃ k : ℤ, av = k)) (hpb : ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k))
    (hs : ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)) :
    Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) ≠ 0 := by
  have h1 := Real.Gamma_ne_zero (ne_neg_nat_of_not_pole ha0 hpa)
  have h2 := Real.Gamma_ne_zero (ne_neg_nat_of_not_pole hb0 hpb)
  have h3 : Real.Gamma (av + bv) ≠ 0 := by
    refine Real.Gamma_ne_zero fun m hm => hs ⟨?_, -(m : ℤ), by rw [hm]; push_cast; rfl⟩
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact div_ne_zero (mul_ne_zero h1 h2) h3

/-- **`lnAbsBetaRealFuel` off the special values**: `(nan, .eq)`, or the rounding of `ln |B|` with
the sign of `B`. -/
theorem lnAbsBetaRealFuel_main (fuel : ℕ) {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (ha0 : av ≠ 0) (hb0 : bv ≠ 0)
    (hpa : ¬ (av < 0 ∧ ∃ k : ℤ, av = k)) (hpb : ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k))
    (hs : ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsBetaRealFuel fuel a b p mode).1 = (nan, .eq) ∨
      ((lnAbsBetaRealFuel fuel a b p mode).1 = roundVal p mode
          (some ((Real.log |Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)| : ℝ) : EReal))
        ∧ ((lnAbsBetaRealFuel fuel a b p mode).2 = true
          ↔ 0 < Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv))) := by
  have hp := NeZero.ne p
  unfold lnAbsBetaRealFuel
  have hpole : ¬ (isNegInt a || isNegInt b) = true := by
    rw [Bool.or_eq_true, isNegInt_iff ha, isNegInt_iff hb]
    exact fun h => h.elim hpa hpb
  have hzero : ¬ (isZeroVal a || isZeroVal b) = true := by
    rw [Bool.or_eq_true, isZeroVal_iff ha, isZeroVal_iff hb]
    exact fun h => h.elim ha0 hb0
  have hsum : ¬ sumIsNonposInt a b = true := by rw [sumIsNonposInt_iff ha hb]; exact hs
  rw [ite_eq_right hpole, ite_eq_right hzero, ite_eq_right hsum, ite_eq_right hp]
  by_cases hb1 : isOneVal b = true
  · right
    rw [ite_eq_left hb1, (isOneVal_iff hb).mp hb1, gamma_mul_gamma_one_div ha0 hpa,
      log_abs_one_div]
    exact ⟨negLnAbs_eq ha ha0 p mode, by
      show lt zero a = true ↔ _
      rw [lt_eq_true_iff toVal_zero' ha, one_div, inv_pos]⟩
  rw [ite_eq_right hb1]
  by_cases ha1 : isOneVal a = true
  · right
    have hv : Real.Gamma 1 * Real.Gamma bv / Real.Gamma (1 + bv) = 1 / bv := by
      rw [mul_comm, add_comm]
      exact gamma_mul_gamma_one_div hb0 hpb
    rw [ite_eq_left ha1, (isOneVal_iff ha).mp ha1, hv, log_abs_one_div]
    exact ⟨negLnAbs_eq hb hb0 p mode, by
      show lt zero b = true ↔ _
      rw [lt_eq_true_iff toVal_zero' hb, one_div, inv_pos]⟩
  rw [ite_eq_right ha1]
  exact lnAbsLoop_spec (w₀ := 64)
    (fun w hw neg L hc => lnAbsBetaCore_spec ha hb (by omega) hw hc) p mode _ _
    (le_max_left _ _)

/-- `lnAbsBetaRealFuel` is the correct rounding of `Spec.lnAbsBeta` on finite arguments, or the
fuel ran out. -/
theorem lnAbsBetaRealFuel_eq_or (fuel : ℕ) {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsBetaRealFuel fuel a b p mode).1
        = roundVal p mode (Spec.lnAbsBeta (av : EReal) (bv : EReal)) ∨
      (lnAbsBetaRealFuel fuel a b p mode).1 = (nan, .eq) := by
  unfold Spec.lnAbsBeta
  by_cases hpole : (av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)
  · left
    have : (isNegInt a || isNegInt b) = true := by
      rw [Bool.or_eq_true, isNegInt_iff ha, isNegInt_iff hb]; exact hpole
    unfold lnAbsBetaRealFuel
    rw [ite_eq_left this, Spec.beta_coe_of_pole hpole, Option.map_none, roundVal_none]
  have hpole' : ¬ (isNegInt a || isNegInt b) = true := by
    rw [Bool.or_eq_true, isNegInt_iff ha, isNegInt_iff hb]; exact hpole
  by_cases hzero : av = 0 ∨ bv = 0
  · left
    have : (isZeroVal a || isZeroVal b) = true := by
      rw [Bool.or_eq_true, isZeroVal_iff ha, isZeroVal_iff hb]; exact hzero
    unfold lnAbsBetaRealFuel
    rw [ite_eq_right hpole', ite_eq_left this, Spec.beta_coe_of_zero hpole hzero,
      Option.map_some, Spec.lnAbsE_top, roundVal_top]
  have hzero' : ¬ (isZeroVal a || isZeroVal b) = true := by
    rw [Bool.or_eq_true, isZeroVal_iff ha, isZeroVal_iff hb]; exact hzero
  rw [Spec.beta_coe hpole hzero, Option.map_some]
  push Not at hzero
  by_cases hs : av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k
  · left
    obtain ⟨hle, k, hk⟩ := hs
    have : sumIsNonposInt a b = true := (sumIsNonposInt_iff ha hb).mpr ⟨hle, k, hk⟩
    unfold lnAbsBetaRealFuel
    rw [ite_eq_right hpole', ite_eq_right hzero', ite_eq_left this,
      gamma_eq_zero_of_nonpos_int hle hk, div_zero, Spec.lnAbsE_zero, roundVal_bot]
  · rw [Spec.lnAbsE_coe (beta_ne_zero hzero.1 hzero.2 (fun h => hpole (Or.inl h))
      (fun h => hpole (Or.inr h)) hs)]
    rcases lnAbsBetaRealFuel_main fuel ha hb hzero.1 hzero.2 (fun h => hpole (Or.inl h))
      (fun h => hpole (Or.inr h)) hs p mode with h | h
    · exact Or.inr h
    · exact Or.inl h.1

/-- `lnAbsBetaInfinite` is the rounding of `ln |B(+∞, y)|` for a real `y`. -/
theorem lnAbsBetaInfinite_eq {y : AzFloat} {yv : ℝ} (hy : y.toVal = some (yv : EReal)) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    lnAbsBetaInfinite y
      = roundVal p mode ((if 0 < yv then some (0 : EReal) else none).map Spec.lnAbsE) := by
  unfold lnAbsBetaInfinite
  by_cases h : 0 < yv
  · rw [ite_eq_left ((lt_eq_true_iff toVal_zero' hy).mpr h), ite_eq_left h, Option.map_some,
      ← EReal.coe_zero, Spec.lnAbsE_zero, roundVal_bot]
  · rw [ite_eq_right (fun h' => h ((lt_eq_true_iff toVal_zero' hy).mp h')), ite_eq_right h,
      Option.map_none, roundVal_none]

/-- **`ln |B|` is correctly rounded, or the fuel ran out.** -/
theorem lnAbsBetaPrecRoundFuel_eq_or (fuel : ℕ) (a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsBetaPrecRoundFuel fuel a b p mode).1 = liftVal₂ Spec.lnAbsBeta a b p mode ∨
      (lnAbsBetaPrecRoundFuel fuel a b p mode).1 = (nan, .eq) := by
  have hz : zero.toVal = some ((0 : ℝ) : EReal) := toVal_zero'
  cases a with
  | nan => left; cases b <;> rfl
  | infinity sa =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sa <;> cases sb <;>
        simp [lnAbsBetaPrecRoundFuel, lnAbsBetaInfinite, liftVal₂, Spec.lnAbsBeta,
          Spec.beta_bot_left, Spec.beta_bot_right, Spec.beta_top_top, lt, partialCompare,
          ← EReal.coe_zero, Spec.lnAbsE_zero]
    | zero =>
      left
      cases sa
      · simp [lnAbsBetaPrecRoundFuel, liftVal₂, Spec.lnAbsBeta, Spec.beta_bot_left]
      · simp only [lnAbsBetaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          hz, Spec.lnAbsBeta, Spec.beta_top_coe]
        exact lnAbsBetaInfinite_eq hz p mode
    | finite s e q m hv =>
      left
      cases sa
      · simp [lnAbsBetaPrecRoundFuel, liftVal₂, Spec.lnAbsBeta, Spec.beta_bot_left]
      · simp only [lnAbsBetaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          toVal_finite, Spec.lnAbsBeta, Spec.beta_top_coe]
        exact lnAbsBetaInfinite_eq (toVal_finite s e q m hv) p mode
  | zero =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sb
      · simp [lnAbsBetaPrecRoundFuel, liftVal₂, Spec.lnAbsBeta, Spec.beta_bot_right]
      · simp only [lnAbsBetaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          hz, Spec.lnAbsBeta, Spec.beta_coe_top]
        exact lnAbsBetaInfinite_eq hz p mode
    | zero =>
      simp only [lnAbsBetaPrecRoundFuel, liftVal₂, hz, Option.bind_some]
      exact lnAbsBetaRealFuel_eq_or fuel hz hz p mode
    | finite s e q m hv =>
      simp only [lnAbsBetaPrecRoundFuel, liftVal₂, hz, toVal_finite, Option.bind_some]
      exact lnAbsBetaRealFuel_eq_or fuel hz (toVal_finite s e q m hv) p mode
  | finite s e q m hv =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sb
      · simp [lnAbsBetaPrecRoundFuel, liftVal₂, Spec.lnAbsBeta, Spec.beta_bot_right]
      · simp only [lnAbsBetaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          toVal_finite, Spec.lnAbsBeta, Spec.beta_coe_top]
        exact lnAbsBetaInfinite_eq (toVal_finite s e q m hv) p mode
    | zero =>
      simp only [lnAbsBetaPrecRoundFuel, liftVal₂, hz, toVal_finite, Option.bind_some]
      exact lnAbsBetaRealFuel_eq_or fuel (toVal_finite s e q m hv) hz p mode
    | finite s' e' q' m' hv' =>
      simp only [lnAbsBetaPrecRoundFuel, liftVal₂, toVal_finite, Option.bind_some]
      exact lnAbsBetaRealFuel_eq_or fuel (toVal_finite s e q m hv) (toVal_finite s' e' q' m' hv')
        p mode

/-- `lnAbsBetaRealFuel` on finite arguments: the special values with the sign `true`, or the
general case. -/
theorem lnAbsBetaRealFuel_eq_or_gen (fuel : ℕ) {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal)) (hb : b.toVal = some (bv : EReal)) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnAbsBetaRealFuel fuel a b p mode
        = (roundVal p mode (Spec.lnAbsBeta (av : EReal) (bv : EReal)), true) ∨
      (av ≠ 0 ∧ bv ≠ 0 ∧ ¬ (av < 0 ∧ ∃ k : ℤ, av = k) ∧ ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k) ∧
        ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)) := by
  unfold Spec.lnAbsBeta
  by_cases hpole : (av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)
  · left
    have : (isNegInt a || isNegInt b) = true := by
      rw [Bool.or_eq_true, isNegInt_iff ha, isNegInt_iff hb]; exact hpole
    unfold lnAbsBetaRealFuel
    rw [ite_eq_left this, Spec.beta_coe_of_pole hpole, Option.map_none, roundVal_none]
  have hpole' : ¬ (isNegInt a || isNegInt b) = true := by
    rw [Bool.or_eq_true, isNegInt_iff ha, isNegInt_iff hb]; exact hpole
  by_cases hzero : av = 0 ∨ bv = 0
  · left
    have : (isZeroVal a || isZeroVal b) = true := by
      rw [Bool.or_eq_true, isZeroVal_iff ha, isZeroVal_iff hb]; exact hzero
    unfold lnAbsBetaRealFuel
    rw [ite_eq_right hpole', ite_eq_left this, Spec.beta_coe_of_zero hpole hzero,
      Option.map_some, Spec.lnAbsE_top, roundVal_top]
  have hzero' : ¬ (isZeroVal a || isZeroVal b) = true := by
    rw [Bool.or_eq_true, isZeroVal_iff ha, isZeroVal_iff hb]; exact hzero
  push Not at hzero
  by_cases hs : av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k
  · left
    obtain ⟨hle, k, hk⟩ := hs
    have : sumIsNonposInt a b = true := (sumIsNonposInt_iff ha hb).mpr ⟨hle, k, hk⟩
    unfold lnAbsBetaRealFuel
    rw [ite_eq_right hpole', ite_eq_right hzero', ite_eq_left this,
      Spec.beta_coe hpole (by push Not; exact hzero), Option.map_some,
      gamma_eq_zero_of_nonpos_int hle hk, div_zero, Spec.lnAbsE_zero, roundVal_bot]
  · exact Or.inr ⟨hzero.1, hzero.2, fun h => hpole (Or.inl h), fun h => hpole (Or.inr h), hs⟩

/-- **`ln |B|` at the special values, with the sign `true`, or the general case** of finite
arguments off the special values. -/
theorem lnAbsBetaPrecRoundFuel_eq_or_gen (fuel : ℕ) (a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnAbsBetaPrecRoundFuel fuel a b p mode = (liftVal₂ Spec.lnAbsBeta a b p mode, true) ∨
      ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧ b.toVal = some (bv : EReal) ∧
        av ≠ 0 ∧ bv ≠ 0 ∧ ¬ (av < 0 ∧ ∃ k : ℤ, av = k) ∧ ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k) ∧
        ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k) := by
  have key : ∀ {a b : AzFloat} {av bv : ℝ}, a.toVal = some (av : EReal) →
      b.toVal = some (bv : EReal) →
      lnAbsBetaPrecRoundFuel fuel a b p mode = lnAbsBetaRealFuel fuel a b p mode →
      (lnAbsBetaPrecRoundFuel fuel a b p mode = (liftVal₂ Spec.lnAbsBeta a b p mode, true) ∨
        ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧ b.toVal = some (bv : EReal) ∧
          av ≠ 0 ∧ bv ≠ 0 ∧ ¬ (av < 0 ∧ ∃ k : ℤ, av = k) ∧ ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k) ∧
          ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)) := by
    intro a b av bv ha hb heq
    rw [heq]
    rcases lnAbsBetaRealFuel_eq_or_gen fuel ha hb p mode with h | h
    · left
      rw [h, liftVal₂, ha, hb, Option.bind_some, Option.bind_some]
    · exact Or.inr ⟨av, bv, ha, hb, h⟩
  have hz : zero.toVal = some ((0 : ℝ) : EReal) := toVal_zero'
  cases a with
  | nan => left; cases b <;> rfl
  | infinity sa =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sa <;> cases sb <;>
        simp [lnAbsBetaPrecRoundFuel, lnAbsBetaInfinite, liftVal₂, Spec.lnAbsBeta,
          Spec.beta_bot_left, Spec.beta_bot_right, Spec.beta_top_top, lt, partialCompare,
          ← EReal.coe_zero, Spec.lnAbsE_zero]
    | zero =>
      left
      cases sa
      · simp [lnAbsBetaPrecRoundFuel, liftVal₂, Spec.lnAbsBeta, Spec.beta_bot_left]
      · simp only [lnAbsBetaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          hz, Spec.lnAbsBeta, Spec.beta_top_coe]
        rw [lnAbsBetaInfinite_eq hz p mode]
    | finite s e q m hv =>
      left
      cases sa
      · simp [lnAbsBetaPrecRoundFuel, liftVal₂, Spec.lnAbsBeta, Spec.beta_bot_left]
      · simp only [lnAbsBetaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          toVal_finite, Spec.lnAbsBeta, Spec.beta_top_coe]
        rw [lnAbsBetaInfinite_eq (toVal_finite s e q m hv) p mode]
  | zero =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sb
      · simp [lnAbsBetaPrecRoundFuel, liftVal₂, Spec.lnAbsBeta, Spec.beta_bot_right]
      · simp only [lnAbsBetaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          hz, Spec.lnAbsBeta, Spec.beta_coe_top]
        rw [lnAbsBetaInfinite_eq hz p mode]
    | zero =>
      exact key hz hz rfl
    | finite s e q m hv =>
      exact key hz (toVal_finite s e q m hv) rfl
  | finite s e q m hv =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sb
      · simp [lnAbsBetaPrecRoundFuel, liftVal₂, Spec.lnAbsBeta, Spec.beta_bot_right]
      · simp only [lnAbsBetaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          toVal_finite, Spec.lnAbsBeta, Spec.beta_coe_top]
        rw [lnAbsBetaInfinite_eq (toVal_finite s e q m hv) p mode]
    | zero =>
      exact key (toVal_finite s e q m hv) hz rfl
    | finite s' e' q' m' hv' =>
      exact key (toVal_finite s e q m hv) (toVal_finite s' e' q' m' hv') rfl


/-- On arguments with real values the driver is `lnAbsBetaRealFuel`. -/
theorem lnAbsBetaPrecRoundFuel_eq_real (fuel : ℕ) {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal)) (hb : b.toVal = some (bv : EReal)) (p : ℕ)
    (mode : RoundingMode) :
    lnAbsBetaPrecRoundFuel fuel a b p mode = lnAbsBetaRealFuel fuel a b p mode := by
  cases a with
  | nan => simp at ha
  | infinity s => cases s <;> simp at ha
  | zero =>
    cases b with
    | nan => simp at hb
    | infinity s => cases s <;> simp at hb
    | zero => rfl
    | finite _ _ _ _ _ => rfl
  | finite _ _ _ _ _ =>
    cases b with
    | nan => simp at hb
    | infinity s => cases s <;> simp at hb
    | zero => rfl
    | finite _ _ _ _ _ => rfl

/-- **The sign component is the sign of `B(a, b)`** whenever the value is not `NaN`, at finite
arguments where `B` is finite and not `0`. -/
theorem lnAbsBetaPrecRoundFuel_sign (fuel : ℕ) {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (ha0 : av ≠ 0) (hb0 : bv ≠ 0)
    (hpa : ¬ (av < 0 ∧ ∃ k : ℤ, av = k)) (hpb : ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k))
    (hs : ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsBetaPrecRoundFuel fuel a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsBetaPrecRoundFuel fuel a b p mode).2 = true
      ↔ 0 < Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) := by
  rw [lnAbsBetaPrecRoundFuel_eq_real fuel ha hb] at hne ⊢
  rcases lnAbsBetaRealFuel_main fuel ha hb ha0 hb0 hpa hpb hs p mode with h | h
  · exact absurd h hne
  · exact h.2

/-! ### `ln B` without the absolute value -/

namespace Spec

/-- `ln B` on the extended reals: the logarithm of `Spec.beta` (`NaN` where `B < 0`). -/
noncomputable def lnBeta (a b : EReal) : Option EReal := (beta a b).bind log

/-- `Spec.beta` is never `−∞`. -/
theorem beta_ne_bot (a b : EReal) : beta a b ≠ some ⊥ := by
  unfold beta
  split_ifs <;> simp

/-- Where `B` is not a negative real, `ln |B|` and `ln B` agree. -/
theorem lnAbsBeta_eq_lnBeta {a b : EReal} (h : ∀ v : ℝ, beta a b = some (v : EReal) → 0 ≤ v) :
    lnAbsBeta a b = lnBeta a b := by
  unfold lnAbsBeta lnBeta
  have hb := beta_ne_bot a b
  cases ho : beta a b with
  | none => rfl
  | some e =>
    rw [ho] at hb h
    induction e using EReal.rec with
    | bot => exact absurd rfl hb
    | top => simp [lnAbsE_top]
    | coe v =>
      have hv := h v rfl
      rcases hv.eq_or_lt with h0 | hpos
      · subst h0
        rw [Option.map_some, Option.bind_some, lnAbsE_zero, EReal.coe_zero, log_zero]
      · rw [Option.map_some, Option.bind_some, lnAbsE_coe hpos.ne', log_coe v hpos,
          abs_of_pos hpos]

/-- A negative value of `Spec.beta` comes from finite arguments off the special values. -/
theorem beta_neg_cases {a b : EReal} {v : ℝ} (h : beta a b = some (v : EReal)) (hv : v < 0) :
    ∃ av bv : ℝ, a = av ∧ b = bv ∧ av ≠ 0 ∧ bv ≠ 0 ∧ ¬ (av < 0 ∧ ∃ k : ℤ, av = k) ∧
      ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k) ∧ ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k) ∧
      v = Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) := by
  have hne0 : (v : EReal) ≠ 0 := by
    rw [← EReal.coe_zero, Ne, EReal.coe_eq_coe_iff]; exact hv.ne
  induction a using EReal.rec with
  | bot => rw [beta_bot_left] at h; exact absurd h (by simp)
  | top =>
    induction b using EReal.rec with
    | bot => rw [beta_bot_right] at h; exact absurd h (by simp)
    | top => rw [beta_top_top, Option.some.injEq] at h; exact absurd h.symm hne0
    | coe bv =>
      rw [beta_top_coe] at h
      split_ifs at h
      rw [Option.some.injEq] at h
      exact absurd h.symm hne0
  | coe av =>
    induction b using EReal.rec with
    | bot => rw [beta_bot_right] at h; exact absurd h (by simp)
    | top =>
      rw [beta_coe_top] at h
      split_ifs at h
      rw [Option.some.injEq] at h
      exact absurd h.symm hne0
    | coe bv =>
      by_cases hpole : (av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)
      · rw [beta_coe_of_pole hpole] at h; exact absurd h (by simp)
      by_cases hzero : av = 0 ∨ bv = 0
      · rw [beta_coe_of_zero hpole hzero, Option.some.injEq] at h
        exact absurd h (EReal.coe_ne_top v).symm
      rw [beta_coe hpole hzero, Option.some.injEq, EReal.coe_eq_coe_iff] at h
      push Not at hzero
      refine ⟨av, bv, rfl, rfl, hzero.1, hzero.2, fun h' => hpole (Or.inl h'),
        fun h' => hpole (Or.inr h'), ?_, h.symm⟩
      rintro ⟨hle, k, hk⟩
      rw [gamma_eq_zero_of_nonpos_int hle hk, div_zero] at h
      exact hv.ne h.symm

end Spec

/-- **`ln B` is correctly rounded, or the fuel ran out** (`NaN` where `B < 0`). -/
theorem lnBetaPrecRoundFuel_eq_or (fuel : ℕ) (a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnBetaPrecRoundFuel fuel a b p mode = liftVal₂ Spec.lnBeta a b p mode ∨
      lnBetaPrecRoundFuel fuel a b p mode = (nan, .eq) := by
  unfold lnBetaPrecRoundFuel
  dsimp only
  by_cases hs : (lnAbsBetaPrecRoundFuel fuel a b p mode).2 = true
  · rw [ite_eq_left hs]
    rcases lnAbsBetaPrecRoundFuel_eq_or fuel a b p mode with h | h
    · by_cases hnan : (lnAbsBetaPrecRoundFuel fuel a b p mode).1 = (nan, .eq)
      · exact Or.inr hnan
      left
      rw [h]
      unfold liftVal₂
      cases ha : a.toVal with
      | none => rfl
      | some x =>
        cases hb : b.toVal with
        | none => rfl
        | some y =>
          simp only [Option.bind_some]
          congr 1
          refine Spec.lnAbsBeta_eq_lnBeta fun v hv => ?_
          by_contra hneg
          push Not at hneg
          obtain ⟨av, bv, rfl, rfl, ha0, hb0, hpa, hpb, hsum, rfl⟩ := Spec.beta_neg_cases hv hneg
          have := (lnAbsBetaPrecRoundFuel_sign fuel ha hb ha0 hb0 hpa hpb hsum p mode hnan).mp hs
          linarith
    · exact Or.inr h
  · rw [ite_eq_right hs]
    exact Or.inr rfl

/-! ### The public functions -/

/-- **`ln |B|` is correctly rounded, or the fuel ran out.** -/
theorem lnAbsBetaPrecRound_eq_or (a b : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsBetaPrecRound a b p mode).1 = liftVal₂ Spec.lnAbsBeta a b p mode ∨
      (lnAbsBetaPrecRound a b p mode).1 = (nan, .eq) :=
  lnAbsBetaPrecRoundFuel_eq_or (gammaFuel p) a b p mode

/-- **The sign component is the sign of `B(a, b)`** whenever the value is not `NaN`, at finite
arguments where `B` is finite and not `0`. -/
theorem lnAbsBetaPrecRound_sign {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (ha0 : av ≠ 0) (hb0 : bv ≠ 0)
    (hpa : ¬ (av < 0 ∧ ∃ k : ℤ, av = k)) (hpb : ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k))
    (hs : ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsBetaPrecRound a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsBetaPrecRound a b p mode).2 = true
      ↔ 0 < Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) :=
  lnAbsBetaPrecRoundFuel_sign (gammaFuel p) ha hb ha0 hb0 hpa hpb hs p mode hne

/-- **`ln B` is correctly rounded, or the fuel ran out** (`NaN` where `B < 0`). -/
theorem lnBetaPrecRound_eq_or (a b : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnBetaPrecRound a b p mode = liftVal₂ Spec.lnBeta a b p mode ∨
      lnBetaPrecRound a b p mode = (nan, .eq) :=
  lnBetaPrecRoundFuel_eq_or (gammaFuel p) a b p mode

/-! ### The loop with a sign as a Ziv loop -/

/-- The value of a level of `lnAbsLoop` is the answer of `roundingPossible` on the bracket of
the enclosure. -/
theorem lnAbsStep_fst (core : ℕ → Option (Bool × Encl)) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (w : ℕ) :
    (lnAbsStep core p mode w).map Prod.fst
      = roundingPossible (lnAbsGammaApproxOf ((core w).map Prod.snd) w).1
        (lnAbsGammaApproxOf ((core w).map Prod.snd) w).2 p mode := by
  unfold lnAbsStep
  cases hc : core w with
  | none => exact (roundingPossible_negSwapApprox_dummy false p mode).symm
  | some t =>
    obtain ⟨neg, L⟩ := t
    show ((roundingPossible (lnGammaApproxOf L w).1 (lnGammaApproxOf L w).2 p mode).map
      fun r => (r, !neg)).map Prod.fst = roundingPossible (lnGammaApproxOf L w).1
        (lnGammaApproxOf L w).2 p mode
    cases roundingPossible (lnGammaApproxOf L w).1 (lnGammaApproxOf L w).2 p mode <;> rfl

/-- **The value of `lnAbsLoop` is Ziv's loop** on the brackets of the enclosures. -/
theorem lnAbsLoop_fst (core : ℕ → Option (Bool × Encl)) (p : ℕ) [NeZero p]
    (mode : RoundingMode) : ∀ fuel w : ℕ,
    (lnAbsLoop core p mode fuel w).1
      = zivLoop (fun w => lnAbsGammaApproxOf ((core w).map Prod.snd) w) p mode fuel w
  | 0, w => by
    have h := lnAbsStep_fst core p mode w
    rw [lnAbsLoop, zivLoop.eq_def]
    dsimp only
    rw [← h]
    cases lnAbsStep core p mode w <;> rfl
  | fuel + 1, w => by
    have h := lnAbsStep_fst core p mode w
    rw [lnAbsLoop, zivLoop.eq_def]
    dsimp only
    rw [← h]
    cases hs : lnAbsStep core p mode w with
    | none => exact lnAbsLoop_fst core p mode fuel (2 * w)
    | some r => rfl

theorem roundVal_coe_ne_nan (p : ℕ) [NeZero p] (mode : RoundingMode) (r : ℝ) :
    roundVal p mode (some (r : EReal)) ≠ (nan, .eq) := by
  intro h
  have := (roundVal_coe p mode r).1
  rw [h] at this
  exact absurd this (by simp)

/-- **A loop with a sign whose enclosures converge returns the correct rounding for every
large enough fuel**, at a value that is no rounding boundary. -/
theorem lnAbsLoop_eventually {core : ℕ → Option (Bool × Encl)} {v : ℝ} (p : ℕ) [NeZero p]
    (mode : RoundingMode) {w₀ : ℕ} (hw₀ : 0 < w₀)
    (hcore : ∀ w, w₀ ≤ w → ∀ neg L, core w = some (neg, L) → IsEncl L v)
    (hconv : ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ᶠ w in Filter.atTop, ∃ neg L, core w = some (neg, L) ∧ AEncl L v (ε w))
    (hvB : ((v : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel →
      (lnAbsLoop core p mode fuel w₀).1 = roundVal p mode (some (v : EReal)) := by
  obtain ⟨ε, hε, hev⟩ := hconv
  have hbc : BracketConv (fun w => lnAbsGammaApproxOf ((core w).map Prod.snd) w) v :=
    lnAbsGammaApproxOf_bracketConv ⟨ε, hε, hev.mono fun w ⟨neg, L, hc, hL⟩ =>
      ⟨L, by rw [hc]; rfl, hL⟩⟩
  obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode _ hbc (ne_zero_of_not_mem_floatSet hvB) hvB
    w₀ hw₀ (fun w hw => (lnAbsGammaApproxOf_valid_or_none (fun b hb => by
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hb
      exact hcore w hw t.1 t.2 ht) w p mode).imp_left
        fun ⟨lv, hv, h1, h2, h3, h4, _⟩ => ⟨lv, hv, h1, h2, h3, h4⟩)
  exact ⟨F, fun fuel hfuel => by rw [lnAbsLoop_fst]; exact hF fuel hfuel⟩

/-! ### The specifications -/

/-- **`ln |B|` in the general case is correctly rounded for every large enough fuel**, when
the value is no rounding boundary. -/
theorem lnAbsBetaRealFuel_eventually {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal)) (hb : b.toVal = some (bv : EReal)) (ha0 : av ≠ 0)
    (hb0 : bv ≠ 0) (hpa : ¬ (av < 0 ∧ ∃ k : ℤ, av = k)) (hpb : ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k))
    (hs : ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hvB : ((Real.log |Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)| : ℝ) : EReal)
      ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → (lnAbsBetaRealFuel fuel a b p mode).1 = roundVal p mode
      (some ((Real.log |Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)| : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  have hpole : ¬ (isNegInt a || isNegInt b) = true := by
    rw [Bool.or_eq_true, isNegInt_iff ha, isNegInt_iff hb]
    exact fun h => h.elim hpa hpb
  have hzero : ¬ (isZeroVal a || isZeroVal b) = true := by
    rw [Bool.or_eq_true, isZeroVal_iff ha, isZeroVal_iff hb]
    exact fun h => h.elim ha0 hb0
  have hsum : ¬ sumIsNonposInt a b = true := by rw [sumIsNonposInt_iff ha hb]; exact hs
  by_cases hone : isOneVal b = true ∨ isOneVal a = true
  · refine ⟨0, fun fuel _ => ?_⟩
    rcases lnAbsBetaRealFuel_main fuel ha hb ha0 hb0 hpa hpb hs p mode with h | h
    · -- with an argument `1` the value is a logarithm: no loop
      exfalso
      unfold lnAbsBetaRealFuel at h
      rw [ite_eq_right hpole, ite_eq_right hzero, ite_eq_right hsum, ite_eq_right hp] at h
      by_cases hb1 : isOneVal b = true
      · rw [ite_eq_left hb1] at h
        have := negLnAbs_eq ha ha0 p mode
        rw [show (negLnAbs a p mode, lt zero a).1 = negLnAbs a p mode from rfl] at h
        rw [h] at this
        exact roundVal_coe_ne_nan p mode _ this.symm
      · have ha1 : isOneVal a = true := hone.resolve_left hb1
        rw [ite_eq_right hb1, ite_eq_left ha1] at h
        have := negLnAbs_eq hb hb0 p mode
        rw [show (negLnAbs b p mode, lt zero b).1 = negLnAbs b p mode from rfl] at h
        rw [h] at this
        exact roundVal_coe_ne_nan p mode _ this.symm
    · exact h.1
  · push Not at hone
    have hA := beta_arg_cases ha0 hpa
    have hB := beta_arg_cases hb0 hpb
    have hS := beta_sum_cases hs
    obtain ⟨F, hF⟩ := lnAbsLoop_eventually (v := Real.log |Real.Gamma av * Real.Gamma bv
        / Real.Gamma (av + bv)|) p mode
      (core := fun w => lnAbsBetaCore a b (w + betaBits (expOf a) (expOf b)
        ((if expOf a ≤ expOf b then expOf b else expOf a) + 1)) w)
      (w₀ := max 64 (p + 32)) (by omega)
      (fun w hw neg L hc => by
        obtain ⟨hpos, hL⟩ := lnAbsBetaCore_spec ha hb (by omega) (le_trans (le_max_left _ _) hw) hc
        rwa [sign_mul_eq_abs hpos] at hL)
      (by
        obtain ⟨E, hE, hev⟩ := lnAbsBetaEncl_conv_log (argConv_float ha hA)
          (argConv_float hb hB) (argConv_sum ha hb hS)
          (fun W σ k E hW hF => by
            have : NeZero W := ⟨by omega⟩
            exact gammaFloatFrac_spec ha hF)
          (fun W σ k E hW hF => by
            have : NeZero W := ⟨by omega⟩
            exact gammaFloatFrac_spec hb hF)
          (fun W σ k E hW hF => by
            have : NeZero W := ⟨by omega⟩
            exact betaSumFrac_spec ha hb hF)
          (expOf a) (expOf b) ((if expOf a ≤ expOf b then expOf b else expOf a) + 1)
          (betaBits (expOf a) (expOf b) ((if expOf a ≤ expOf b then expOf b else expOf a) + 1))
        exact ⟨E, hE, hev⟩)
      hvB
    refine ⟨F, fun fuel hfuel => ?_⟩
    have := hF fuel hfuel
    unfold lnAbsBetaRealFuel
    rw [ite_eq_right hpole, ite_eq_right hzero, ite_eq_right hsum, ite_eq_right hp,
      ite_eq_right hone.1, ite_eq_right hone.2]
    exact this

/-- **The specification of `ln |B|`** (the value component; `ZivSpec`): sound at every fuel,
and complete in the limit of the fuel wherever the value is no rounding boundary.  No value
is known to be irrational. -/
theorem lnAbsBetaPrecRoundFuel_zivSpec :
    ZivSpec
      (fun xy : AzFloat × AzFloat => xy.1.toVal.bind fun a => xy.2.toVal.bind fun b =>
        Spec.lnAbsBeta a b)
      (fun fuel xy p mode => (lnAbsBetaPrecRoundFuel fuel xy.1 xy.2 p mode).1) ∅ ∅ where
  sound := fun fuel xy p _ mode => lnAbsBetaPrecRoundFuel_eq_or fuel xy.1 xy.2 p mode
  complete := fun xy p _ mode hB => by
    by_cases hgen : ∃ av bv : ℝ, xy.1.toVal = some (av : EReal) ∧
        xy.2.toVal = some (bv : EReal) ∧ av ≠ 0 ∧ bv ≠ 0 ∧ ¬ (av < 0 ∧ ∃ k : ℤ, av = k) ∧
        ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k) ∧ ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)
    · obtain ⟨av, bv, ha, hb, ha0, hb0, hpa, hpb, hs⟩ := hgen
      have hval : (xy.1.toVal.bind fun a => xy.2.toVal.bind fun b => Spec.lnAbsBeta a b)
          = some ((Real.log |Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)| : ℝ)
            : EReal) := by
        rw [ha, hb, Option.bind_some, Option.bind_some]
        unfold Spec.lnAbsBeta
        rw [Spec.beta_coe (fun h => h.elim hpa hpb) (fun h => h.elim ha0 hb0), Option.map_some,
          Spec.lnAbsE_coe (beta_ne_zero ha0 hb0 hpa hpb hs)]
      obtain ⟨F, hF⟩ := lnAbsBetaRealFuel_eventually ha hb ha0 hb0 hpa hpb hs p mode
        (hB _ hval)
      refine ⟨F, fun fuel hfuel => ?_⟩
      show (lnAbsBetaPrecRoundFuel fuel xy.1 xy.2 p mode).1 = _
      rw [lnAbsBetaPrecRoundFuel_eq_real fuel ha hb, hval]
      exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases lnAbsBetaPrecRoundFuel_eq_or_gen fuel xy.1 xy.2 p mode with h | h
      · show (lnAbsBetaPrecRoundFuel fuel xy.1 xy.2 p mode).1 = _
        rw [h]
        rfl
      · exact absurd h hgen
  dyadic := fun xy h => absurd h (Set.notMem_empty _)
  nondyadic := fun xy h => absurd h (Set.notMem_empty _)
  correct := fun xy h => absurd (h.elim id id) (Set.notMem_empty _)

/-- **The specification of `ln B`** (`ZivSpec`): sound at every fuel, and complete in the
limit of the fuel wherever the value is no rounding boundary (`NaN` at every fuel where
`B < 0`). -/
theorem lnBetaPrecRoundFuel_zivSpec :
    ZivSpec
      (fun xy : AzFloat × AzFloat => xy.1.toVal.bind fun a => xy.2.toVal.bind fun b =>
        Spec.lnBeta a b)
      (fun fuel xy p mode => lnBetaPrecRoundFuel fuel xy.1 xy.2 p mode) ∅ ∅ where
  sound := fun fuel xy p _ mode => lnBetaPrecRoundFuel_eq_or fuel xy.1 xy.2 p mode
  complete := fun xy p _ mode hB => by
    by_cases hgen : ∃ av bv : ℝ, xy.1.toVal = some (av : EReal) ∧
        xy.2.toVal = some (bv : EReal) ∧ av ≠ 0 ∧ bv ≠ 0 ∧ ¬ (av < 0 ∧ ∃ k : ℤ, av = k) ∧
        ¬ (bv < 0 ∧ ∃ k : ℤ, bv = k) ∧ ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)
    · obtain ⟨av, bv, ha, hb, ha0, hb0, hpa, hpb, hs⟩ := hgen
      have hBne := beta_ne_zero ha0 hb0 hpa hpb hs
      have hbeta := Spec.beta_coe (xv := av) (yv := bv) (fun h => h.elim hpa hpb)
        (fun h => h.elim ha0 hb0)
      rcases lt_or_gt_of_ne hBne with hneg | hpos
      · -- `B < 0`: `NaN` at every fuel
        refine ⟨0, fun fuel _ => ?_⟩
        have hval : (xy.1.toVal.bind fun a => xy.2.toVal.bind fun b => Spec.lnBeta a b)
            = none := by
          rw [ha, hb, Option.bind_some, Option.bind_some]
          unfold Spec.lnBeta
          rw [hbeta, Option.bind_some, Spec.log_coe_neg _ hneg]
        show lnBetaPrecRoundFuel fuel xy.1 xy.2 p mode = _
        rw [hval, roundVal_none]
        unfold lnBetaPrecRoundFuel
        dsimp only
        rw [lnAbsBetaPrecRoundFuel_eq_real fuel ha hb]
        rcases lnAbsBetaRealFuel_main fuel ha hb ha0 hb0 hpa hpb hs p mode with h | ⟨-, h2⟩
        · by_cases hsgn : (lnAbsBetaRealFuel fuel xy.1 xy.2 p mode).2 = true
          · rw [ite_eq_left hsgn]
            exact h
          · rw [ite_eq_right hsgn]
        · rw [ite_eq_right fun h' => absurd (h2.mp h') (not_lt.mpr hneg.le)]
      · -- `B > 0`
        have e : Real.log |Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)|
            = Real.log (Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)) := by
          rw [abs_of_pos hpos]
        have hval : (xy.1.toVal.bind fun a => xy.2.toVal.bind fun b => Spec.lnBeta a b)
            = some ((Real.log |Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)| : ℝ)
              : EReal) := by
          rw [ha, hb, Option.bind_some, Option.bind_some, e]
          unfold Spec.lnBeta
          rw [hbeta, Option.bind_some, Spec.log_coe _ hpos]
        obtain ⟨F, hF⟩ := lnAbsBetaRealFuel_eventually ha hb ha0 hb0 hpa hpb hs p mode
          (hB _ hval)
        refine ⟨F, fun fuel hfuel => ?_⟩
        show lnBetaPrecRoundFuel fuel xy.1 xy.2 p mode = _
        rw [hval]
        unfold lnBetaPrecRoundFuel
        dsimp only
        rw [lnAbsBetaPrecRoundFuel_eq_real fuel ha hb]
        have h1 := hF fuel hfuel
        rcases lnAbsBetaRealFuel_main fuel ha hb ha0 hb0 hpa hpb hs p mode with h | ⟨-, h2⟩
        · rw [h1] at h
          exact absurd h (roundVal_coe_ne_nan p mode _)
        · rw [ite_eq_left (h2.mpr hpos), h1]
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases lnAbsBetaPrecRoundFuel_eq_or_gen fuel xy.1 xy.2 p mode with h | h
      · show lnBetaPrecRoundFuel fuel xy.1 xy.2 p mode = _
        unfold lnBetaPrecRoundFuel
        dsimp only
        rw [h]
        show liftVal₂ Spec.lnAbsBeta xy.1 xy.2 p mode = _
        unfold liftVal₂
        cases ha : xy.1.toVal with
        | none => rfl
        | some x =>
          cases hb : xy.2.toVal with
          | none => rfl
          | some y =>
            simp only [Option.bind_some]
            congr 1
            refine Spec.lnAbsBeta_eq_lnBeta fun v hv => ?_
            by_contra hneg
            push Not at hneg
            obtain ⟨av, bv, rfl, rfl, ha0, hb0, hpa, hpb, hsum, rfl⟩ :=
              Spec.beta_neg_cases hv hneg
            exact hgen ⟨av, bv, ha, hb, ha0, hb0, hpa, hpb, hsum⟩
      · exact absurd h hgen
  dyadic := fun xy h => absurd h (Set.notMem_empty _)
  nondyadic := fun xy h => absurd h (Set.notMem_empty _)
  correct := fun xy h => absurd (h.elim id id) (Set.notMem_empty _)

end Azurite.AzFloat
