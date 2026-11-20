/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaFloatRat
import Azurite.AzFloat.Equiv.BetaRat
import Azurite.AzFloat.Equiv.LnBetaRat
import Azurite.AzFloat.Equiv.Conversion

/-!
# Equivalence: `B`, `ln |B|` and `ln B` of a float and a rational

The functions are those of two rationals at the rational a finite float is, so their
specifications are those (`ZivSpec.floatRat`), with the values at `NaN` and `±∞` added:

* **`betaFloatRatPrecRoundFuel_zivSpec`**: sound at every fuel, complete in the limit of the
  fuel wherever the value is no rounding boundary, and correct at every fuel on the special
  values and where `betaRatSpecial` knows the value to be irrational;
* **`lnAbsBetaFloatRatPrecRoundFuel_zivSpec`** (the value component),
  **`lnAbsBetaFloatRatPrecRoundFuel_sign`** (the sign component is the sign of `B`),
  **`lnBetaFloatRatPrecRoundFuel_zivSpec`**;
* the corollaries `…_eq_or` at the default fuel.
-/

namespace Azurite.AzFloat

open Real

/-- **A function of a float and a rational that is a function of two rationals at the
rational the float is** has its specification, the arguments that are not finite being
exact. -/
theorem ZivSpec.floatRat {S : EReal → EReal → Option EReal}
    {fR : ℕ → AzRat × AzRat → ℕ → RoundingMode → AzFloat × Ordering} {D N : Set (AzRat × AzRat)}
    (h : ZivSpec (fun ab : AzRat × AzRat => S (((AzRat.toRat ab.1 : ℚ) : ℝ) : EReal)
      (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal)) fR D N)
    {fM : ℕ → AzFloat × AzRat → ℕ → RoundingMode → AzFloat × Ordering}
    (hsome : ∀ fuel (ab : AzFloat × AzRat) q p mode, ab.1.toAzRat? = some q →
      fM fuel ab p mode = fR fuel (q, ab.2) p mode)
    (hnone : ∀ fuel (ab : AzFloat × AzRat) (p : ℕ) [NeZero p] mode, ab.1.toAzRat? = none →
      fM fuel ab p mode = roundVal p mode
        (ab.1.toVal.bind fun x => S x (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal)))
    (hd : ∀ (ab : AzFloat × AzRat), ab.1.toAzRat? = none → ∀ v : ℝ,
      (ab.1.toVal.bind fun x => S x (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal)) = some (v : EReal) →
      IsDyadic v) :
    ZivSpec (fun ab : AzFloat × AzRat =>
        ab.1.toVal.bind fun x => S x (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal)) fM
      {ab | ∀ q, ab.1.toAzRat? = some q → (q, ab.2) ∈ D}
      {ab | ∃ q, ab.1.toAzRat? = some q ∧ (q, ab.2) ∈ N} := by
  have hval : ∀ (ab : AzFloat × AzRat) q, ab.1.toAzRat? = some q →
      (ab.1.toVal.bind fun x => S x (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal))
        = S (((AzRat.toRat q : ℚ) : ℝ) : EReal) (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal) :=
    fun ab q hq => by rw [toVal_of_toAzRat? _ _ hq, Option.bind_some]
  refine ⟨fun fuel ab p _ mode => ?_, fun ab p _ mode hB => ?_, fun ab hab v hv => ?_,
    fun ab hab => ?_, fun ab hab fuel p _ mode => ?_⟩
  · cases hq : ab.1.toAzRat? with
    | none => exact Or.inl (hnone fuel ab p mode hq)
    | some q =>
      rw [hsome fuel ab q p mode hq, hval ab q hq]
      exact h.sound fuel (q, ab.2) p mode
  · cases hq : ab.1.toAzRat? with
    | none => exact ⟨0, fun fuel _ => hnone fuel ab p mode hq⟩
    | some q =>
      rw [hval ab q hq] at hB ⊢
      obtain ⟨F, hF⟩ := h.complete (q, ab.2) p mode hB
      exact ⟨F, fun fuel hfuel => by rw [hsome fuel ab q p mode hq]; exact hF fuel hfuel⟩
  · cases hq : ab.1.toAzRat? with
    | none => exact hd ab hq v hv
    | some q =>
      rw [hval ab q hq] at hv
      exact h.dyadic (q, ab.2) (hab q hq) v hv
  · obtain ⟨q, hq, hN⟩ := hab
    rw [hval ab q hq]
    exact h.nondyadic (q, ab.2) hN
  · cases hq : ab.1.toAzRat? with
    | none => exact hnone fuel ab p mode hq
    | some q =>
      rw [hsome fuel ab q p mode hq, hval ab q hq]
      refine h.correct (q, ab.2) ?_ fuel p mode
      rcases hab with hD | ⟨q', hq', hN⟩
      · exact Or.inl (hD q hq)
      · rw [hq, Option.some.injEq] at hq'
        subst hq'
        exact Or.inr hN

/-- A specification holds on smaller sets of known arguments. -/
theorem ZivSpec.mono {α : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} {D N D' N' : Set α}
    (h : ZivSpec val f D N) (hD : D' ⊆ D) (hN : N' ⊆ N) : ZivSpec val f D' N' where
  sound := h.sound
  complete := h.complete
  dyadic := fun x hx => h.dyadic x (hD hx)
  nondyadic := fun x hx => h.nondyadic x (hN hx)
  correct := fun x hx => h.correct x (hx.imp (fun h' => hD h') fun h' => hN h')

/-- The rational a finite float is has its value. -/
theorem toRat_of_toAzRat? {a : AzFloat} {q : AzRat} (hq : a.toAzRat? = some q) {av : ℝ}
    (ha : a.toVal = some (av : EReal)) : ((AzRat.toRat q : ℚ) : ℝ) = av := by
  have := toVal_of_toAzRat? a q hq
  rw [ha, Option.some.injEq, EReal.coe_eq_coe_iff] at this
  exact this.symm

/-- A float with a real value is a rational. -/
theorem exists_toAzRat? {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) :
    ∃ q, a.toAzRat? = some q ∧ ((AzRat.toRat q : ℚ) : ℝ) = av := by
  have h := isSome_toAzRat? a
  rw [isFinite_of_toVal_coe ha] at h
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h
  exact ⟨q, hq, toRat_of_toAzRat? hq ha⟩

/-- `ratIsPos` is positivity. -/
theorem ratIsPos_iff (b : AzRat) : ratIsPos b = true ↔ 0 < ((AzRat.toRat b : ℚ) : ℝ) := by
  unfold ratIsPos
  rw [Bool.and_eq_true, decide_eq_true_eq]
  by_cases h0 : b.num = 0
  · rw [coe_toRat_eq_zero_of_num_eq_zero b h0]
    simp [h0]
  · rw [← toRat_sign_iff b h0]
    exact ⟨fun h => h.1, fun h => ⟨h, h0⟩⟩

/-- A float that is no rational is `NaN` or infinite. -/
theorem eq_of_toAzRat?_eq_none {a : AzFloat} (h : a.toAzRat? = none) :
    a = nan ∨ a = infinity true ∨ a = infinity false := by
  cases a with
  | nan => exact Or.inl rfl
  | infinity s => cases s <;> simp
  | zero => simp [toAzRat?] at h
  | finite s e q m hv => simp [toAzRat?] at h

/-- The value of `B` at a float that is not finite. -/
theorem betaFloatRatInfinite_eq {a : AzFloat} (h : a.toAzRat? = none) (b : AzRat) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    betaFloatRatInfinite a b = roundVal p mode
      (a.toVal.bind fun x => Spec.beta x (((AzRat.toRat b : ℚ) : ℝ) : EReal)) := by
  rcases eq_of_toAzRat?_eq_none h with rfl | rfl | rfl
  · rfl
  · simp only [betaFloatRatInfinite, toVal_infinity, ↓reduceIte, Option.bind_some,
      Spec.beta_top_coe]
    by_cases hb : ratIsPos b = true
    · rw [ite_eq_left hb, ite_eq_left ((ratIsPos_iff b).mp hb), roundVal_zero]
    · rw [ite_eq_right hb, ite_eq_right (fun h' => hb ((ratIsPos_iff b).mpr h')),
        roundVal_none]
  · simp only [betaFloatRatInfinite, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
      Option.bind_some, Spec.beta_bot_left, roundVal_none]

/-- The value of `ln |B|` at a float that is not finite. -/
theorem lnAbsBetaFloatRatInfinite_eq {a : AzFloat} (h : a.toAzRat? = none) (b : AzRat) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    lnAbsBetaFloatRatInfinite a b = roundVal p mode
      (a.toVal.bind fun x => Spec.lnAbsBeta x (((AzRat.toRat b : ℚ) : ℝ) : EReal)) := by
  unfold Spec.lnAbsBeta
  rcases eq_of_toAzRat?_eq_none h with rfl | rfl | rfl
  · rfl
  · simp only [lnAbsBetaFloatRatInfinite, toVal_infinity, ↓reduceIte, Option.bind_some,
      Spec.beta_top_coe]
    by_cases hb : ratIsPos b = true
    · rw [ite_eq_left hb, ite_eq_left ((ratIsPos_iff b).mp hb), Option.map_some,
        ← EReal.coe_zero, Spec.lnAbsE_zero, roundVal_bot]
    · rw [ite_eq_right hb, ite_eq_right (fun h' => hb ((ratIsPos_iff b).mpr h')),
        Option.map_none, roundVal_none]
  · simp only [lnAbsBetaFloatRatInfinite, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
      Option.bind_some, Spec.beta_bot_left, Option.map_none, roundVal_none]

/-- At a float that is not finite, `B` is `0` or no number. -/
theorem beta_infinite_cases {a : AzFloat} (h : a.toAzRat? = none) (y : ℝ) :
    (a.toVal.bind fun x => Spec.beta x (y : EReal)) = none ∨
      (a.toVal.bind fun x => Spec.beta x (y : EReal)) = some 0 := by
  rcases eq_of_toAzRat?_eq_none h with rfl | rfl | rfl
  · exact Or.inl rfl
  · simp only [toVal_infinity, ↓reduceIte, Option.bind_some, Spec.beta_top_coe]
    split_ifs <;> simp
  · left
    simp only [toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
      Spec.beta_bot_left]

/-! ### `B` -/

/-- **The specification of `B` for a float and a rational** (`ZivSpec`): sound at every fuel;
complete in the limit of the fuel wherever the value is no rounding boundary; and correct at
every fuel at the arguments that are not finite, on the special values (`NaN`, `+∞`, the
zeros) and where `betaRatSpecial` knows the value to be irrational. -/
theorem betaFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun ab : AzFloat × AzRat =>
        ab.1.toVal.bind fun x => Spec.beta x (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal))
      (fun fuel ab p mode => betaFloatRatPrecRoundFuel fuel ab.1 ab.2 p mode)
      {ab | ∀ av : ℝ, ab.1.toVal = some (av : EReal) →
        (av < 0 ∧ ∃ k : ℤ, av = k) ∨
        (((AzRat.toRat ab.2 : ℚ) : ℝ) < 0 ∧ ∃ k : ℤ, ((AzRat.toRat ab.2 : ℚ) : ℝ) = k) ∨
        av = 0 ∨ ((AzRat.toRat ab.2 : ℚ) : ℝ) = 0 ∨
        (av + ((AzRat.toRat ab.2 : ℚ) : ℝ) ≤ 0 ∧
          ∃ k : ℤ, av + ((AzRat.toRat ab.2 : ℚ) : ℝ) = k)}
      {ab | ∃ q, ab.1.toAzRat? = some q ∧ betaRatSpecial q ab.2 (q + ab.2) = true ∧
        ¬ ((q + ab.2).den = 1 ∧ ((q + ab.2).num = 0 ∨ (q + ab.2).sign = false))} :=
  (ZivSpec.floatRat betaRatPrecRoundFuel_zivSpec
    (fun fuel ab q p mode hq => by
      show betaFloatRatPrecRoundFuel fuel ab.1 ab.2 p mode = _
      unfold betaFloatRatPrecRoundFuel
      rw [hq])
    (fun fuel ab p _ mode hq => by
      show betaFloatRatPrecRoundFuel fuel ab.1 ab.2 p mode = _
      unfold betaFloatRatPrecRoundFuel
      rw [hq]
      exact betaFloatRatInfinite_eq hq ab.2 p mode)
    (fun ab hq v hv => by
      rcases beta_infinite_cases hq ((AzRat.toRat ab.2 : ℚ) : ℝ) with h | h
      · rw [h] at hv; exact absurd hv (by simp)
      · rw [h, Option.some.injEq, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at hv
        rw [← hv]
        exact isDyadic_zero)).mono
    (fun ab hab q hq => hab _ (toVal_of_toAzRat? _ _ hq)) (fun _ h => h)

/-- **`B` of a float and a rational is correctly rounded, or the fuel ran out.** -/
theorem betaFloatRatPrecRound_eq_or (a : AzFloat) (b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    betaFloatRatPrecRound a b p mode = roundVal p mode
        (a.toVal.bind fun x => Spec.beta x (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      betaFloatRatPrecRound a b p mode = (nan, .eq) :=
  betaFloatRatPrecRoundFuel_zivSpec.sound (gammaFuel p) (a, b) p mode

/-! ### `ln |B|` -/

/-- **The specification of `ln |B|` for a float and a rational** (the value component;
`ZivSpec`): sound at every fuel, and complete in the limit of the fuel wherever the value is
no rounding boundary. -/
theorem lnAbsBetaFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun ab : AzFloat × AzRat =>
        ab.1.toVal.bind fun x => Spec.lnAbsBeta x (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal))
      (fun fuel ab p mode => (lnAbsBetaFloatRatPrecRoundFuel fuel ab.1 ab.2 p mode).1)
      {ab | ab.1.toAzRat? = none} ∅ :=
  (ZivSpec.floatRat lnAbsBetaRatPrecRoundFuel_zivSpec
    (fun fuel ab q p mode hq => by
      show (lnAbsBetaFloatRatPrecRoundFuel fuel ab.1 ab.2 p mode).1 = _
      unfold lnAbsBetaFloatRatPrecRoundFuel
      rw [hq])
    (fun fuel ab p _ mode hq => by
      show (lnAbsBetaFloatRatPrecRoundFuel fuel ab.1 ab.2 p mode).1 = _
      unfold lnAbsBetaFloatRatPrecRoundFuel
      rw [hq]
      exact lnAbsBetaFloatRatInfinite_eq hq ab.2 p mode)
    (fun ab hq v hv => by
      exfalso
      have e : (ab.1.toVal.bind fun x =>
            Spec.lnAbsBeta x (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal))
          = (ab.1.toVal.bind fun x =>
            Spec.beta x (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal)).map Spec.lnAbsE := by
        unfold Spec.lnAbsBeta
        cases ab.1.toVal <;> rfl
      rw [e] at hv
      rcases beta_infinite_cases hq ((AzRat.toRat ab.2 : ℚ) : ℝ) with h | h
      · rw [h] at hv
        exact absurd hv (by simp)
      · rw [h, Option.map_some, ← EReal.coe_zero, Spec.lnAbsE_zero] at hv
        exact absurd hv (by simp))).mono
    (fun ab (hab : ab.1.toAzRat? = none) q hq => by rw [hab] at hq; exact absurd hq (by simp))
    (fun _ h => absurd h (Set.notMem_empty _))

/-- **`ln |B|` of a float and a rational is correctly rounded, or the fuel ran out.** -/
theorem lnAbsBetaFloatRatPrecRound_eq_or (a : AzFloat) (b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsBetaFloatRatPrecRound a b p mode).1 = roundVal p mode
        (a.toVal.bind fun x => Spec.lnAbsBeta x (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      (lnAbsBetaFloatRatPrecRound a b p mode).1 = (nan, .eq) :=
  lnAbsBetaFloatRatPrecRoundFuel_zivSpec.sound (gammaFuel p) (a, b) p mode

/-- **The sign component is the sign of `B(a, b)`** whenever the value is not `NaN`, where `B`
is finite and not `0`. -/
theorem lnAbsBetaFloatRatPrecRoundFuel_sign (fuel : ℕ) {a : AzFloat} {av : ℝ}
    (ha : a.toVal = some (av : EReal)) (b : AzRat) (ha0 : av ≠ 0) (hb0 : b.num ≠ 0)
    (hpa : ¬ (av < 0 ∧ ∃ k : ℤ, av = k)) (hpb : betaRatPole b ≠ true)
    (hs : ¬ (av + ((AzRat.toRat b : ℚ) : ℝ) ≤ 0 ∧
      ∃ k : ℤ, av + ((AzRat.toRat b : ℚ) : ℝ) = k)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsBetaFloatRatPrecRoundFuel fuel a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsBetaFloatRatPrecRoundFuel fuel a b p mode).2 = true
      ↔ 0 < Real.Gamma av * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
        / Real.Gamma (av + ((AzRat.toRat b : ℚ) : ℝ)) := by
  obtain ⟨q, hq, hqv⟩ := exists_toAzRat? ha
  have e : lnAbsBetaFloatRatPrecRoundFuel fuel a b p mode
      = lnAbsBetaRatPrecRoundFuel fuel q b p mode := by
    unfold lnAbsBetaFloatRatPrecRoundFuel
    rw [hq]
  rw [e] at hne ⊢
  have hsum : ((AzRat.toRat (q + b) : ℚ) : ℝ) = av + ((AzRat.toRat b : ℚ) : ℝ) := by
    rw [AzRat.toRat_add, ← hqv]; push_cast; rfl
  have := lnAbsBetaRatPrecRoundFuel_sign fuel q b
    (fun h0 => ha0 (by rw [← hqv]; exact coe_toRat_eq_zero_of_num_eq_zero q h0)) hb0
    (fun h => hpa (by rw [← hqv]; exact (betaRatPole_iff q).mp h)) hpb
    (fun h => hs (by rw [← hsum]; exact (nonpos_int_iff (q + b)).mp h)) p mode hne
  rwa [hqv] at this

/-- The sign theorem at the default fuel. -/
theorem lnAbsBetaFloatRatPrecRound_sign {a : AzFloat} {av : ℝ}
    (ha : a.toVal = some (av : EReal)) (b : AzRat) (ha0 : av ≠ 0) (hb0 : b.num ≠ 0)
    (hpa : ¬ (av < 0 ∧ ∃ k : ℤ, av = k)) (hpb : betaRatPole b ≠ true)
    (hs : ¬ (av + ((AzRat.toRat b : ℚ) : ℝ) ≤ 0 ∧
      ∃ k : ℤ, av + ((AzRat.toRat b : ℚ) : ℝ) = k)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsBetaFloatRatPrecRound a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsBetaFloatRatPrecRound a b p mode).2 = true
      ↔ 0 < Real.Gamma av * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
        / Real.Gamma (av + ((AzRat.toRat b : ℚ) : ℝ)) :=
  lnAbsBetaFloatRatPrecRoundFuel_sign (gammaFuel p) ha b ha0 hb0 hpa hpb hs p mode hne

/-! ### `ln B` -/

/-- At a float that is not finite, `ln B` is `ln |B|`. -/
theorem lnBeta_infinite_eq {a : AzFloat} (h : a.toAzRat? = none) (y : ℝ) :
    (a.toVal.bind fun x => Spec.lnBeta x (y : EReal))
      = a.toVal.bind fun x => Spec.lnAbsBeta x (y : EReal) := by
  rcases eq_of_toAzRat?_eq_none h with rfl | rfl | rfl
  · rfl
  · simp only [toVal_infinity, ↓reduceIte, Option.bind_some]
    refine (Spec.lnAbsBeta_eq_lnBeta fun v hv => ?_).symm
    rw [Spec.beta_top_coe] at hv
    split_ifs at hv
    · rw [Option.some.injEq, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at hv
      exact hv.le
  · simp only [toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
    refine (Spec.lnAbsBeta_eq_lnBeta fun v hv => ?_).symm
    rw [Spec.beta_bot_left] at hv
    exact absurd hv (by simp)

/-- **The specification of `ln B` for a float and a rational** (`ZivSpec`): sound at every
fuel, and complete in the limit of the fuel wherever the value is no rounding boundary (`NaN`
at every fuel where `B < 0`). -/
theorem lnBetaFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun ab : AzFloat × AzRat =>
        ab.1.toVal.bind fun x => Spec.lnBeta x (((AzRat.toRat ab.2 : ℚ) : ℝ) : EReal))
      (fun fuel ab p mode => lnBetaFloatRatPrecRoundFuel fuel ab.1 ab.2 p mode)
      {ab | ab.1.toAzRat? = none} ∅ :=
  (ZivSpec.floatRat lnBetaRatPrecRoundFuel_zivSpec
    (fun fuel ab q p mode hq => by
      show lnBetaFloatRatPrecRoundFuel fuel ab.1 ab.2 p mode
        = lnBetaRatPrecRoundFuel fuel q ab.2 p mode
      unfold lnBetaFloatRatPrecRoundFuel lnAbsBetaFloatRatPrecRoundFuel lnBetaRatPrecRoundFuel
      rw [hq])
    (fun fuel ab p _ mode hq => by
      show lnBetaFloatRatPrecRoundFuel fuel ab.1 ab.2 p mode = _
      unfold lnBetaFloatRatPrecRoundFuel lnAbsBetaFloatRatPrecRoundFuel
      rw [hq, lnBeta_infinite_eq hq]
      exact lnAbsBetaFloatRatInfinite_eq hq ab.2 p mode)
    (fun ab hq v hv => by
      rw [lnBeta_infinite_eq hq] at hv
      exact lnAbsBetaFloatRatPrecRoundFuel_zivSpec.dyadic ab hq v hv)).mono
    (fun ab (hab : ab.1.toAzRat? = none) q hq => by rw [hab] at hq; exact absurd hq (by simp))
    (fun _ h => absurd h (Set.notMem_empty _))

/-- **`ln B` of a float and a rational is correctly rounded, or the fuel ran out.** -/
theorem lnBetaFloatRatPrecRound_eq_or (a : AzFloat) (b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnBetaFloatRatPrecRound a b p mode = roundVal p mode
        (a.toVal.bind fun x => Spec.lnBeta x (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      lnBetaFloatRatPrecRound a b p mode = (nan, .eq) :=
  lnBetaFloatRatPrecRoundFuel_zivSpec.sound (gammaFuel p) (a, b) p mode

end Azurite.AzFloat
