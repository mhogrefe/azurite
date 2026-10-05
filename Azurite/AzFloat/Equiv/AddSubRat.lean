/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddSubRat
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.Ziv
import Azurite.AzRat.Equiv.Add
import Azurite.AzRat.Equiv.Unary

/-!
# Addition of an `AzFloat` and an `AzRat` is a lift

`addRatPrecRound_eq_liftVal`: `addRatPrecRound x q p mode = liftVal (fun a => Spec.add a q) x
p mode`, where `q` stands for the value of the rational.  The approximation step is checked with
`truncError_spec` twice (for `q` and for the sum) and the rounding up of the error bound with
`isLeast_roundCeiling`; `zivLoop_eq` does the rest.  `ofAzRatRound_eq_roundVal` is the pair
form of `ofAzRatRound_eq_ofEReal`, used for the zero case and the exact fallback.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-- Rounding a rational computably is `roundVal` of its value, tag included. -/
theorem ofAzRatRound_eq_roundVal (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ofAzRatRound q p mode = roundVal p mode (some ((AzRat.toRat q : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  refine Prod.ext ?_ ?_
  · rw [fst_roundVal]
    exact ofAzRatRound_eq_ofEReal p q mode
  · obtain ⟨v, hv, ht⟩ := snd_ofAzRatRound q p hp mode
    rw [ht, (roundVal_coe p mode _).2]
    have hval : ((v : ℝ) : EReal) = (round (floatSet p) mode (AzRat.toRat q : ℝ)).val := by
      have h1 := (ofEReal_spec p mode (AzRat.toRat q : ℝ)).2
      rw [← ofAzRatRound_eq_ofEReal p q mode, hv, Option.some.injEq] at h1
      exact h1
    rw [← hval, compare_coe_coe]

/-- The exact fallback is the rounding of the exact sum. -/
theorem addRatExact_eq (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (xv : ℝ) (hx : x.toVal = some (xv : EReal)) :
    addRatExact x q p mode = roundVal p mode (some ((xv + AzRat.toRat q : ℝ) : EReal)) := by
  unfold addRatExact
  cases hr : x.toAzRat? with
  | none =>
    exfalso
    cases x <;> simp [toAzRat?] at hr hx
    rename_i s
    cases s <;> simp at hx
  | some r =>
    have hxr := toVal_of_toAzRat? x r hr
    rw [hx, Option.some.injEq, EReal.coe_eq_coe_iff] at hxr
    simp only
    rw [ofAzRatRound_eq_roundVal, AzRat.toRat_add, hxr]
    push_cast
    rfl

/-- The approximation at a positive working precision brackets the exact sum. -/
theorem addRatApprox_spec (x : AzFloat) (q : AzRat) (xv : ℝ) (hx : x.toVal = some (xv : EReal))
    (w : ℕ) (hw : 0 < w) :
    ∃ yv εv : ℝ, yv ≤ xv + AzRat.toRat q ∧ xv + AzRat.toRat q ≤ yv + εv ∧
      (addRatApprox x q w).1.toVal = some (yv : EReal) ∧
      (addRatApprox x q w).2.toVal = some (εv : EReal) := by
  have : NeZero w := ⟨hw.ne'⟩
  have : NeZero (w + 2) := ⟨by omega⟩
  have : NeZero 2 := ⟨by omega⟩
  unfold addRatApprox
  simp only
  -- the truncation of `q`
  rw [ofAzRatRound_eq_ofEReal w q .Floor]
  obtain ⟨lov, e₁, hlo, he₁, hlo1, hlo2⟩ := truncError_spec w (AzRat.toRat q : ℝ)
  -- the truncation of the sum
  have hy : (addPrecRound x (ofEReal w .Floor (AzRat.toRat q : ℝ)) (w + 2) .Floor).1
      = ofEReal (w + 2) .Floor ((xv + lov : ℝ) : EReal) := by
    rw [addPrecRound_eq_liftVal₂]
    unfold liftVal₂
    rw [hx, hlo, Option.bind_some, Option.bind_some, Spec.add_coe_coe, fst_roundVal]
    rfl
  rw [hy]
  obtain ⟨yv, e₂, hyv, he₂, hy1, hy2⟩ := truncError_spec (w + 2) (xv + lov)
  -- the error bound, rounded up
  have hε : (addPrecRound (truncError (ofEReal w .Floor (AzRat.toRat q : ℝ)))
      (truncError (ofEReal (w + 2) .Floor ((xv + lov : ℝ) : EReal))) 2 .Ceiling).1
      = ofEReal 2 .Ceiling ((e₁ + e₂ : ℝ) : EReal) := by
    rw [addPrecRound_eq_liftVal₂]
    unfold liftVal₂
    rw [he₁, he₂, Option.bind_some, Option.bind_some, Spec.add_coe_coe, fst_roundVal]
    rfl
  rw [hε]
  obtain ⟨_, hεval⟩ := ofEReal_spec 2 .Ceiling (e₁ + e₂)
  rw [val_round_floatSet] at hεval
  have hC : (round (precisionSet 2 2) .Ceiling (e₁ + e₂)).val
      = (roundCeiling (precisionSet 2 2) (e₁ + e₂)).val := rfl
  rw [hC] at hεval
  obtain ⟨εv, hεv⟩ := precisionSet_exists_real (roundCeiling (precisionSet 2 2) (e₁ + e₂))
  have hεle : e₁ + e₂ ≤ εv := by
    have := (isLeast_roundCeiling (precisionSet 2 2) (e₁ + e₂)).1.2
    rw [← hεv] at this
    exact EReal.coe_le_coe_iff.mp this
  refine ⟨yv, εv, by linarith, by linarith, hyv, ?_⟩
  rw [hεval, ← hεv]

/-- Addition of a rational is the lift of `EReal` addition with its value. -/
theorem addRatPrecRound_eq_liftVal (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    addRatPrecRound x q p mode
      = liftVal (fun a => Spec.add a ((AzRat.toRat q : ℝ) : EReal)) x p mode := by
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;> simp [addRatPrecRound, liftVal, Spec.add]
  | zero =>
    show ofAzRatRound q p mode = _
    unfold liftVal
    rw [toVal_zero, Option.bind_some, Spec.add_zero_left, ofAzRatRound_eq_roundVal]
  | finite s e q' m hv =>
    show zivLoop _ _ p mode _ _ = _
    unfold liftVal
    rw [toVal_finite, Option.bind_some, Spec.add_coe_coe]
    apply zivLoop_eq p mode _ _ (finiteVal s e m + AzRat.toRat q)
    · exact addRatApprox_spec (finite s e q' m hv) q (finiteVal s e m) rfl
    · exact addRatExact_eq (finite s e q' m hv) q p mode (finiteVal s e m) rfl
    · simp only [zivStart, zivGuardBits]
      split_ifs <;> omega

/-- The value of a negated rational. -/
theorem coe_toRat_neg (q : AzRat) :
    ((AzRat.toRat (-q) : ℝ) : EReal) = -((AzRat.toRat q : ℝ) : EReal) := by
  rw [AzRat.toRat_neg]
  push_cast
  rfl

/-- Subtraction of a rational is the lift of `EReal` subtraction with its value. -/
theorem subRatPrecRound_eq_liftVal (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    subRatPrecRound x q p mode
      = liftVal (fun a => Spec.sub a ((AzRat.toRat q : ℝ) : EReal)) x p mode := by
  unfold subRatPrecRound
  rw [addRatPrecRound_eq_liftVal, coe_toRat_neg]
  rfl

/-- Subtraction from a rational is the lift of `EReal` subtraction from its value. -/
theorem ratSubPrecRound_eq_liftVal (q : AzRat) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ratSubPrecRound q x p mode
      = liftVal (fun a => Spec.sub ((AzRat.toRat q : ℝ) : EReal) a) x p mode := by
  unfold ratSubPrecRound
  rw [addRatPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_neg]
  cases x.toVal with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Option.bind_some]
    unfold Spec.sub Spec.add
    congr 1
    rw [add_comm]
    by_cases h1 : a = ⊤
    · subst h1; simp
    · by_cases h2 : a = ⊥
      · subst h2; simp
      · simp [h1, h2, EReal.neg_eq_top_iff, EReal.neg_eq_bot_iff]

end Azurite.AzFloat
