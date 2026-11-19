/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.FallingFactorial
import Azurite.AzFloat.Equiv.PochhammerRat
import Azurite.AzFloat.Equiv.NegRound
import Azurite.AzRat.Equiv.Unary

/-!
# Equivalence: the falling factorial

`Spec.fallingFactorial n : EReal → Option EReal` is the falling factorial on the extended
reals — Mathlib's `(descPochhammer ℝ n).eval a` — and `fallingFactorialPrecRound_eq_or`,
`fallingFactorialRatPrecRound_eq_or` say that the functions are its correct rounding, or
`(nan, .eq)` when the fuel of the Ziv loop runs out.

The step: `prod_sub_eq` (`∏ (x − j) = (−1)ⁿ ∏ (−x + j)`) and `negRounded_roundVal`.
-/

namespace Azurite.AzFloat

open Finset

/-- `∏_{j<n} (x − j) = (−1)ⁿ ∏_{j<n} (−x + j)`. -/
theorem prod_sub_eq (x : ℝ) (n : ℕ) :
    ∏ j ∈ range n, (x - j) = (-1) ^ n * ∏ j ∈ range n, (-x + j) := by
  have h : ∀ j ∈ range n, x - (j : ℝ) = -(-x + j) := fun j _ => by ring
  rw [prod_congr rfl h, prod_neg, card_range]

/-- Negating the rounding of `v` in the opposite mode rounds `−v`. -/
theorem negRounded_roundVal (p : ℕ) [NeZero p] (mode : RoundingMode) (v : ℝ) :
    negRounded (roundVal p (-mode) (some (v : EReal)))
      = roundVal p mode (some ((-v : ℝ) : EReal)) :=
  (roundVal_neg p mode v).symm

/-- The reflection step: from "the rounding of `∏ (−x + j)`, or `NaN`" in every mode to the
rounding of `∏ (x − j)`. -/
theorem falling_of_rising {f : RoundingMode → AzFloat × Ordering} {xv : ℝ} {n p : ℕ}
    [NeZero p]
    (h : ∀ mode, f mode = roundVal p mode (some ((∏ j ∈ range n, (-xv + j) : ℝ) : EReal)) ∨
      f mode = (nan, .eq)) (mode : RoundingMode) :
    (if n % 2 = 0 then f mode else negRounded (f (-mode)))
        = roundVal p mode (some ((∏ j ∈ range n, (xv - j) : ℝ) : EReal)) ∨
      (if n % 2 = 0 then f mode else negRounded (f (-mode))) = (nan, .eq) := by
  rw [prod_sub_eq]
  by_cases he : n % 2 = 0
  · rw [ite_eq_left he, (Nat.even_iff.mpr he).neg_one_pow, one_mul]
    exact h mode
  · rw [ite_eq_right he, (Nat.odd_iff.mpr (by omega)).neg_one_pow, neg_one_mul]
    rcases h (-mode) with h' | h'
    · left; rw [h', negRounded_roundVal]
    · right; rw [h']; rfl

namespace Spec

/-- The falling factorial on the extended reals: `1` for `n = 0`; `+∞` at `+∞` and `(−1)ⁿ ∞`
at `−∞` for `n ≥ 1`. -/
noncomputable def fallingFactorial (n : ℕ) (a : EReal) : Option EReal :=
  if n = 0 then some 1
  else if a = ⊤ then some ⊤
  else if a = ⊥ then (if n % 2 = 0 then some ⊤ else some ⊥)
  else some (((descPochhammer ℝ n).eval a.toReal : ℝ) : EReal)

theorem fallingFactorial_zero (a : EReal) : fallingFactorial 0 a = some 1 := by
  simp [fallingFactorial]

theorem fallingFactorial_coe {n : ℕ} (hn : n ≠ 0) (xv : ℝ) :
    fallingFactorial n (xv : EReal) = some ((∏ j ∈ range n, (xv - j) : ℝ) : EReal) := by
  unfold fallingFactorial
  rw [ite_eq_right hn, ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    EReal.toReal_coe, descPochhammer_eval_eq_prod_range]

end Spec

theorem fallingReal_eq_or {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (n p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    fallingReal x n p mode = roundVal p mode (some ((∏ j ∈ range n, (xv - j) : ℝ) : EReal)) ∨
      fallingReal x n p mode = (nan, .eq) := by
  have hneg : (-x).toVal = some ((-xv : ℝ) : EReal) := by
    rw [toVal_neg, hx, Option.map_some, EReal.coe_neg]
  exact falling_of_rising (f := fun m => pochReal (-x) n p m)
    (fun m => pochReal_eq_or hneg n p m) mode

/-- **The falling factorial is correctly rounded, or the fuel ran out.** -/
theorem fallingFactorialPrecRound_eq_or (x : AzFloat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    fallingFactorialPrecRound x n p mode = liftVal (Spec.fallingFactorial n) x p mode ∨
      fallingFactorialPrecRound x n p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  have hone : setPrecRound one p mode = roundVal p mode (some (1 : EReal)) := by
    rw [setPrecRound_eq_roundVal toVal_one', EReal.coe_one]
  unfold liftVal
  cases x with
  | nan => left; rfl
  | infinity s =>
    left
    by_cases hn : n = 0
    · subst hn
      simp only [fallingFactorialPrecRound, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.fallingFactorial_zero, ite_eq_right hp, hone]
    · simp only [fallingFactorialPrecRound, ite_eq_right hn, toVal_infinity, Option.bind_some]
      cases s
      · by_cases he : n % 2 = 0
        · simp [Spec.fallingFactorial, hn, he]
        · simp [Spec.fallingFactorial, hn, he]
      · simp [Spec.fallingFactorial, hn]
  | zero =>
    by_cases hn : n = 0
    · left
      subst hn
      simp only [fallingFactorialPrecRound, ↓reduceIte, toVal_zero, Option.bind_some,
        Spec.fallingFactorial_zero, ite_eq_right hp, hone]
    · simp only [fallingFactorialPrecRound, ite_eq_right hn, toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.fallingFactorial_coe hn]
      exact fallingReal_eq_or toVal_zero' n p mode
  | finite s e q m hv =>
    by_cases hn : n = 0
    · left
      subst hn
      simp only [fallingFactorialPrecRound, ↓reduceIte, toVal_finite, Option.bind_some,
        Spec.fallingFactorial_zero, ite_eq_right hp, hone]
    · simp only [fallingFactorialPrecRound, ite_eq_right hn, toVal_finite, Option.bind_some]
      rw [Spec.fallingFactorial_coe hn]
      exact fallingReal_eq_or (toVal_finite s e q m hv) n p mode

/-- **The falling factorial of a rational is correctly rounded, or the fuel ran out.** -/
theorem fallingFactorialRatPrecRound_eq_or (q : AzRat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    fallingFactorialRatPrecRound q n p mode
        = roundVal p mode (Spec.fallingFactorial n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      fallingFactorialRatPrecRound q n p mode = (nan, .eq) := by
  unfold fallingFactorialRatPrecRound
  by_cases hn : n = 0
  · subst hn
    rw [ite_eq_left rfl, Spec.fallingFactorial_zero]
    have := pochhammerRatPrecRound_eq_or (-q) 0 p mode
    rwa [Spec.pochhammer_zero] at this
  · rw [Spec.fallingFactorial_coe hn]
    refine falling_of_rising (f := fun m => pochhammerRatPrecRound (-q) n p m) (fun m => ?_) mode
    have := pochhammerRatPrecRound_eq_or (-q) n p m
    rwa [Spec.pochhammer_coe hn, AzRat.toRat_neg, Rat.cast_neg] at this

end Azurite.AzFloat
