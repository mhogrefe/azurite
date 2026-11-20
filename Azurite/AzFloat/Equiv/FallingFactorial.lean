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

/-- Negating the rounding in the opposite mode rounds the negated value, whatever it is. -/
theorem negRounded_roundVal_opt (p : ℕ) [NeZero p] (mode : RoundingMode) (o : Option EReal) :
    negRounded (roundVal p (-mode) o) = roundVal p mode (o.map Neg.neg) := by
  cases o with
  | none => rfl
  | some e =>
    induction e using EReal.rec with
    | bot =>
      rw [Option.map_some, EReal.neg_bot, roundVal_bot, roundVal_top]
      rfl
    | coe v =>
      rw [Option.map_some, ← EReal.coe_neg]
      exact negRounded_roundVal p mode v
    | top =>
      rw [Option.map_some, EReal.neg_top, roundVal_bot, roundVal_top]
      rfl

theorem IsDyadic.neg {v : ℝ} (h : IsDyadic v) : IsDyadic (-v) := by
  obtain ⟨m, k, rfl⟩ := h
  exact ⟨-m, k, by push_cast; ring⟩

/-- **A specification carries over to the reflected function**: where `σ` holds, the negated
value, rounded by negating the result in the opposite mode. -/
theorem ZivSpec.reflect {α : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} {D N : Set α} (h : ZivSpec val f D N)
    (σ : α → Prop) [DecidablePred σ] :
    ZivSpec (fun x => if σ x then (val x).map Neg.neg else val x)
      (fun fuel x p mode => if σ x then negRounded (f fuel x p (-mode)) else f fuel x p mode)
      D N where
  sound := fun fuel x p _ mode => by
    by_cases hs : σ x
    · simp only [hs, ↓reduceIte]
      rcases h.sound fuel x p (-mode) with h' | h'
      · left; rw [h', negRounded_roundVal_opt]
      · right; rw [h']; rfl
    · simp only [hs, ↓reduceIte]
      exact h.sound fuel x p mode
  complete := fun x p _ mode hB => by
    by_cases hs : σ x
    · simp only [hs, ↓reduceIte] at hB ⊢
      obtain ⟨F, hF⟩ := h.complete x p (-mode) (fun v hv hmem => by
        refine hB (-v) (by rw [hv, Option.map_some, EReal.coe_neg]) ?_
        rw [EReal.coe_neg]
        exact floatSet_neg_mem (p + 1) hmem)
      exact ⟨F, fun fuel hfuel => by rw [hF fuel hfuel, negRounded_roundVal_opt]⟩
    · simp only [hs, ↓reduceIte] at hB ⊢
      exact h.complete x p mode hB
  dyadic := fun x hx v hv => by
    by_cases hs : σ x
    · simp only [hs, ↓reduceIte] at hv
      obtain ⟨w, hw, hwv⟩ := Option.map_eq_some_iff.mp hv
      have hw' : w = ((-v : ℝ) : EReal) := by rw [EReal.coe_neg, ← hwv, neg_neg]
      rw [hw'] at hw
      have := (h.dyadic x hx _ hw).neg
      rwa [neg_neg] at this
    · simp only [hs, ↓reduceIte] at hv
      exact h.dyadic x hx v hv
  nondyadic := fun x hx => by
    obtain ⟨v, hv, hnd⟩ := h.nondyadic x hx
    by_cases hs : σ x
    · refine ⟨-v, by simp only [hs, ↓reduceIte, hv, Option.map_some, EReal.coe_neg], ?_⟩
      intro hd
      have := hd.neg
      rw [neg_neg] at this
      exact hnd this
    · exact ⟨v, by simp only [hs, ↓reduceIte, hv], hnd⟩
  correct := fun x hx fuel p _ mode => by
    by_cases hs : σ x
    · simp only [hs, ↓reduceIte]
      rw [h.correct x hx fuel p (-mode), negRounded_roundVal_opt]
    · simp only [hs, ↓reduceIte]
      exact h.correct x hx fuel p mode

/-- A specification pulled back along a map of the arguments. -/
theorem ZivSpec.comap {α β : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} {D N : Set α} (h : ZivSpec val f D N)
    (g : β → α) :
    ZivSpec (fun y => val (g y)) (fun fuel y p mode => f fuel (g y) p mode) (g ⁻¹' D)
      (g ⁻¹' N) where
  sound := fun fuel y p _ mode => h.sound fuel (g y) p mode
  complete := fun y p _ mode hB => h.complete (g y) p mode hB
  dyadic := fun y hy v hv => h.dyadic (g y) hy v hv
  nondyadic := fun y hy => h.nondyadic (g y) hy
  correct := fun y hy fuel p _ mode => h.correct (g y) hy fuel p mode

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

/-- The falling factorial as the reflected rising factorial, on the extended reals. -/
theorem Spec.fallingFactorial_eq (n : ℕ) (a : EReal) :
    Spec.fallingFactorial n a
      = if n % 2 = 1 then (Spec.pochhammer n (-a)).map Neg.neg else Spec.pochhammer n (-a) := by
  by_cases hn : n = 0
  · subst hn
    simp [Spec.fallingFactorial_zero, Spec.pochhammer_zero]
  induction a using EReal.rec with
  | bot =>
    by_cases he : n % 2 = 0
    · simp [Spec.fallingFactorial, Spec.pochhammer, hn, he]
    · have ho : n % 2 = 1 := by omega
      simp [Spec.fallingFactorial, Spec.pochhammer, hn, ho]
  | coe v =>
    rw [← EReal.coe_neg, Spec.fallingFactorial_coe hn, Spec.pochhammer_coe hn, prod_sub_eq]
    by_cases he : n % 2 = 0
    · rw [ite_eq_right (by omega), (Nat.even_iff.mpr he).neg_one_pow, one_mul]
    · have ho : n % 2 = 1 := by omega
      rw [ite_eq_left ho, (Nat.odd_iff.mpr ho).neg_one_pow, neg_one_mul, Option.map_some,
        EReal.coe_neg]
  | top =>
    by_cases he : n % 2 = 0
    · simp [Spec.fallingFactorial, Spec.pochhammer, hn, he]
    · have ho : n % 2 = 1 := by omega
      simp [Spec.fallingFactorial, Spec.pochhammer, hn, ho]

/-- The falling factorial is the reflected rising factorial at `−x`. -/
theorem fallingFactorialPrecRoundFuel_eq (fuel : ℕ) (x : AzFloat) (n p : ℕ)
    (mode : RoundingMode) :
    fallingFactorialPrecRoundFuel fuel x n p mode
      = if n % 2 = 1 then negRounded (pochhammerPrecRoundFuel fuel (-x) n p (-mode))
        else pochhammerPrecRoundFuel fuel (-x) n p mode := by
  by_cases hn : n = 0
  · subst hn
    cases x <;> rfl
  by_cases he : n % 2 = 0
  · have ho : ¬ n % 2 = 1 := by omega
    rw [ite_eq_right ho]
    cases x with
    | nan => rfl
    | infinity s =>
      show fallingFactorialPrecRoundFuel fuel (infinity s) n p mode
        = pochhammerPrecRoundFuel fuel (infinity (!s)) n p mode
      simp [fallingFactorialPrecRoundFuel, pochhammerPrecRoundFuel, hn, he]
    | zero =>
      show fallingFactorialPrecRoundFuel fuel zero n p mode
        = pochhammerPrecRoundFuel fuel zero n p mode
      simp only [fallingFactorialPrecRoundFuel, pochhammerPrecRoundFuel, ite_eq_right hn,
        fallingRealFuel, ite_eq_left he]
      rfl
    | finite s e q m hv =>
      show fallingFactorialPrecRoundFuel fuel (finite s e q m hv) n p mode
        = pochhammerPrecRoundFuel fuel (finite (!s) e q m hv) n p mode
      simp only [fallingFactorialPrecRoundFuel, pochhammerPrecRoundFuel, ite_eq_right hn,
        fallingRealFuel, ite_eq_left he]
      rfl
  · have ho : n % 2 = 1 := by omega
    rw [ite_eq_left ho]
    cases x with
    | nan => rfl
    | infinity s =>
      show fallingFactorialPrecRoundFuel fuel (infinity s) n p mode
        = negRounded (pochhammerPrecRoundFuel fuel (infinity (!s)) n p (-mode))
      cases s <;> simp [fallingFactorialPrecRoundFuel, pochhammerPrecRoundFuel, hn, ho,
        negRounded] <;> rfl
    | zero =>
      show fallingFactorialPrecRoundFuel fuel zero n p mode
        = negRounded (pochhammerPrecRoundFuel fuel zero n p (-mode))
      simp only [fallingFactorialPrecRoundFuel, pochhammerPrecRoundFuel, ite_eq_right hn,
        fallingRealFuel, ite_eq_right he]
      rfl
    | finite s e q m hv =>
      show fallingFactorialPrecRoundFuel fuel (finite s e q m hv) n p mode
        = negRounded (pochhammerPrecRoundFuel fuel (finite (!s) e q m hv) n p (-mode))
      simp only [fallingFactorialPrecRoundFuel, pochhammerPrecRoundFuel, ite_eq_right hn,
        fallingRealFuel, ite_eq_right he]
      rfl

/-- **The specification of the falling factorial** (`ZivSpec`): the one of Pochhammer's
symbol at `−x`, reflected for an odd `n`. -/
theorem fallingFactorialPrecRoundFuel_zivSpec :
    ZivSpec (fun xn : AzFloat × ℕ => xn.1.toVal.bind (Spec.fallingFactorial xn.2))
      (fun fuel xn p mode => fallingFactorialPrecRoundFuel fuel xn.1 xn.2 p mode)
      {xn | xn.2 = 0 ∨ xn.1.isFinite = false ∨ pochHasZero (-xn.1) xn.2 = true} ∅ := by
  have h := ((pochhammerPrecRoundFuel_zivSpec.reflect (fun xn => xn.2 % 2 = 1)).comap
    (fun xn : AzFloat × ℕ => (-xn.1, xn.2)))
  have hval : (fun xn : AzFloat × ℕ => xn.1.toVal.bind (Spec.fallingFactorial xn.2))
      = fun y : AzFloat × ℕ => if (-y.1, y.2).2 % 2 = 1
        then ((-y.1, y.2).1.toVal.bind (Spec.pochhammer (-y.1, y.2).2)).map Neg.neg
        else (-y.1, y.2).1.toVal.bind (Spec.pochhammer (-y.1, y.2).2) := by
    funext xn
    dsimp only
    rw [toVal_neg]
    cases xn.1.toVal with
    | none => simp
    | some a => rw [Option.bind_some, Option.map_some, Option.bind_some, Spec.fallingFactorial_eq]
  have hf : (fun fuel (xn : AzFloat × ℕ) p mode =>
        fallingFactorialPrecRoundFuel fuel xn.1 xn.2 p mode)
      = fun fuel (y : AzFloat × ℕ) p mode => if (-y.1, y.2).2 % 2 = 1
        then negRounded (pochhammerPrecRoundFuel fuel (-y.1, y.2).1 (-y.1, y.2).2 p (-mode))
        else pochhammerPrecRoundFuel fuel (-y.1, y.2).1 (-y.1, y.2).2 p mode := by
    funext fuel xn p mode
    exact fallingFactorialPrecRoundFuel_eq fuel xn.1 xn.2 p mode
  have hD : {xn : AzFloat × ℕ | xn.2 = 0 ∨ xn.1.isFinite = false ∨
        pochHasZero (-xn.1) xn.2 = true}
      = (fun xn : AzFloat × ℕ => (-xn.1, xn.2)) ⁻¹'
        {xn | xn.2 = 0 ∨ xn.1.isFinite = false ∨ pochHasZero xn.1 xn.2 = true} := by
    ext xn
    have : (-xn.1).isFinite = xn.1.isFinite := by cases xn.1 <;> rfl
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, this]
  rw [hval, hf, hD]
  exact h

/-- **The falling factorial is correctly rounded, or the fuel ran out**, at every fuel. -/
theorem fallingFactorialPrecRoundFuel_eq_or (fuel : ℕ) (x : AzFloat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    fallingFactorialPrecRoundFuel fuel x n p mode
        = liftVal (Spec.fallingFactorial n) x p mode ∨
      fallingFactorialPrecRoundFuel fuel x n p mode = (nan, .eq) :=
  fallingFactorialPrecRoundFuel_zivSpec.sound fuel (x, n) p mode

/-- **The falling factorial is correctly rounded, or the fuel ran out.** -/
theorem fallingFactorialPrecRound_eq_or (x : AzFloat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    fallingFactorialPrecRound x n p mode = liftVal (Spec.fallingFactorial n) x p mode ∨
      fallingFactorialPrecRound x n p mode = (nan, .eq) :=
  fallingFactorialPrecRoundFuel_eq_or (gammaFuel p) x n p mode

/-- **The specification of the falling factorial of a rational** (`ZivSpec`): the one of
Pochhammer's symbol at `−q`, reflected for an odd `n` — correct at every fuel, in particular,
wherever the denominator of `q` is not a power of two. -/
theorem fallingFactorialRatPrecRoundFuel_zivSpec :
    ZivSpec (fun qn : AzRat × ℕ =>
        Spec.fallingFactorial qn.2 ((((AzRat.toRat qn.1 : ℚ) : ℝ) : ℝ) : EReal))
      (fun fuel qn p mode => fallingFactorialRatPrecRoundFuel fuel qn.1 qn.2 p mode)
      {qn | qn.2 = 0 ∨ pochRatHasZero (-qn.1) qn.2 = true}
      {qn | qn.2 ≠ 0 ∧ pochRatSpecial qn.1 = true} := by
  have h := ((pochhammerRatPrecRoundFuel_zivSpec.reflect (fun qn => qn.2 % 2 = 1)).comap
    (fun qn : AzRat × ℕ => (-qn.1, qn.2)))
  have hval : (fun qn : AzRat × ℕ =>
        Spec.fallingFactorial qn.2 ((((AzRat.toRat qn.1 : ℚ) : ℝ) : ℝ) : EReal))
      = fun y : AzRat × ℕ => if (-y.1, y.2).2 % 2 = 1
        then (Spec.pochhammer (-y.1, y.2).2
          ((((AzRat.toRat (-y.1, y.2).1 : ℚ) : ℝ) : ℝ) : EReal)).map Neg.neg
        else Spec.pochhammer (-y.1, y.2).2
          ((((AzRat.toRat (-y.1, y.2).1 : ℚ) : ℝ) : ℝ) : EReal) := by
    funext qn
    dsimp only
    rw [AzRat.toRat_neg, Rat.cast_neg, EReal.coe_neg, Spec.fallingFactorial_eq]
  have hf : (fun fuel (qn : AzRat × ℕ) p mode =>
        fallingFactorialRatPrecRoundFuel fuel qn.1 qn.2 p mode)
      = fun fuel (y : AzRat × ℕ) p mode => if (-y.1, y.2).2 % 2 = 1
        then negRounded (pochhammerRatPrecRoundFuel fuel (-y.1, y.2).1 (-y.1, y.2).2 p (-mode))
        else pochhammerRatPrecRoundFuel fuel (-y.1, y.2).1 (-y.1, y.2).2 p mode := by
    funext fuel qn p mode
    unfold fallingFactorialRatPrecRoundFuel
    dsimp only
    by_cases he : qn.2 % 2 = 0
    · rw [ite_eq_left he, ite_eq_right (by omega)]
    · rw [ite_eq_right he, ite_eq_left (by omega)]
  rw [hval, hf]
  exact h

/-- **The falling factorial of a rational is correctly rounded, or the fuel ran out**, at
every fuel. -/
theorem fallingFactorialRatPrecRoundFuel_eq_or (fuel : ℕ) (q : AzRat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    fallingFactorialRatPrecRoundFuel fuel q n p mode
        = roundVal p mode (Spec.fallingFactorial n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      fallingFactorialRatPrecRoundFuel fuel q n p mode = (nan, .eq) :=
  fallingFactorialRatPrecRoundFuel_zivSpec.sound fuel (q, n) p mode

/-- **The falling factorial of a rational is correctly rounded, or the fuel ran out.** -/
theorem fallingFactorialRatPrecRound_eq_or (q : AzRat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    fallingFactorialRatPrecRound q n p mode
        = roundVal p mode (Spec.fallingFactorial n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      fallingFactorialRatPrecRound q n p mode = (nan, .eq) :=
  fallingFactorialRatPrecRoundFuel_eq_or (gammaFuel p) q n p mode

end Azurite.AzFloat
