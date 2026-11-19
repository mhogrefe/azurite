/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Ziv
import Azurite.AzFloat.Equiv.ZivPair

/-!
# The specification of a fuel-bound Ziv loop

A function computed by Ziv's loop is correctly rounded as soon as the loop stops, and the loop
stops when the bracket is narrower than the distance from the value to the nearest rounding
boundary.  When the value is not known to avoid the boundaries (the dyadic rationals), no
termination certificate is available and the loop carries fuel.  "Correctly rounded, or `NaN`"
is then all that can be said at a fixed fuel — but it is satisfied by a function that always
gives up.  `ZivSpec` says what such a function does, as far as it can be said:

* `sound`: at every fuel the result is the correctly rounded value or `(nan, .eq)`;
* `complete`: when the value is not a rounding boundary at the precision asked for, every
  large enough fuel gives the correctly rounded value (this is the convergence of the
  bracket, `BracketConv`, seen from outside);
* `correct`: on two sets of arguments given with the specification — `D`, where the value is
  known to be dyadic (or not a real number) and is produced exactly, and `N`, where it is
  known not to be dyadic — the result is correctly rounded at every fuel.

So the function can fail for ever only at an argument outside `D` whose value is a dyadic
rational: whether there are any is a question about the function, not about the program.
When `D ∪ N` is everything, `ZivSpec` is the unconditional specification
(`ZivSpec.eq_of_univ`).

* `BracketConv approx v`: the brackets enclose `v` from some level on, with widths that tend
  to `0`; `BracketConv.exists_isSome`.
* `zivLoop_some_of_isSome`, `zivLoop_eventually_eq`: the fuel loop reaches the first accepted
  level when the fuel allows.
* `IsDyadic`, `not_mem_floatSet_of_not_isDyadic`, `not_isDyadic_of_irrational`.
-/

namespace Azurite.AzFloat

open Filter Topology

/-- **The brackets converge to `v`**: from some level on they enclose `v`, with widths that
tend to `0`. -/
def BracketConv (approx : ℕ → Roundable × Roundable) (v : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ W₀ : ℕ, ∀ w, W₀ ≤ w → ∃ lv hv : ℝ,
    Rounds (approx w).1 lv ∧ Rounds (approx w).2 hv ∧ lv ≤ v ∧ v ≤ hv ∧ hv - lv ≤ ε w

/-- A convergent bracket of a value that is not a rounding boundary is accepted at some
level. -/
theorem BracketConv.exists_isSome {approx : ℕ → Roundable × Roundable} {v : ℝ}
    (h : BracketConv approx v) (hv0 : v ≠ 0) (p : ℕ) [NeZero p]
    (hvB : ((v : ℝ) : EReal) ∉ floatSet (p + 1)) (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (approx (w₀ * 2 ^ f)).1 (approx (w₀ * 2 ^ f)).2 p
      mode).isSome = true := by
  obtain ⟨ε, hε, W₀, hW₀⟩ := h
  exact exists_isSome_of_not_mem_threshold p mode approx hv0 hvB ε hε W₀ hW₀ w₀ hw₀

/-- With fuel for `f` doublings and an accepted level `w 2^f`, the fuel loop returns the
answer of `roundingPossible` at the first accepted level. -/
theorem zivLoop_some_of_isSome (approx : ℕ → Roundable × Roundable) (p : ℕ)
    (mode : RoundingMode) : ∀ (fuel f w : ℕ), f ≤ fuel →
      (roundingPossible (approx (w * 2 ^ f)).1 (approx (w * 2 ^ f)).2 p mode).isSome = true →
      ∃ g : ℕ, roundingPossible (approx (w * 2 ^ g)).1 (approx (w * 2 ^ g)).2 p mode
        = some (zivLoop approx p mode fuel w)
  | fuel, f, w, hf, hs => by
    rw [zivLoop.eq_def]
    cases hr : roundingPossible (approx w).1 (approx w).2 p mode with
    | some r => exact ⟨0, by simpa using hr⟩
    | none =>
      dsimp only
      cases f with
      | zero =>
        rw [pow_zero, mul_one, hr] at hs
        exact absurd hs (by simp)
      | succ f =>
        cases fuel with
        | zero => omega
        | succ fuel =>
          have hs' : (roundingPossible (approx (2 * w * 2 ^ f)).1 (approx (2 * w * 2 ^ f)).2 p
              mode).isSome = true := by
            rw [show 2 * w * 2 ^ f = w * 2 ^ (f + 1) by ring]
            exact hs
          obtain ⟨g, hg⟩ := zivLoop_some_of_isSome approx p mode fuel f (2 * w) (by omega) hs'
          exact ⟨g + 1, by rw [show w * 2 ^ (g + 1) = 2 * w * 2 ^ g by ring]; exact hg⟩

/-- **The fuel loop on a convergent bracket of a non-boundary value is correct for every
large enough fuel.** -/
theorem zivLoop_eventually_eq (p : ℕ) [NeZero p] (mode : RoundingMode)
    (approx : ℕ → Roundable × Roundable) {v : ℝ} (hconv : BracketConv approx v) (hv0 : v ≠ 0)
    (hvB : ((v : ℝ) : EReal) ∉ floatSet (p + 1)) (w₀ : ℕ) (hw₀ : 0 < w₀)
    (hvalid : ∀ w, w₀ ≤ w → (∃ lv hv : ℝ, Rounds (approx w).1 lv ∧ Rounds (approx w).2 hv ∧
      lv ≤ v ∧ v ≤ hv) ∨ roundingPossible (approx w).1 (approx w).2 p mode = none) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel →
      zivLoop approx p mode fuel w₀ = roundVal p mode (some (v : EReal)) := by
  obtain ⟨f, hf⟩ := hconv.exists_isSome hv0 p hvB mode w₀ hw₀
  refine ⟨f, fun fuel hfuel => ?_⟩
  obtain ⟨g, hg⟩ := zivLoop_some_of_isSome approx p mode fuel f w₀ hfuel hf
  rcases hvalid (w₀ * 2 ^ g) (Nat.le_mul_of_pos_right _ (by positivity)) with
    ⟨lv, hv, hl, hh, h1, h2⟩ | hn
  · exact roundingPossible_eq' p mode hl hh h1 h2 (Or.inr hvB) hg
  · rw [hn] at hg
    exact absurd hg (by simp)

/-- Brackets that agree from some level on converge together. -/
theorem BracketConv.congr {a a' : ℕ → Roundable × Roundable} {v : ℝ} (h : BracketConv a v)
    (heq : ∃ W : ℕ, ∀ w, W ≤ w → a' w = a w) : BracketConv a' v := by
  obtain ⟨ε, hε, W₀, hW₀⟩ := h
  obtain ⟨W, hW⟩ := heq
  refine ⟨ε, hε, max W₀ W, fun w hw => ?_⟩
  rw [hW w (le_trans (le_max_right _ _) hw)]
  exact hW₀ w (le_trans (le_max_left _ _) hw)

/-- `0` is a float of every precision. -/
theorem zero_mem_floatSet (p : ℕ) : (((0 : ℝ) : ℝ) : EReal) ∈ floatSet p :=
  ⟨zero, Or.inr rfl, by rw [toVal_zero, EReal.coe_zero]⟩

/-- A real that is no rounding boundary is not `0`. -/
theorem ne_zero_of_not_mem_floatSet {p : ℕ} {v : ℝ} (h : ((v : ℝ) : EReal) ∉ floatSet p) :
    v ≠ 0 := fun h0 => h (h0 ▸ zero_mem_floatSet p)

/-- `nanOrElse` of a result that is correct or `NaN`, and a correct fallback. -/
theorem nanOrElse_eq {r v : AzFloat × Ordering} {f : Unit → AzFloat × Ordering}
    (hr : r = v ∨ r = (nan, .eq)) (hf : f () = v) : nanOrElse r f = v := by
  rcases hr with rfl | rfl
  · unfold nanOrElse
    split
    · exact hf
    · rfl
  · exact hf

/-- The fuel loop gives up, or returns the answer of `roundingPossible` at some level. -/
theorem zivLoop_eq_nan_or_some (approx : ℕ → Roundable × Roundable) (p : ℕ)
    (mode : RoundingMode) : ∀ (fuel w : ℕ), zivLoop approx p mode fuel w = (nan, .eq) ∨
      ∃ g : ℕ, roundingPossible (approx (w * 2 ^ g)).1 (approx (w * 2 ^ g)).2 p mode
        = some (zivLoop approx p mode fuel w)
  | fuel, w => by
    rw [zivLoop.eq_def]
    cases hr : roundingPossible (approx w).1 (approx w).2 p mode with
    | some r => exact Or.inr ⟨0, by simpa using hr⟩
    | none =>
      dsimp only
      cases fuel with
      | zero => exact Or.inl rfl
      | succ fuel =>
        rcases zivLoop_eq_nan_or_some approx p mode fuel (2 * w) with h | ⟨g, hg⟩
        · exact Or.inl h
        · exact Or.inr ⟨g + 1, by rw [show w * 2 ^ (g + 1) = 2 * w * 2 ^ g by ring]; exact hg⟩

/-- **The fuel loop on valid brackets of a value that is no rounding boundary** is correct
when it does not give up. -/
theorem zivLoop_eq_or_nan_of_not_boundary (p : ℕ) [NeZero p] (mode : RoundingMode)
    (approx : ℕ → Roundable × Roundable) {v : ℝ} (hvB : ((v : ℝ) : EReal) ∉ floatSet (p + 1))
    (w₁ : ℕ)
    (hvalid : ∀ w, w₁ ≤ w → (∃ lv hv : ℝ, Rounds (approx w).1 lv ∧ Rounds (approx w).2 hv ∧
      lv ≤ v ∧ v ≤ hv) ∨ roundingPossible (approx w).1 (approx w).2 p mode = none)
    (fuel w₀ : ℕ) (hw : w₁ ≤ w₀) :
    zivLoop approx p mode fuel w₀ = roundVal p mode (some (v : EReal)) ∨
      zivLoop approx p mode fuel w₀ = (nan, .eq) := by
  rcases zivLoop_eq_nan_or_some approx p mode fuel w₀ with h | ⟨g, hg⟩
  · exact Or.inr h
  · left
    rcases hvalid (w₀ * 2 ^ g) (hw.trans (Nat.le_mul_of_pos_right _ (by positivity))) with
      ⟨lv, hv, hl, hh, h1, h2⟩ | hn
    · exact roundingPossible_eq' p mode hl hh h1 h2 (Or.inr hvB) hg
    · rw [hn] at hg
      exact absurd hg (by simp)

/-- **The backed loop gives the correctly rounded value**, on valid brackets of a value that
is no rounding boundary. -/
theorem zivLoopBacked_eq (p : ℕ) [NeZero p] (mode : RoundingMode)
    (approx : ℕ → Roundable × Roundable) {v : ℝ} (hvB : ((v : ℝ) : EReal) ∉ floatSet (p + 1))
    (w₁ : ℕ)
    (hvalid : ∀ w, w₁ ≤ w → (∃ lv hv : ℝ, Rounds (approx w).1 lv ∧ Rounds (approx w).2 hv ∧
      lv ≤ v ∧ v ≤ hv) ∨ roundingPossible (approx w).1 (approx w).2 p mode = none)
    (fuel w₀ : ℕ) (hw : w₁ ≤ w₀) (hw₀ : 0 < w₀)
    (h : ∃ f : ℕ,
      (roundingPossible (approx (w₀ * 2 ^ f)).1 (approx (w₀ * 2 ^ f)).2 p mode).isSome = true) :
    zivLoopBacked approx p mode fuel w₀ h = roundVal p mode (some (v : EReal)) :=
  nanOrElse_eq (zivLoop_eq_or_nan_of_not_boundary p mode approx hvB w₁ hvalid fuel w₀ hw)
    (zivLoopCertified_eq_or_none p mode approx v hvB w₀ hw₀
      (fun w hw' => hvalid w (hw.trans hw')) h)

/-! ### Dyadic numbers -/

/-- `v = m 2^k`: the reals that are rounding boundaries at some precision. -/
def IsDyadic (v : ℝ) : Prop := ∃ m k : ℤ, v = m * (2 : ℝ) ^ k

theorem isDyadic_zero : IsDyadic 0 := ⟨0, 0, by simp⟩

theorem isDyadic_intCast (n : ℤ) : IsDyadic n := ⟨n, 0, by simp⟩

theorem isDyadic_natCast (n : ℕ) : IsDyadic n := ⟨n, 0, by simp⟩

/-- The value of a float is dyadic. -/
theorem isDyadic_of_toVal {x : AzFloat} {a : ℝ} (hx : x.toVal = some (a : EReal)) :
    IsDyadic a := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero =>
    rw [toVal_zero, Option.some.injEq] at hx
    have : a = 0 := by exact_mod_cast hx.symm
    rw [this]
    exact isDyadic_zero
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    rw [← hx]
    unfold finiteVal
    cases s
    · exact ⟨-(m.toNat : ℤ), e.toInt - m.size, by simp⟩
    · exact ⟨(m.toNat : ℤ), e.toInt - m.size, by simp⟩

theorem not_isDyadic_of_irrational {v : ℝ} (h : Irrational v) : ¬ IsDyadic v := by
  rintro ⟨m, k, rfl⟩
  exact h ⟨m * (2 : ℚ) ^ k, by push_cast; rfl⟩

/-- A real that is not dyadic is no rounding boundary. -/
theorem not_mem_floatSet_of_not_isDyadic (p : ℕ) [NeZero p] {v : ℝ} (h : ¬ IsDyadic v) :
    ((v : ℝ) : EReal) ∉ floatSet (p + 1) := by
  intro hB
  have hv0 : v ≠ 0 := fun h0 => h (h0 ▸ isDyadic_zero)
  obtain ⟨M, k, hMk, -⟩ := boundary_repr p v hB hv0
  exact h ⟨M, k, hMk⟩

/-! ### The specification -/

/-- **The specification of a fuel-bound correctly rounded function** `f fuel x p mode` of the
value `val x`, with the arguments `D` known to be exact (dyadic or not real values) and the
arguments `N` known to have non-dyadic values. -/
structure ZivSpec {α : Type*} (val : α → Option EReal)
    (f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering) (D N : Set α) : Prop where
  /-- At every fuel: the correctly rounded value, or `(nan, .eq)`. -/
  sound : ∀ (fuel : ℕ) (x : α) (p : ℕ) [NeZero p] (mode : RoundingMode),
    f fuel x p mode = roundVal p mode (val x) ∨ f fuel x p mode = (nan, .eq)
  /-- When the value is not a rounding boundary at precision `p`, every large enough fuel
  gives the correctly rounded value. -/
  complete : ∀ (x : α) (p : ℕ) [NeZero p] (mode : RoundingMode),
    (∀ v : ℝ, val x = some (v : EReal) → ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → f fuel x p mode = roundVal p mode (val x)
  /-- The values on `D` that are real numbers are dyadic. -/
  dyadic : ∀ x ∈ D, ∀ v : ℝ, val x = some (v : EReal) → IsDyadic v
  /-- The values on `N` are real numbers that are not dyadic. -/
  nondyadic : ∀ x ∈ N, ∃ v : ℝ, val x = some (v : EReal) ∧ ¬ IsDyadic v
  /-- On `D` and on `N` the result is correctly rounded, at every fuel. -/
  correct : ∀ x ∈ D ∪ N, ∀ (fuel : ℕ) (p : ℕ) [NeZero p] (mode : RoundingMode),
    f fuel x p mode = roundVal p mode (val x)

/-- When every argument is known, the specification is unconditional. -/
theorem ZivSpec.eq_of_univ {α : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} {D N : Set α} (h : ZivSpec val f D N)
    (huniv : D ∪ N = Set.univ) (fuel : ℕ) (x : α) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    f fuel x p mode = roundVal p mode (val x) :=
  h.correct x (huniv ▸ Set.mem_univ x) fuel p mode

end Azurite.AzFloat
