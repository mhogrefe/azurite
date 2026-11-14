/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ziv

/-!
# Ziv's strategy for a pair of values

Two values that are approximated together (for instance `sin x` and `cos x`, whose brackets come
out of one computation) are rounded by one loop: `roundingPossible₂` answers when the rounding of
both is determined, and `zivLoopCertified₂` doubles the working precision until it does, under a
termination certificate as in `zivLoopCertified`.  Each level evaluates the joint approximation
once.
-/

namespace Azurite.AzFloat

/-- `roundingPossible` for two brackets at once: `some` of the two roundings when both are
determined. -/
def roundingPossible₂ (a : (Roundable × Roundable) × (Roundable × Roundable)) (p : Nat)
    (mode : RoundingMode) : Option ((AzFloat × Ordering) × (AzFloat × Ordering)) :=
  match roundingPossible a.1.1 a.1.2 p mode, roundingPossible a.2.1 a.2.2 p mode with
  | some r₁, some r₂ => some (r₁, r₂)
  | _, _ => none

/-- Ziv's loop for a pair of values with a **termination certificate**: `h` says that at some
working precision `w₀ · 2^f` both roundings are determined; the loop doubles the working
precision until the first such level. -/
def zivLoopCertified₂ (approx : Nat → (Roundable × Roundable) × (Roundable × Roundable))
    (p : Nat) (mode : RoundingMode) (w₀ : Nat)
    (h : ∃ f : Nat, (roundingPossible₂ (approx (w₀ * 2 ^ f)) p mode).isSome = true) :
    (AzFloat × Ordering) × (AzFloat × Ordering) :=
  go h 0 (fun _ hg => absurd hg (Nat.not_lt_zero _))
where
  go (h : ∃ f : Nat, (roundingPossible₂ (approx (w₀ * 2 ^ f)) p mode).isSome = true)
      (f : Nat)
      (hf : ∀ g < f, (roundingPossible₂ (approx (w₀ * 2 ^ g)) p mode).isSome = false) :
      (AzFloat × Ordering) × (AzFloat × Ordering) :=
    match hr : roundingPossible₂ (approx (w₀ * 2 ^ f)) p mode with
    | some r => r
    | none => go h (f + 1) (fun g hg => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg' | rfl
        · exact hf g hg'
        · rw [hr]; rfl)
  termination_by Nat.find h - f
  decreasing_by
    have hlt : f < Nat.find h := by
      by_contra hcon
      push Not at hcon
      have hspec := Nat.find_spec h
      rcases Nat.lt_or_eq_of_le hcon with hlt' | heq
      · rw [hf _ hlt'] at hspec; exact Bool.false_ne_true hspec
      · rw [heq, hr] at hspec; exact Bool.false_ne_true hspec
    omega

end Azurite.AzFloat
