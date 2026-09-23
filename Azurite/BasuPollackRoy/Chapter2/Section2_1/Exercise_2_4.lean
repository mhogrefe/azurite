/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.FieldSimp

/-! # BPR Section 2.1 — Exercise 2.4: Uniqueness of the 0₊ order

> Show that 0₊ is the only order on F[X] in which ε is positive
> infinitesimal over F.

We formalise this as: any positivity predicate `pos` on `F[X]`
satisfying the ordered-ring axioms + "X is positive infinitesimal"
must agree with `polyPos` (the 0₊ positivity predicate, i.e.\
`pos P ↔ 0 < P.trailingCoeff` for nonzero `P`).
-/

namespace Azurite.BPR

open Polynomial

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **Exercise 2.4.** The 0₊ order is the unique order on F[X] making ε
    positive infinitesimal: any positivity predicate satisfying the
    ordered-ring axioms with X infinitesimal agrees with `polyPos`. -/
theorem exercise_2_4
    (pos : F[X] → Prop)
    (pos_add : ∀ {a b}, pos a → pos b → pos (a + b))
    (pos_mul : ∀ {a b}, pos a → pos b → pos (a * b))
    (pos_tri : ∀ a, pos a ∨ a = 0 ∨ pos (-a))
    (pos_antisymm : ∀ {a}, pos a → ¬ pos (-a))
    (hC : ∀ {a : F}, 0 < a → pos (C a))
    (hε_pos : pos X)
    (hε_inf : ∀ {a : F}, 0 < a → pos (C a - X))
    (P : F[X]) (hP : P ≠ 0) :
    pos P ↔ 0 < P.trailingCoeff := by
  -- Helper facts
  have not_pos_zero : ¬ pos 0 := fun h => pos_antisymm h (by rwa [neg_zero])
  have pos_C_iff : ∀ {a : F}, a ≠ 0 → (pos (C a) ↔ 0 < a) := by
    intro a ha
    exact ⟨fun h => by
      by_contra hle; push Not at hle
      exact pos_antisymm h (by rw [← map_neg]; exact hC (neg_pos.mpr (lt_of_le_of_ne hle ha))),
      fun h => hC h⟩
  -- X^k > 0 for k ≥ 1
  have pos_X_pow : ∀ k, 1 ≤ k → pos (X ^ k : F[X]) := by
    intro k hk; induction k with
    | zero => omega
    | succ n ih => cases n with
      | zero => simpa
      | succ m => rw [pow_succ]; exact pos_mul (ih (by omega)) hε_pos
  -- X^k < C(a) for k ≥ 1 and a > 0
  have pos_C_sub_X_pow : ∀ k, 1 ≤ k → ∀ {a : F}, 0 < a → pos (C a - X ^ k : F[X]) := by
    intro k hk; induction k with
    | zero => omega
    | succ n ih => intro a ha; cases n with
      | zero => simpa using hε_inf ha
      | succ m =>
        rw [show C a - X ^ (m + 2) =
            (C a - X ^ (m + 1)) + (X ^ (m + 1) * (C (1 : F) - X)) from by
          rw [map_one]; ring]
        exact pos_add (ih (by omega) ha)
          (pos_mul (pos_X_pow _ (by omega)) (by rw [map_one]; exact hε_inf one_pos))
  -- pos(a) → pos(a*b) ↔ pos(b)
  have pos_cancel : ∀ {a b : F[X]}, pos a → (pos (a * b) ↔ pos b) := by
    intro a b ha
    constructor
    · intro hab
      rcases pos_tri b with hb | hb | hb
      · exact hb
      · exact absurd (by rw [hb, mul_zero] at hab; exact hab) not_pos_zero
      · have : pos (a * (-b)) := pos_mul ha hb
        rw [mul_neg] at this
        exact absurd this (pos_antisymm hab)
    · exact fun hb => pos_mul ha hb
  -- KEY LEMMA: X * Q is bounded by any positive constant
  have mul_X_bounded : ∀ Q : F[X], ∀ {a : F}, 0 < a → pos (C a - X * Q) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q ihp ihq =>
      intro a ha
      have hsplit : C a - X * (p + q) = (C (a / 2) - X * p) + (C (a / 2) - X * q) := by
        have : C a = C (a / 2) + C (a / 2) := by rw [← map_add]; congr 1; field_simp; ring
        rw [this]; ring
      rw [hsplit]
      exact pos_add (ihp (half_pos ha)) (ihq (half_pos ha))
    | monomial n c =>
      intro a ha
      have hmon : X * monomial n c = C c * X ^ (n + 1) := by
        rw [← C_mul_X_pow_eq_monomial]; ring
      rw [hmon]
      by_cases hc : c = 0
      · simp [hc]; exact hC ha
      · rcases pos_tri (C c * X ^ (n + 1) : F[X]) with h | h | h
        · -- term > 0: show it's < C(a) via X^(n+1) < C(a/c)
          have hc_pos : (0 : F) < c := by
            rw [show C c * X ^ (n + 1) = X ^ (n + 1) * C c from mul_comm ..] at h
            rwa [pos_cancel (pos_X_pow _ (Nat.one_le_iff_ne_zero.mpr (by omega))),
                 pos_C_iff hc] at h
          rw [show C a - C c * X ^ (n + 1) = C c * (C (a / c) - X ^ (n + 1)) from by
            rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hc]]
          exact pos_mul (hC hc_pos) (pos_C_sub_X_pow _
            (Nat.one_le_iff_ne_zero.mpr (by omega)) (div_pos ha hc_pos))
        · -- term = 0: trivial
          rw [show C a - C c * X ^ (n + 1) = C a + -(C c * X ^ (n + 1)) from sub_eq_add_neg ..,
              h, neg_zero, add_zero]
          exact hC ha
        · -- term < 0: C(a) - term = C(a) + |term| > 0
          rw [show C a - C c * X ^ (n + 1) = C a + -(C c * X ^ (n + 1)) from sub_eq_add_neg ..]
          exact pos_add (hC ha) h
  -- MAIN PROOF
  -- Step 1: Factor P = X^m * Q where m = natTrailingDegree P
  have hdvd : X ^ P.natTrailingDegree ∣ P :=
    X_pow_dvd_iff.mpr (fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd)
  obtain ⟨Q, hQ⟩ := hdvd
  have hQne : Q ≠ 0 := right_ne_zero_of_mul (hQ ▸ hP)
  -- Q.coeff 0 = trailingCoeff P ≠ 0
  have hcm : (X ^ P.natTrailingDegree * Q).coeff P.natTrailingDegree = Q.coeff 0 := by
    have := coeff_X_pow_mul Q P.natTrailingDegree 0; simp at this; exact this
  have hQ0 : Q.coeff 0 = P.trailingCoeff := by
    rw [trailingCoeff]; rw [← hcm]
    exact congrArg (fun p => Polynomial.coeff p P.natTrailingDegree) hQ.symm
  have hQ0ne : Q.coeff 0 ≠ 0 := hQ0 ▸ trailingCoeff_nonzero_iff_nonzero.mpr hP
  -- Step 2: pos P ↔ pos Q
  have hfactor : pos P ↔ pos Q := by
    rw [hQ]
    rcases Nat.eq_zero_or_pos P.natTrailingDegree with hm | hm
    · rw [hm]; simp
    · exact pos_cancel (pos_X_pow _ hm)
  -- Step 3: Q = C(Q.coeff 0) + X * Q.divX
  have hQeq : Q = C (Q.coeff 0) + X * Q.divX := by
    ext n; cases n with
    | zero => simp [coeff_divX]
    | succ k => simp [coeff_divX, coeff_X_mul]
  -- Helper for splitting C(a) = C(a/2) + C(a/2)
  have half_split : ∀ (a : F) (S : F[X]),
      C a - X * S = C (a / 2) + (C (a / 2) - X * S) := by
    intro a S
    have : C a = C (a / 2) + C (a / 2) := by rw [← map_add]; congr 1; field_simp; ring
    rw [show C a - X * S = C a + (-X * S) from by ring,
        this, show C (a / 2) + C (a / 2) + -X * S = C (a / 2) + (C (a / 2) - X * S) from by ring]
  -- Step 4: pos Q ↔ 0 < Q.coeff 0
  have hQ_iff : pos Q ↔ 0 < Q.coeff 0 := by
    constructor
    · intro hposQ
      rcases lt_trichotomy (Q.coeff 0) 0 with hlt | heq | hgt
      · exfalso
        have hneg : pos (-Q) := by
          rw [hQeq, show -(C (Q.coeff 0) + X * Q.divX) = C (-(Q.coeff 0)) - X * Q.divX
            from by rw [map_neg]; ring, half_split]
          exact pos_add (hC (by linarith)) (mul_X_bounded _ (by linarith))
        exact pos_antisymm hposQ hneg
      · exact absurd heq.symm (Ne.symm hQ0ne)
      · exact hgt
    · intro hbpos
      rw [hQeq, show C (Q.coeff 0) + X * Q.divX = C (Q.coeff 0) - X * (-Q.divX) from by ring,
          half_split]
      exact pos_add (hC (by linarith)) (mul_X_bounded _ (by linarith))
  rw [hfactor, hQ_iff, hQ0]

end Azurite.BPR
