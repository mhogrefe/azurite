/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# BPR Section 1.3 — Specialization `P_y(X)`

Given `P ∈ C[Y₁, …, Y_k, X]` and a point `y ∈ C^k`, the specialization
`specialize y P : C[X]` is the univariate polynomial obtained by
substituting `Y_i ↦ y_i` while leaving `X` symbolic. This implements
BPR's notation `P_y(X)`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {C : Type*} [Field C]

/-- BPR notation `P_y(X)`: specialize the first `k` variables of
`P ∈ C[Y₁, …, Y_k, X]` at `y ∈ C^k`, leaving the last variable `X`
symbolic. Concretely, `Y_i ↦ y_i` and `X ↦ X`. -/
noncomputable def specialize (y : Fin k → C)
    (P : MvPolynomial (Fin (k+1)) C) : Polynomial C :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin (k+1) =>
      Fin.lastCases (motive := fun _ => Polynomial C)
        Polynomial.X
        (fun j : Fin k => Polynomial.C (y j))
        i) P

@[simp] theorem specialize_C (y : Fin k → C) (c : C) :
    specialize y (MvPolynomial.C c : MvPolynomial (Fin (k+1)) C) =
      Polynomial.C c := by
  simp [specialize]

@[simp] theorem specialize_X_last (y : Fin k → C) :
    specialize y (MvPolynomial.X (Fin.last k) :
      MvPolynomial (Fin (k+1)) C) = Polynomial.X := by
  simp [specialize]

@[simp] theorem specialize_X_castSucc (y : Fin k → C) (j : Fin k) :
    specialize y (MvPolynomial.X j.castSucc :
      MvPolynomial (Fin (k+1)) C) = Polynomial.C (y j) := by
  simp [specialize]

/-- Evaluating the specialization `P_y(X)` at `x` recovers
`P(y₁, …, y_k, x)`, i.e. `MvPolynomial.eval (Fin.snoc y x) P`. This
is the key compatibility relating BPR's `P_y(X)` notation to direct
multivariate evaluation at a concatenated point. -/
theorem eval_specialize (y : Fin k → C) (x : C)
    (P : MvPolynomial (Fin (k+1)) C) :
    Polynomial.eval x (specialize y P) =
      MvPolynomial.eval (Fin.snoc y x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [specialize]
  | add p q hp hq =>
    simp only [specialize, MvPolynomial.eval₂_add, Polynomial.eval_add,
      MvPolynomial.eval_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i ih =>
    simp only [specialize, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.eval_mul,
      MvPolynomial.eval_X, Polynomial.eval_mul] at ih ⊢
    rw [ih]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]

end Azurite.BPR
