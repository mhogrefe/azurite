/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# BPR Section 1.3 — Splitting the last variable

For posgcd-style manipulations we need the opposite view of
`Section1_3.Specialize.specialize`: instead of evaluating `Y` at a
concrete point in `C^k`, we keep the `Y`-variables **symbolic** and
split off the last variable `X` as the polynomial variable. The
result is a univariate polynomial in `X` with coefficients in
`D[Y₁, …, Y_k]`. Unlike `MvPolynomial.finSuccEquiv` which splits
the *first* variable, `splitLast` splits the *last*.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {D : Type*} [CommRing D]

/-- `splitLast P` re-views `P ∈ D[Y₁, …, Y_k, X]` as an element of
`D[Y₁, …, Y_k][X]` by treating the last variable as the polynomial
variable and leaving the `Y`-variables symbolic. -/
noncomputable def splitLast :
    MvPolynomial (Fin (k+1)) D →+* Polynomial (MvPolynomial (Fin k) D) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i : Fin (k+1) =>
      Fin.lastCases (motive := fun _ => Polynomial (MvPolynomial (Fin k) D))
        Polynomial.X
        (fun j : Fin k => Polynomial.C (MvPolynomial.X j))
        i)

@[simp] theorem splitLast_C (d : D) :
    splitLast (MvPolynomial.C d : MvPolynomial (Fin (k+1)) D) =
      Polynomial.C (MvPolynomial.C d) := by
  simp [splitLast]

@[simp] theorem splitLast_X_last :
    splitLast (MvPolynomial.X (Fin.last k) :
      MvPolynomial (Fin (k+1)) D) = Polynomial.X := by
  simp [splitLast]

@[simp] theorem splitLast_X_castSucc (j : Fin k) :
    splitLast (MvPolynomial.X j.castSucc :
      MvPolynomial (Fin (k+1)) D) = Polynomial.C (MvPolynomial.X j) := by
  simp [splitLast]

/-- Compatibility of `splitLast` with evaluation: evaluating the
split/specialized polynomial at `x` recovers multivariate evaluation
at `Fin.snoc y x`. -/
theorem aeval_snoc_eq_eval_splitLast {C : Type*} [CommSemiring C] [Algebra D C]
    (y : Fin k → C) (x : C) (P : MvPolynomial (Fin (k+1)) D) :
    MvPolynomial.aeval (Fin.snoc y x) P =
      Polynomial.eval x
        ((splitLast P).map (MvPolynomial.aeval y).toRingHom) := by
  induction P using MvPolynomial.induction_on with
  | C d =>
    simp
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, Polynomial.eval_add]
    rw [hp, hq]
  | mul_X p i ih =>
    simp only [map_mul, MvPolynomial.aeval_X, Polynomial.map_mul,
      Polynomial.eval_mul]
    rw [ih]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]

end Azurite.BPR
