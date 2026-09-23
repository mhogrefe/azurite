/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_32
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots

/-! # BPR Section 2.2 — Notation 2.34: Sign variations of a polynomial sequence at a point

> Let `P = P₀, …, P_d` be a sequence of polynomials in `R[X]` and let
> `a ∈ R ∪ {−∞, +∞}`. The number of sign variations of `P` at `a`, denoted
> `Var(P; a)`, is `Var(P₀(a), …, P_d(a))`. At `a = ±∞` the signs to consider
> are those of the leading monomials (Proposition 2.4): for `x → +∞` the
> sign of `P_i(x)` stabilises to `sign(leadingCoeff P_i)`, and for `x → −∞`
> to `sign((−1)^(natDegree P_i) · leadingCoeff P_i)`.

This file additionally records BPR's surrounding unnumbered notations:

* `varPoly P := Var (a₀, …, aₚ)`, the number of sign variations in the
  coefficient sequence of a univariate `P ∈ R[X]`;
* `posRoots P`, the number of positive real roots of `P` counted with
  multiplicity;
* `varBetween P a b := Var(P; a) − Var(P; b)`, the change in sign-variation
  count between two extended points;
* `numRoots P a b`, the number of roots of `P` in the half-open interval
  `(a, b] ⊆ R`, counted with multiplicity, with `a, b : ExtendedPoint R`.

The supporting type `ExtendedPoint R` represents `R ∪ {−∞, +∞}`; its
`evalPoly` evaluates a polynomial by returning `P(a)` at finite points and a
sign-representative leading-monomial value at the two infinities, in
agreement with Proposition 2.4 on the ultimate sign of `P` at large `|x|`.

The file also includes the BPR worked example
`Var(X⁵, X² − 1, 0, X² − 1, X + 2, 1; 1) = 0`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*}

/-! ## `Var(P)` and `pos(P)` for a univariate polynomial -/

/-- **BPR notation.** For `P = aₚ Xᵖ + ⋯ + a₀ ∈ R[X]`, `Var(P)` is the
    number of sign variations in the coefficient sequence `a₀, …, aₚ`. -/
noncomputable def varPoly [Semiring R] [LinearOrder R] (P : R[X]) : ℕ :=
  Var ((List.range (P.natDegree + 1)).map P.coeff)

/-- **BPR notation.** For `P ∈ R[X]`, `pos(P)` is the number of positive
    real roots of `P`, counted with multiplicity. (Follows Mathlib's
    convention `Polynomial.roots 0 = ∅`, so `pos(0) = 0`.) -/
noncomputable def posRoots [CommRing R] [IsDomain R] [LinearOrder R]
    (P : R[X]) : ℕ :=
  Multiset.card (P.roots.filter (0 < ·))

/-! ## Notation 2.34: Sign variations of a polynomial sequence at a point -/

/-- An element of `R ∪ {−∞, +∞}`, used as the evaluation point for
    `varAt` (BPR Notation 2.34). -/
inductive ExtendedPoint (R : Type*)
  | finite (a : R) : ExtendedPoint R
  | posInf : ExtendedPoint R
  | negInf : ExtendedPoint R
  deriving DecidableEq

namespace ExtendedPoint

/-- Evaluation of `P ∈ R[X]` at an extended point.

    At a finite `a` this is `P(a)`. At `±∞` it returns a representative
    whose sign agrees with the sign of `P(x)` for `|x|` sufficiently large,
    by Proposition 2.4:

    - at `+∞`, `sign(P(x)) = sign(aₚ · x^p) = sign(aₚ)` for `x → +∞`, so
      return `leadingCoeff P`;
    - at `−∞`, `sign(P(x)) = sign(aₚ · x^p) = sign((−1)^p · aₚ)` for
      `x → −∞`, so return `(−1)^(natDegree P) · leadingCoeff P`.

    For `P = 0` the return value is `0`, matching `sign(0) = 0`. -/
noncomputable def evalPoly [Ring R] (P : R[X]) : ExtendedPoint R → R
  | .finite a => P.eval a
  | .posInf   => P.leadingCoeff
  | .negInf   => (-1) ^ P.natDegree * P.leadingCoeff

end ExtendedPoint

/-- **BPR Notation 2.34.** The number of sign variations of a sequence of
    polynomials `P = P₀, …, P_d` at a point `a ∈ R ∪ {−∞, +∞}`,
    `Var(P; a) = Var(P₀(a), …, P_d(a))`, where at `a = ±∞` the signs to
    consider are those of the leading monomials (Proposition 2.4). -/
noncomputable def varAt [Ring R] [LinearOrder R]
    (P : List R[X]) (a : ExtendedPoint R) : ℕ :=
  Var (P.map (ExtendedPoint.evalPoly · a))

section

variable [Ring R] [LinearOrder R]

lemma varAt_finite (P : List R[X]) (a : R) :
    varAt P (ExtendedPoint.finite a) = Var (P.map (fun Q => Q.eval a)) := rfl

lemma varAt_posInf (P : List R[X]) :
    varAt P ExtendedPoint.posInf = Var (P.map Polynomial.leadingCoeff) := rfl

lemma varAt_negInf (P : List R[X]) :
    varAt P ExtendedPoint.negInf =
      Var (P.map (fun Q => (-1) ^ Q.natDegree * Q.leadingCoeff)) := rfl

@[simp] lemma varAt_nil (a : ExtendedPoint R) : varAt ([] : List R[X]) a = 0 := rfl

end

/-! ### Worked example (BPR Notation 2.34)

`Var(X⁵, X² − 1, 0, X² − 1, X + 2, 1; 1) = 0`: evaluating at `1` gives the
sequence `1, 0, 0, 0, 3, 1`; dropping zeros yields `1, 3, 1`, with no sign
changes. -/

example :
    varAt ([X ^ 5, X ^ 2 - 1, 0, X ^ 2 - 1, X + 2, 1] : List ℤ[X])
      (ExtendedPoint.finite 1) = 0 := by
  simp [varAt_finite, Var, varNonzero]

/-! ## `Var(P; a, b)` and `num(P; (a, b])` -/

/-- **BPR notation.** `Var(P; a, b) = Var(P; a) − Var(P; b)`, the change in
    sign-variation count of a polynomial sequence `P` between two extended
    points `a, b ∈ R ∪ {−∞, +∞}`. Takes values in `ℤ` because the two
    `varAt` counts need not be comparable in general. -/
noncomputable def varBetween [Ring R] [LinearOrder R]
    (P : List R[X]) (a b : ExtendedPoint R) : ℤ :=
  (varAt P a : ℤ) - (varAt P b : ℤ)

/-- **BPR notation.** `num(P; (a, b])` is the number of roots of `P` in the
    half-open interval `(a, b] ⊆ R`, counted with multiplicity, where
    `a, b : ExtendedPoint R`. Conventions:

    - `a = +∞` or `b = −∞` gives the empty interval, so `0`;
    - `a = −∞, b = +∞` covers all of `R`, so the total root count of `P`;
    - finite `a, b` use `{r | a < r ∧ r ≤ b}`;
    - `a = finite a', b = +∞` uses `{r | a' < r}`;
    - `a = −∞, b = finite b'` uses `{r | r ≤ b'}`. -/
noncomputable def numRoots [CommRing R] [IsDomain R] [LinearOrder R]
    (P : R[X]) : ExtendedPoint R → ExtendedPoint R → ℕ
  | .posInf,   _           => 0
  | .negInf,   .negInf     => 0
  | .finite _, .negInf     => 0
  | .negInf,   .posInf     => Multiset.card P.roots
  | .finite a, .posInf     => Multiset.card (P.roots.filter (a < ·))
  | .negInf,   .finite b   => Multiset.card (P.roots.filter (· ≤ b))
  | .finite a, .finite b   =>
      Multiset.card (P.roots.filter (fun r => a < r ∧ r ≤ b))

end Azurite.BPR
