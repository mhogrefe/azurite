/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # BPR Section 2.1 — Intermediate value property

> A field `R` has the *intermediate value property* if `R` is an ordered
> field such that, for any `P ∈ R[X]`, if there exist `a, b ∈ R` with
> `a < b` and `P(a) · P(b) < 0`, then there exists `x ∈ (a, b)` such that
> `P(x) = 0`.

This is one of the four equivalent characterisations of real-closedness in
BPR Theorem 2.11.
-/

namespace Azurite.BPR

/-- **BPR Definition (p.38).** An ordered field `R` has the *intermediate value property*
    if, for every polynomial `P ∈ R[X]` and every pair `a < b` with `P(a) · P(b) < 0`,
    there exists `x ∈ (a, b)` such that `P(x) = 0`. -/
def HasIntermediateValueProperty (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    Prop :=
  ∀ (P : Polynomial R) (a b : R), a < b →
    Polynomial.eval a P * Polynomial.eval b P < 0 →
    ∃ x : R, a < x ∧ x < b ∧ Polynomial.eval x P = 0

end Azurite.BPR
