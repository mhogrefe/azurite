/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect

/-! # BPR Section 2.1 — Exercise 2.1

Two parts:

* **(a)** Prove that `P ∈ K[X]` is separable if and only if `P` has no
  multiple root in `C`, where `C` is an algebraically closed field
  containing `K`. Mathlib expresses "no multiple root" as
  `(P.aroots C).Nodup`. The proof is a direct application of
  `Polynomial.nodup_aroots_iff_of_splits`, using `IsAlgClosed.splits`
  to show the mapped polynomial splits in `C`.

* **(b)** If the characteristic of `K` is 0, prove that `P ∈ K[X]` is
  separable if and only if `P` is square-free. Follows from
  `PerfectField.separable_iff_squarefree` since every field of
  characteristic 0 is a perfect field.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

omit [CharZero K] in
/-- **BPR Exercise 2.1(a).** P is separable iff P has no multiple root
    in an algebraically closed field C containing K. -/
theorem exercise_2_1a (P : K[X]) (hP : P ≠ 0) :
    P.Separable ↔ (P.aroots C).Nodup :=
  (nodup_aroots_iff_of_splits hP (IsAlgClosed.splits (P.map (algebraMap K C)))).symm

/-- **BPR Exercise 2.1(b).** In characteristic 0, P is separable iff P is square-free. -/
theorem exercise_2_1b (P : K[X]) :
    P.Separable ↔ Squarefree P :=
  PerfectField.separable_iff_squarefree

end Azurite.BPR
