/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Exercise 1.7

Over an algebraically closed field $C$, every polynomial $P \in C[X]$
factors as
$P = (\operatorname{leadingCoeff}\,P) \cdot \prod_{x \in P\lcode{.roots}} (X - x)$.

The multiset $P\lcode{.roots}$ records roots with multiplicity, so this
encodes $P = a (X - x_1)^{\mu_1} \cdots (X - x_k)^{\mu_k}$. Uniqueness
is automatic since $P\lcode{.roots}$ is uniquely determined by $P$.
-/

namespace Azurite.BPR

open Polynomial

variable {C : Type*} [Field C] [IsAlgClosed C]

/-- Exercise 1.7: Over an algebraically closed field, every polynomial factors as
    `P = C(leadingCoeff P) * ∏ (X − C x)` for `x ∈ P.roots`. -/
theorem exercise_1_7 (P : C[X]) :
    P = Polynomial.C P.leadingCoeff *
      (Multiset.map (fun a => X - Polynomial.C a) P.roots).prod :=
  (C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.splits P).natDegree_eq_card_roots.symm).symm

end Azurite.BPR
