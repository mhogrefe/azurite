/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_3.Theorem_4_58

/-!
# BPR Theorem 4.59: rank and signature of `Her(P, 1)`

The `Q = 1` specialization of Theorem 4.58 (Hermite). Since `1` never vanishes, the rank of
`Her(P, 1)` counts *all* distinct roots of `P` in `C = R[i]`, and since `TaQ(1, P)` counts
the distinct real roots, the signature of `Her(P, 1)` is the number of distinct roots of `P`
in `R`.
-/

namespace Azurite.BPR.Chapter4

open _root_.Polynomial
open scoped Matrix
open Azurite.BPR Azurite.BPR.Theorem2_11

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR Theorem 4.59 (rank).** The rank of `Her(P, 1)` is the number of distinct roots of
`P` in `C = R[i]`. -/
theorem theorem_4_59_rank (P : R[X]) (hP : P.Monic) :
    quadraticFormRank (HerMatR P 1) = (P.aroots (Ri R)).toFinset.card := by
  rw [theorem_4_58_rank P 1 hP,
    Finset.filter_true_of_mem (fun x _ => by rw [map_one]; exact one_ne_zero)]

/-- **BPR Theorem 4.59 (signature).** The signature of `Her(P, 1)` is the number of distinct
roots of `P` in `R`. -/
theorem theorem_4_59_sign (P : R[X]) (hP : P.Monic) :
    Sign (quadraticForm (HerMatR P 1)) = (P.roots.toFinset.card : ℤ) := by
  rw [theorem_4_58_sign P 1 hP, tarskiQuery_eq_sum_roots]
  simp only [Polynomial.eval_one, sign_one, SignType.coe_one, Finset.sum_const, nsmul_eq_mul,
    mul_one]

end Azurite.BPR.Chapter4
