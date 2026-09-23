/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.RecursionStep

/-! # BPR §2.6 — invariants of the Puiseux root recursion

Towards Puiseux's theorem (Theorem 2.91), the construction iterates `P ↦ P₁ = substPoly P x ξ β`.
For the iteration to keep applying `recursion_step`, the degree must stay odd: `substPoly`
substitutes a degree-`1` polynomial and multiplies by a nonzero constant, so it preserves the
degree (`substPoly_natDegree`). Hence every `Pᵢ` has the same (odd) degree as `P`. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- **`substPoly` preserves degree.** `R(P, E, x, Y) = ε^{−β} P(ε^ξ(x + Y))` has the same degree as
`P`: it is `P` composed with the degree-`1` substitution `ε^ξ(x + Y)`, scaled by the nonzero
constant `ε^{−β}`. -/
theorem substPoly_natDegree (P : Polynomial (PuiseuxSeries R)) (x : R) (ξ β : ℚ) :
    (substPoly P x ξ β).natDegree = P.natDegree := by
  have hg : (C (puiseuxMonomial ξ) * (X + C (constPuiseux x)) :
      Polynomial (PuiseuxSeries R)).natDegree = 1 := by
    rw [natDegree_C_mul (puiseuxMonomial_ne_zero ξ), natDegree_X_add_C]
  rw [substPoly, natDegree_C_mul (puiseuxMonomial_ne_zero (-β)), natDegree_comp, hg, mul_one]

/-- The recentered polynomial keeps an odd degree, so `recursion_step` applies again. -/
theorem substPoly_odd_natDegree {P : Polynomial (PuiseuxSeries R)} (hodd : Odd P.natDegree)
    (x : R) (ξ β : ℚ) : Odd (substPoly P x ξ β).natDegree := by
  rw [substPoly_natDegree]; exact hodd

/-- **The evaluation telescoping relation.** `P(ε^ξ(x + y)) = ε^β · P₁(y)` where
`P₁ = substPoly P x ξ β`. This is what lets one track `P(x̄)` across the recursion: substituting
`y = ε^{ξ₂}(x₂ + …)` recursively expresses `P` at the accumulated root in terms of the recentered
`Pᵢ`, and at `y = 0` it gives the barrier identity `P(ε^ξ x) = ε^β · P₁(0)`. -/
theorem substPoly_eval (P : Polynomial (PuiseuxSeries R)) (x : R) (ξ β : ℚ)
    (y : PuiseuxSeries R) :
    P.eval (puiseuxMonomial ξ * (constPuiseux x + y))
      = puiseuxMonomial β * (substPoly P x ξ β).eval y := by
  have hsub : (substPoly P x ξ β).eval y
      = puiseuxMonomial (-β) * P.eval (puiseuxMonomial ξ * (constPuiseux x + y)) := by
    rw [substPoly, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_add, eval_X, eval_C,
      add_comm y (constPuiseux x)]
  rw [hsub, ← mul_assoc, puiseuxMonomial_mul, add_neg_cancel, puiseuxMonomial_zero, one_mul]

end Azurite.BPR
