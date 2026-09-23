/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.RecursionStep
import Azurite.BasuPollackRoy.Chapter2.Section2_6.NegSlopeEdge
import Azurite.BasuPollackRoy.Chapter2.Section2_6.CharPolyDegree

/-! # BPR §2.6 — the negative-slope recursion step

The recursion's continuation step (`i ≥ 1`): given `Pᵢ` with the order structure produced by the
previous step (`o(b_r) = 0`, `o(b_i) > 0` for `i < r`, `o ≥ 0`, `r` odd) and nonzero constant term,
select a *negative-slope* odd edge over `[0, r]` (`exists_neg_slope_odd_edge`) and recenter. This
yields the next multiplicity `r' ≤ r` (multiplicities are **non-increasing**) and `β > 0` (so the
order increments accumulate), together with the order conclusions of Lemma 2.95. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [IsRealClosed R]

/-- **The negative-slope recursion step.** From `Pᵢ` (continue case, with the order structure of a
recentered polynomial) we obtain `x ≠ 0`, `ξ`, `β`, and odd `r' ≤ r` with `β > 0`, so that
`P_{i+1} = substPoly Pᵢ x ξ β` satisfies Lemma 2.95. -/
theorem recursion_step_neg {P : Polynomial (PuiseuxSeries R)} {r : ℕ}
    (hr_odd : Odd r) (h0 : P.coeff 0 ≠ 0)
    (hbr : puiseuxOrder R (P.coeff r) = (0 : WithTop ℚ))
    (hbi : ∀ i, i < r → 0 < puiseuxOrder R (P.coeff i))
    (hge : ∀ i, (0 : WithTop ℚ) ≤ puiseuxOrder R (P.coeff i)) :
    ∃ (x : R) (ξ β : ℚ) (A B : ℕ × ℚ), x ≠ 0 ∧ A.1 < B.1 ∧ B.1 ≤ r ∧ 0 < β ∧ 0 < ξ ∧
      puiseuxOrder R (P.coeff A.1) = (A.2 : WithTop ℚ) ∧
      puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ) ∧ ξ = -(newtonSlope A B) ∧
      β = A.2 + (A.1 : ℚ) * ξ ∧
      Odd ((charPoly P A B).rootMultiplicity x) ∧ (charPoly P A B).rootMultiplicity x ≤ r ∧
      (∀ i, 0 ≤ puiseuxOrder R ((substPoly P x ξ β).coeff i)) ∧
      (∀ i < (charPoly P A B).rootMultiplicity x,
        0 < puiseuxOrder R ((substPoly P x ξ β).coeff i)) ∧
      puiseuxOrder R ((substPoly P x ξ β).coeff ((charPoly P A B).rootMultiplicity x)) = 0 ∧
      (∀ y : PuiseuxSeries R, 0 < puiseuxOrder R y →
        (β : WithTop ℚ) <
          puiseuxOrder R (P.eval (puiseuxMonomial ξ * (constPuiseux x + y)))) := by
  obtain ⟨A, B, hABlt, hBr, hABodd, hslope, hcolA, hcolB, hsupport, honseg⟩ :=
    exists_neg_slope_odd_edge hr_odd h0 hbr hbi hge
  have hABr : A.1 < r := lt_of_lt_of_le hABlt hBr
  set ξ := -(newtonSlope A B) with hξdef
  have hξ : newtonSlope A B = -ξ := by rw [hξdef, neg_neg]
  have hξpos : 0 < ξ := by rw [hξdef]; exact neg_pos.mpr hslope
  set β := A.2 + (A.1 : ℚ) * ξ with hβdef
  have hA2pos : 0 < A.2 := by
    have := hbi A.1 hABr; rw [hcolA] at this; exact_mod_cast this
  have hβpos : 0 < β := by
    have hnn : (0 : ℚ) ≤ (A.1 : ℚ) * ξ := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hξpos)
    rw [hβdef]; linarith
  have hQne : charPoly P A B ≠ 0 := charPoly_ne_zero hABlt hcolB
  have hspan : Odd ((charPoly P A B).natDegree - (charPoly P A B).natTrailingDegree) := by
    rw [charPoly_natDegree_eq hABlt hcolB, charPoly_natTrailingDegree_eq hABlt hcolA hcolB]
    exact hABodd
  obtain ⟨x, hx0, hxr⟩ := exists_ne_zero_odd_rootMultiplicity_of_span hQne hspan
  have hxroot : (charPoly P A B).IsRoot x :=
    (rootMultiplicity_pos hQne).mp (by obtain ⟨k, hk⟩ := hxr; omega)
  have hrle : (charPoly P A B).rootMultiplicity x ≤ r :=
    le_trans (charPoly_rootMultiplicity_le hABlt hcolB x) hBr
  obtain ⟨ha1, ha2, ha3⟩ := lemma_2_95a (x := x) hξ hβdef hsupport honseg hQne
  exact ⟨x, ξ, β, A, B, hx0, hABlt, hBr, hβpos, hξpos, hcolA, hcolB, hξdef, hβdef, hxr, hrle, ha1,
    ha2, ha3, fun y hy => lemma_2_95b hξ hβdef hsupport honseg hQne hxroot y hy⟩

end Azurite.BPR
