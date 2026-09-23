/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.Lemma_2_95
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Lemma_2_97
import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonStrict
import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonOddEdge
import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonEdge
import Azurite.BasuPollackRoy.Chapter2.Section2_6.OddMultiplicityRoot

/-! # BPR §2.6 — one step of the Puiseux root construction

Assembling the pieces (Newton polygon existence + odd-length edge + edge data + odd-multiplicity
root + Lemma 2.95), one step of the construction: from `P` with nonzero constant term and odd
degree (over a real closed coefficient field) we obtain a slope `−ξ`, the constant `β`, a nonzero
root `x ∈ R` of odd multiplicity `r` of the characteristic polynomial, and the recentered
polynomial `P₁ = R(P, E, x, Y)` satisfying the order conclusions of Lemma 2.95 (`recursion_step`).
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [IsRealClosed R]

/-- **One step of the Puiseux construction.** Given `P` with `P.coeff 0 ≠ 0` and odd degree, there
are `x ≠ 0`, `ξ`, `β`, and odd `r` so that `P₁ = substPoly P x ξ β` satisfies Lemma 2.95:
`o(b̄_i) ≥ 0` for all `i`, `o(b̄_i) > 0` for `i < r`, `o(b̄_r) = 0`, and for any `o(y) > 0` one has
`o(P(ε^ξ(x + y))) > β`. -/
theorem recursion_step {P : Polynomial (PuiseuxSeries R)} (h0 : P.coeff 0 ≠ 0)
    (hodd : Odd P.natDegree) :
    ∃ (x : R) (ξ β : ℚ) (r : ℕ), x ≠ 0 ∧ Odd r ∧
      (∀ i, 0 ≤ puiseuxOrder R ((substPoly P x ξ β).coeff i)) ∧
      (∀ i < r, 0 < puiseuxOrder R ((substPoly P x ξ β).coeff i)) ∧
      puiseuxOrder R ((substPoly P x ξ β).coeff r) = 0 ∧
      (∀ y : PuiseuxSeries R, 0 < puiseuxOrder R y →
        (β : WithTop ℚ) <
          puiseuxOrder R (P.eval (puiseuxMonomial ξ * (constPuiseux x + y)))) := by
  classical
  obtain ⟨M, hM, hhonM⟩ := exists_isNewtonPolygon_honseg P h0
  obtain ⟨A, B, hAB_zip, hABodd⟩ := exists_odd_length_edge hM hodd
  have hABlt : A.1 < B.1 := newtonEdge_fst_lt hM hAB_zip
  have hcolA : puiseuxOrder R (P.coeff A.1) = (A.2 : WithTop ℚ) :=
    newtonEdge_colPoint_left hM hAB_zip
  have hcolB : puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ) :=
    newtonEdge_colPoint_right hM hAB_zip
  have hsupport := newtonEdge_hsupport hM hAB_zip
  have honseg : ∀ h, colOnLine P A B h → A.1 ≤ h ∧ h ≤ B.1 := hhonM A B hAB_zip
  set ξ := -(newtonSlope A B) with hξdef
  have hξ : newtonSlope A B = -ξ := by rw [hξdef, neg_neg]
  set β := A.2 + (A.1 : ℚ) * ξ with hβdef
  have hAmem : A.1 ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl _, le_of_lt hABlt⟩, colOnLine_left hcolA⟩
  have hBmem : B.1 ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_of_lt hABlt, le_refl _⟩,
      colOnLine_right hABlt.ne hcolB⟩
  have hAne : (charPoly P A B).coeff A.1 ≠ 0 := by
    rw [charPoly_coeff, ite_eq_left hAmem]
    exact initCoeff_ne_zero_of_colOnLine (colOnLine_left (B := B) hcolA)
  have hBne : (charPoly P A B).coeff B.1 ≠ 0 := by
    rw [charPoly_coeff, ite_eq_left hBmem]
    exact initCoeff_ne_zero_of_colOnLine (colOnLine_right hABlt.ne hcolB)
  have hQne : charPoly P A B ≠ 0 := fun h => hBne (by rw [h, coeff_zero])
  have hQdeg : (charPoly P A B).natDegree = B.1 :=
    le_antisymm (charPoly_natDegree_le P A B) (le_natDegree_of_ne_zero hBne)
  have hQtrail : (charPoly P A B).natTrailingDegree = A.1 := by
    refine le_antisymm (natTrailingDegree_le_of_ne_zero hAne) (le_natTrailingDegree hQne ?_)
    intro m hm
    rw [charPoly_coeff, ite_eq_right]
    intro hmem
    exact absurd (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).1 (by omega)
  have hspan : Odd ((charPoly P A B).natDegree - (charPoly P A B).natTrailingDegree) := by
    rw [hQdeg, hQtrail]; exact hABodd
  obtain ⟨x, hx0, hxr⟩ := exists_ne_zero_odd_rootMultiplicity_of_span hQne hspan
  have hxroot : (charPoly P A B).IsRoot x :=
    (rootMultiplicity_pos hQne).mp (by obtain ⟨k, hk⟩ := hxr; omega)
  obtain ⟨ha1, ha2, ha3⟩ := lemma_2_95a (x := x) hξ hβdef hsupport honseg hQne
  exact ⟨x, ξ, β, (charPoly P A B).rootMultiplicity x, hx0, hxr, ha1, ha2, ha3,
    fun y hy => lemma_2_95b hξ hβdef hsupport honseg hQne hxroot y hy⟩

end Azurite.BPR
