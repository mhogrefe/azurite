/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_3.BoundedGerms
import Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxLimit

/-! # BPR §3.3 — Proposition 3.18: continuous extension of a bounded semialgebraic function

A continuous bounded semialgebraic function `f : (0, a) → R` extends continuously to `[0, a)`: it has
a limit `b ∈ R` at `0⁺`. The limit is `b = lim_ε(ϕ)`, where `ϕ ∈ R⟨ε⟩` is the germ of `f` — bounded,
hence in the valuation ring `R⟨ε⟩_b`, where `lim_ε` is defined. Then `ϕ − b` is infinitesimal (the
defining property of `lim_ε`), so by the germ-order / eventual-pointwise correspondence,
`|f(t) − b| < r` for all small `t > 0`, which is exactly continuity of the extension at `0`. -/

namespace Azurite.BPR

open scoped Classical

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [IsRealClosed R] in
/-- An algebraic Puiseux series whose difference with `algebraMap x` has positive order is
infinitesimally close to `x`: it lies strictly between `algebraMap (x ± r)` for every `r > 0`. -/
theorem aP_infinitesimal (y : algebraicPuiseux R) (x : R)
    (h : 0 < puiseuxOrder R (((y : algebraicPuiseux R) : PuiseuxSeries R) - constPuiseux x))
    (r : R) (hr : 0 < r) :
    -(algebraMap R (algebraicPuiseux R) r) < y - algebraMap R (algebraicPuiseux R) x
      ∧ y - algebraMap R (algebraicPuiseux R) x < algebraMap R (algebraicPuiseux R) r := by
  have hP := infinitesimal_of_puiseuxOrder_pos h r hr
  rw [abs_lt] at hP
  have hcoeR : ((algebraMap R (algebraicPuiseux R) r : algebraicPuiseux R) : PuiseuxSeries R)
      = algebraMap R (PuiseuxSeries R) r := by
    rw [algebraMap_algebraicPuiseux_coe, algebraMap_eq_constPuiseux]
  have hcoeX : ((algebraMap R (algebraicPuiseux R) x : algebraicPuiseux R) : PuiseuxSeries R)
      = constPuiseux x := algebraMap_algebraicPuiseux_coe x
  have hsub : ((y - algebraMap R (algebraicPuiseux R) x : algebraicPuiseux R) : PuiseuxSeries R)
      = ((y : algebraicPuiseux R) : PuiseuxSeries R) - constPuiseux x := by
    rw [AddSubgroupClass.coe_sub, hcoeX]
  constructor
  · rw [← Subtype.coe_lt_coe, NegMemClass.coe_neg, hcoeR, hsub]; exact hP.1
  · rw [← Subtype.coe_lt_coe, hcoeR, hsub]; exact hP.2

/-- **BPR Proposition 3.18.** A continuous bounded semialgebraic function `f` on `(0, a)` has a limit
`b ∈ R` at `0⁺`: for every `r > 0` there is `δ > 0` with `|f(t) − b| < r` for all `t ∈ (0, δ)`. Hence
`f` extends continuously to `[0, a)` by `f(0) := b`. -/
theorem proposition_3_18 (a : R) (ha : 0 < a) (f : (Fin 1 → R) → R)
    (hf : IsSemialgContinuousOn (rightNbhd a) f) (M : R)
    (hbdd : ∀ s : R, 0 < s → s < a → |f (constPt s)| < M) :
    ∃ b : R, ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧
      ∀ s : R, 0 < s → s < δ → |f (constPt s) - b| < r := by
  have : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  let fRep : SemialgGermRep R := ⟨a, ha, f, hf⟩
  have hbound : IsBoundedGerm fRep.germ :=
    (isBoundedGerm_germ_iff fRep).mpr ⟨M, a, ha, hbdd⟩
  let e := (theorem_3_14 (R := R)).some
  have hmem : e fRep.germ ∈ puiseuxBounded R :=
    (mem_boundedGerms_iff_mem_puiseuxBounded e fRep.germ).mp hbound
  let b : R := puiseuxLim R ⟨e fRep.germ, hmem⟩
  have hord : 0 < puiseuxOrder R
      (((e fRep.germ : algebraicPuiseux R) : PuiseuxSeries R) - constPuiseux b) :=
    (puiseuxLim_eq_iff ⟨e fRep.germ, hmem⟩ b).mp rfl
  refine ⟨b, fun r hr => ?_⟩
  -- `ϕ − b` is infinitesimal: `|fRep.germ − b| < r` in the germ field.
  have hinf : |fRep.germ - algebraMap R (SemialgGerm R) b| < algebraMap R (SemialgGerm R) r := by
    obtain ⟨h1, h2⟩ := aP_infinitesimal (e fRep.germ) b hord r hr
    rw [abs_lt]
    have hediff : e (fRep.germ - algebraMap R (SemialgGerm R) b)
        = e fRep.germ - algebraMap R (algebraicPuiseux R) b := by rw [map_sub, algEquiv_algebraMap]
    exact ⟨by rw [← algEquiv_lt_iff e, map_neg, algEquiv_algebraMap, hediff]; exact h1,
      by rw [← algEquiv_lt_iff e, algEquiv_algebraMap, hediff]; exact h2⟩
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hinf
  -- rearrange to `b − r < ϕ < b + r` and compare representatives near `0`.
  have hgt : fRep.germ < (constGermRep (b + r)).germ := by rw [constGermRep_germ, map_add]; linarith
  have hlt : (constGermRep (b - r)).germ < fRep.germ := by rw [constGermRep_germ, map_sub]; linarith
  obtain ⟨t₁, ht₁, H₁⟩ := germ_lt_eventually hgt
  obtain ⟨t₂, ht₂, H₂⟩ := germ_lt_eventually hlt
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, fun s hs hst => ?_⟩
  have hA := H₁ s hs (lt_of_lt_of_le hst (min_le_left _ _))
  have hB := H₂ s hs (lt_of_lt_of_le hst (min_le_right _ _))
  simp only [constGermRep, show fRep.toFun = f from rfl] at hA hB
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

end Azurite.BPR
