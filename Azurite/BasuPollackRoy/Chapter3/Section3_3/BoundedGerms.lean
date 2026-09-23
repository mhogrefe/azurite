/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_3.Theorem_3_14
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Proposition_2_99

/-! # BPR §3.3 — bounded germs and the valuation ring `R⟨ε⟩_b`

The subring of germs of semialgebraic continuous functions at the right of the origin that are
bounded by an element of `R` coincides, under the isomorphism `R⟨ε⟩ ≅ algebraicPuiseux R`
(Theorem 3.14), with the valuation ring `R⟨ε⟩_b = puiseuxBounded R` of Chapter 2 (Notation 2.100).

The key point is that any `R(ε)`-algebra isomorphism between the two real closed fields is
automatically order-preserving (it preserves squares, and in a real closed field nonnegativity is
being a square) and fixes `R`, so "bounded by an element of `R`" is transported across it. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

section Iso

variable (e : SemialgGerm R ≃ₐ[RatFunc R] algebraicPuiseux R)

/-- An `R(ε)`-algebra isomorphism of the two real closed fields preserves nonnegativity: it preserves
squares, and nonnegativity is being a square. -/
theorem algEquiv_nonneg_iff (x : SemialgGerm R) : 0 ≤ e x ↔ 0 ≤ x := by
  have : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  rw [IsRealClosed.nonneg_iff_isSquare, IsRealClosed.nonneg_iff_isSquare]
  constructor
  · rintro ⟨s, hs⟩; exact ⟨e.symm s, by rw [← e.symm_apply_apply x, hs, map_mul]⟩
  · rintro ⟨r, hr⟩; exact ⟨e r, by rw [hr, map_mul]⟩

theorem algEquiv_pos_iff (x : SemialgGerm R) : 0 < e x ↔ 0 < x := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, algEquiv_nonneg_iff, ← map_zero e, e.injective.ne_iff]

/-- The isomorphism is strictly monotone. -/
theorem algEquiv_lt_iff (x y : SemialgGerm R) : e x < e y ↔ x < y := by
  rw [← sub_pos, ← map_sub, algEquiv_pos_iff, sub_pos]

/-- The isomorphism fixes `R` (it is an `R(ε)`-algebra map, and `R ⊆ R(ε)`). -/
theorem algEquiv_algebraMap (a : R) :
    e (algebraMap R (SemialgGerm R) a) = algebraMap R (algebraicPuiseux R) a := by
  have : IsScalarTower R (RatFunc R) (algebraicPuiseux R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [IsScalarTower.algebraMap_apply R (RatFunc R) (SemialgGerm R), e.commutes,
    ← IsScalarTower.algebraMap_apply R (RatFunc R) (algebraicPuiseux R)]

end Iso

/-! ### The subring of bounded germs -/

/-- A germ is **bounded by an element of `R`** if its absolute value is `< a` for some `a ∈ R`. -/
def IsBoundedGerm (x : SemialgGerm R) : Prop :=
  ∃ a : R, 0 < a ∧ |x| < algebraMap R (SemialgGerm R) a

/-- **The subring of germs bounded by an element of `R`.** -/
noncomputable def boundedGerms : Subring (SemialgGerm R) where
  carrier := {x | IsBoundedGerm x}
  zero_mem' := ⟨1, one_pos, by rw [abs_zero, map_one]; exact zero_lt_one⟩
  one_mem' := ⟨2, two_pos, by
    rw [abs_one, show (algebraMap R (SemialgGerm R)) 2 = 2 by rw [map_ofNat]]
    exact one_lt_two⟩
  add_mem' := fun {x y} ⟨a, ha, hx⟩ ⟨b, hb, hy⟩ =>
    ⟨a + b, by positivity, by
      rw [map_add]
      exact (abs_add_le x y).trans_lt (add_lt_add hx hy)⟩
  mul_mem' := fun {x y} ⟨a, ha, hx⟩ ⟨b, hb, hy⟩ =>
    ⟨a * b, by positivity, by
      rw [map_mul, abs_mul]
      exact mul_lt_mul'' hx hy (abs_nonneg x) (abs_nonneg y)⟩
  neg_mem' := fun {x} ⟨a, ha, hx⟩ => ⟨a, ha, by rwa [abs_neg]⟩

@[simp] theorem mem_boundedGerms {x : SemialgGerm R} : x ∈ boundedGerms ↔ IsBoundedGerm x := Iff.rfl

/-- The constant-`a` representative on `(0, 1)`. -/
noncomputable def constGermRep (a : R) : SemialgGermRep R :=
  ⟨1, one_pos, fun _ => a, isSemialgContinuousOn_const a⟩

theorem constGermRep_germ (a : R) : (constGermRep a).germ = algebraMap R (SemialgGerm R) a := by
  show (constGermRep a).germ = constGermHom a
  rw [SemialgGermRep.germ, constGermHom, RingHom.comp_apply, germHom_apply]
  exact Quotient.sound ⟨1, one_pos, fun _ _ _ => rfl⟩

/-- **A germ is bounded by an element of `R` iff a representative is eventually bounded.** This is
the germ-order ↔ eventual-pointwise-order correspondence (`germ_lt_eventually`); since all
representatives of a germ agree near `0`, the property does not depend on the representative. -/
theorem isBoundedGerm_germ_iff (f : SemialgGermRep R) :
    IsBoundedGerm f.germ
      ↔ ∃ a : R, ∃ t : R, 0 < t ∧ ∀ s : R, 0 < s → s < t → |f.toFun (constPt s)| < a := by
  constructor
  · rintro ⟨a, _, hlt⟩
    rw [abs_lt] at hlt
    rw [← constGermRep_germ] at hlt
    rw [show -(constGermRep a).germ = (constGermRep (-a)).germ from by
      rw [constGermRep_germ, constGermRep_germ, map_neg]] at hlt
    obtain ⟨t₂, ht₂, H₂⟩ := germ_lt_eventually hlt.1
    obtain ⟨t₁, ht₁, H₁⟩ := germ_lt_eventually hlt.2
    refine ⟨a, min t₁ t₂, lt_min ht₁ ht₂, fun s hs hst => ?_⟩
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · have := H₂ s hs (lt_of_lt_of_le hst (min_le_right _ _))
      simpa [constGermRep] using this
    · have := H₁ s hs (lt_of_lt_of_le hst (min_le_left _ _))
      simpa [constGermRep] using this
  · rintro ⟨a, t, ht, hb⟩
    have ha : 0 < a := lt_of_le_of_lt (abs_nonneg _) (hb (t / 2) (by positivity) (by linarith))
    refine ⟨a, ha, ?_⟩
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · rw [show -(algebraMap R (SemialgGerm R) a) = (constGermRep (-a)).germ from by
        rw [constGermRep_germ, map_neg]]
      exact germ_lt_of_eventually ⟨t, ht, fun s hs hst => by
        simpa [constGermRep] using (abs_lt.mp (hb s hs hst)).1⟩
    · rw [← constGermRep_germ]
      exact germ_lt_of_eventually ⟨t, ht, fun s hs hst => by
        simpa [constGermRep] using (abs_lt.mp (hb s hs hst)).2⟩

/-- **A germ is bounded by an element of `R` iff it has a bounded representative.** -/
theorem isBoundedGerm_iff_exists_bounded_rep (x : SemialgGerm R) :
    IsBoundedGerm x ↔ ∃ (g : SemialgGermRep R) (a : R), x = g.germ ∧
      ∀ s : R, 0 < s → s < g.bound → |g.toFun (constPt s)| < a := by
  constructor
  · intro hx
    obtain ⟨f, rfl⟩ := Quotient.exists_rep x
    obtain ⟨a, t, ht, hb⟩ := (isBoundedGerm_germ_iff f).mp hx
    refine ⟨⟨min f.bound t, lt_min f.bound_pos ht, f.toFun,
      f.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd _)
        (rightNbhd_subset (min_le_left _ _))⟩, a,
      Quotient.sound ⟨min f.bound t, lt_min f.bound_pos ht, fun _ _ _ => rfl⟩,
      fun s hs hst => hb s hs (lt_of_lt_of_le hst (min_le_right _ _))⟩
  · rintro ⟨g, a, rfl, hb⟩
    exact (isBoundedGerm_germ_iff g).mpr ⟨a, g.bound, g.bound_pos, hb⟩

omit [IsRealClosed R] in
/-- An algebraic Puiseux series lies in `R⟨ε⟩_b` exactly when it is bounded between `±a` for some
`a ∈ R` (the intrinsic form of `mem_puiseuxBounded_iff_bounded`). -/
theorem mem_puiseuxBounded_iff_intrinsic (y : algebraicPuiseux R) :
    y ∈ puiseuxBounded R
      ↔ ∃ a : R, 0 < a ∧ -(algebraMap R (algebraicPuiseux R) a) < y
          ∧ y < algebraMap R (algebraicPuiseux R) a := by
  rw [mem_puiseuxBounded_iff_bounded]
  refine exists_congr fun a => and_congr_right fun _ => ?_
  have hcoe : ((algebraMap R (algebraicPuiseux R) a : algebraicPuiseux R) : PuiseuxSeries R)
      = algebraMap R (PuiseuxSeries R) a := by
    rw [algebraMap_algebraicPuiseux_coe, algebraMap_eq_constPuiseux]
  rw [abs_lt, ← hcoe, ← NegMemClass.coe_neg, Subtype.coe_lt_coe, Subtype.coe_lt_coe]

/-- **The bounded germs coincide with `R⟨ε⟩_b`.** Under any `R(ε)`-algebra isomorphism
`e : R⟨ε⟩ ≅ algebraicPuiseux R` (Theorem 3.14), a germ is bounded by an element of `R` iff its image
is in the valuation ring `puiseuxBounded R = R⟨ε⟩_b`. -/
theorem mem_boundedGerms_iff_mem_puiseuxBounded
    (e : SemialgGerm R ≃ₐ[RatFunc R] algebraicPuiseux R) (x : SemialgGerm R) :
    x ∈ boundedGerms ↔ e x ∈ puiseuxBounded R := by
  rw [mem_boundedGerms, mem_puiseuxBounded_iff_intrinsic]
  simp only [IsBoundedGerm]
  refine exists_congr fun a => and_congr_right fun _ => ?_
  rw [abs_lt]
  refine and_congr ?_ ?_
  · rw [← algEquiv_lt_iff e, map_neg, algEquiv_algebraMap]
  · rw [← algEquiv_lt_iff e, algEquiv_algebraMap]

/-- **The subring of bounded germs coincides with `R⟨ε⟩_b`** (BPR, following Notation 2.100). Under
the identification `R⟨ε⟩ ≅ algebraicPuiseux R` of Theorem 3.14, a germ is bounded by an element of `R`
exactly when its image lies in the valuation ring `puiseuxBounded R`. -/
theorem mem_boundedGerms_iff_image_mem_puiseuxBounded (x : SemialgGerm R) :
    x ∈ boundedGerms ↔ theorem_3_14.some x ∈ puiseuxBounded R :=
  mem_boundedGerms_iff_mem_puiseuxBounded theorem_3_14.some x

end Azurite.BPR
