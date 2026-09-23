/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Ring.SumsOfSquares

/-! # BPR §2.1 Exercise 2.10 — the real closure as a relative algebraic closure

If a field `F` is contained in a real closed field `R`, then the elements of `R` algebraic over `F`
form a real closed field — the real closure of `F` inside `R`. In Mathlib the algebraic elements
already form a field, `algebraicClosure F R` (so the "sum/product of algebraic is algebraic" hint via
Proposition 2.16 is automatic); the content here is that this relative algebraic closure is real
closed.

The proof mirrors Exercise 2.11 (`ℝ_alg = algebraicClosure ℚ ℝ`), generalized from `ℝ` to an
arbitrary real closed `R`, using the *algebraic* characterization of real-closedness (every element
or its negation is a square; every odd-degree polynomial has a root) — no order is needed. The key
closure step is that a square root, or a root of an odd-degree polynomial, of elements of
`algebraicClosure F R` is itself algebraic over `F` (transitivity of algebraicity), hence lies in
`algebraicClosure F R`. -/

namespace Azurite.BPR

open Polynomial

variable {F R : Type*} [Field F] [Field R] [Algebra F R] [IsRealClosed R]

omit [IsRealClosed R] in
/-- An element of `R` that is a root of a nonzero polynomial over `algebraicClosure F R` lies in
`algebraicClosure F R` (it is algebraic over `F` by transitivity). -/
theorem mem_algebraicClosure_of_root {f : (algebraicClosure F R)[X]} (hf : f ≠ 0) {r : R}
    (hr : (f.map (algebraMap (algebraicClosure F R) R)).IsRoot r) :
    r ∈ algebraicClosure F R := by
  rw [mem_algebraicClosure_iff]
  have halg : IsAlgebraic (algebraicClosure F R) r := ⟨f, hf, by rwa [aeval_def, ← eval_map]⟩
  exact (isAlgebraic_iff_isIntegral.mp halg).trans_isAlgebraic F

/-- Every element of `algebraicClosure F R`, or its negation, is a square. -/
theorem isSquare_or_isSquare_neg_algClosure (x : algebraicClosure F R) :
    IsSquare x ∨ IsSquare (-x) := by
  have key : ∀ z : algebraicClosure F R, IsSquare (algebraMap _ R z) → IsSquare z := by
    rintro z ⟨y, hy⟩
    have hr : ((X ^ 2 - C z).map (algebraMap (algebraicClosure F R) R)).IsRoot y := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, IsRoot.def, eval_sub,
        eval_pow, eval_X, eval_C]
      rw [hy]; ring
    exact ⟨⟨y, mem_algebraicClosure_of_root (X_pow_sub_C_ne_zero (by norm_num) z) hr⟩,
      Subtype.ext hy⟩
  rcases IsRealClosed.isSquare_or_isSquare_neg (algebraMap (algebraicClosure F R) R x) with h | h
  · exact Or.inl (key x h)
  · exact Or.inr (key (-x) (by rw [map_neg]; exact h))

/-- Every odd-degree polynomial over `algebraicClosure F R` has a root in `algebraicClosure F R`. -/
theorem exists_isRoot_of_odd_algClosure {f : (algebraicClosure F R)[X]} (hf : Odd f.natDegree) :
    ∃ r : algebraicClosure F R, f.IsRoot r := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hinj : Function.Injective (algebraMap (algebraicClosure F R) R) :=
    (algebraMap (algebraicClosure F R) R).injective
  have hdeg : (f.map (algebraMap (algebraicClosure F R) R)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective hinj f
  obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (f := f.map _) (hdeg ▸ hf)
  have hmem := mem_algebraicClosure_of_root hf0 hr
  refine ⟨⟨r, hmem⟩, ?_⟩
  apply Subtype.val_injective
  simp only [ZeroMemClass.coe_zero]
  change (algebraMap (algebraicClosure F R) R) (eval ⟨r, hmem⟩ f) = 0
  rw [show eval ⟨r, hmem⟩ f = eval₂ (RingHom.id _) ⟨r, hmem⟩ f from rfl,
    hom_eval₂ f (RingHom.id _) (algebraMap (algebraicClosure F R) R) ⟨r, hmem⟩]
  simp only [RingHom.comp_id]
  rw [← eval_map]
  exact hr

/-- **Exercise 2.10.** If `F` is contained in a real closed field `R`, the elements of `R` algebraic
over `F` form a real closed field (the real closure of `F` inside `R`). -/
theorem isRealClosed_algebraicClosure (F R : Type*) [Field F] [Field R] [Algebra F R]
    [IsRealClosed R] : IsRealClosed (algebraicClosure F R) := by
  have : IsSemireal (algebraicClosure F R) := by
    apply IsSemireal.of_not_isSumSq_neg_one
    intro h
    have hmap : ∀ {z : algebraicClosure F R}, IsSumSq z →
        IsSumSq (algebraMap (algebraicClosure F R) R z) := by
      intro z hz
      induction hz with
      | zero => simp
      | sq_add a _ ih => rw [map_add, map_mul]; exact IsSumSq.sq_add _ ih
    have hb := hmap h
    rw [map_neg, map_one] at hb
    exact absurd hb (IsSemireal.not_isSumSq_neg_one R)
  exact
    { isSquare_or_isSquare_neg := isSquare_or_isSquare_neg_algClosure
      exists_isRoot_of_odd_natDegree := fun hf => exists_isRoot_of_odd_algClosure hf }

end Azurite.BPR
