/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.IsRealClosedOrder
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.IsRealClosed.Basic

/-! # BPR Section 2.1 — Notation 2.18: `R[i]`, conjugate, and modulus

> If `R` is real closed, `R[i] = R[T]/(T² + 1)` can be identified with `R²`.
> For `z = a + i b ∈ R[i]` with `a, b ∈ R`:
> * the *conjugate* of `z` is `z̄ = a − i b`;
> * the *modulus* of `z` is `|z| = √(a² + b²)`.

There is no `StarRing` or `normSq` instance on `AdjoinRoot` in Mathlib, and the
`RCLike` typeclass (which provides `conj`, `normSq`, and `‖·‖`) is designed for
`ℝ` and `ℂ` only — not for `R[i]` over an arbitrary real closed field. We
therefore define the conjugate, norm squared, and modulus directly on
`Ri R := AdjoinRoot (X² + 1)`.
-/

namespace Azurite.BPR

open Polynomial

/-- R[i] := R[X]/(X² + 1), the "complex numbers" over R. -/
noncomputable abbrev Ri (R : Type*) [CommRing R] :=
  AdjoinRoot (X ^ 2 + 1 : R[X])

/-- The imaginary unit `i` in R[i], i.e., the image of X in R[X]/(X² + 1). -/
noncomputable def Ri.i (R : Type*) [CommRing R] : Ri R :=
  AdjoinRoot.root (X ^ 2 + 1 : R[X])

/-- **Conjugation** on R[i]: the R-algebra endomorphism sending i ↦ −i (BPR: z̄ = a − ib). -/
noncomputable def Ri.conj (R : Type*) [CommRing R] : Ri R →ₐ[R] Ri R :=
  { AdjoinRoot.lift (AdjoinRoot.of (X ^ 2 + 1 : R[X])) (-Ri.i R)
      (by
        simp only [Ri.i, eval₂_add, eval₂_pow, eval₂_one, eval₂_X, neg_sq]
        have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : R[X])
        simpa [eval₂_add, eval₂_pow, eval₂_one, eval₂_X] using h) with
    commutes' := fun r => by simp [AdjoinRoot.lift_of] }

/-- Conjugation sends i to −i. -/
theorem Ri.conj_i (R : Type*) [CommRing R] : (Ri.conj R) (Ri.i R) = -Ri.i R := by
  simp [Ri.conj, Ri.i, AdjoinRoot.lift_root]

/-- Conjugation is an involution: conj(conj(z)) = z. -/
theorem Ri.conj_conj (R : Type*) [CommRing R] (z : Ri R) :
    (Ri.conj R) ((Ri.conj R) z) = z := by
  have : (Ri.conj R).comp (Ri.conj R) = AlgHom.id R (Ri R) := by
    apply AdjoinRoot.algHom_ext
    simp only [Ri.conj, AlgHom.comp_apply, AlgHom.coe_mk, Ri.i,
      AdjoinRoot.lift_root, map_neg, neg_neg, AlgHom.id_apply]
  exact AlgHom.congr_fun this z

/-- Conjugation is injective. -/
theorem Ri.conj_injective (R : Type*) [CommRing R] :
    Function.Injective (Ri.conj R : Ri R →+* Ri R) :=
  Function.HasLeftInverse.injective ⟨Ri.conj R, Ri.conj_conj R⟩

/-- The defining relation: i² = −1 in R[i]. -/
theorem Ri.i_sq (R : Type*) [CommRing R] :
    (Ri.i R) ^ 2 = -(1 : Ri R) := by
  have h : AdjoinRoot.mk (X ^ 2 + 1 : R[X]) (X ^ 2 + 1 : R[X]) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X] at h
  unfold Ri.i
  linear_combination h

/-- In a real closed field, −1 is not a square. -/
theorem not_isSquare_neg_one {R : Type*} [Field R] [IsRealClosed R] :
    ¬ IsSquare (-1 : R) := by
  intro h; exact IsSemireal.not_isSumSq_neg_one R h.isSumSq

/-- X² + 1 is irreducible over a real closed field R. -/
theorem irred_X_sq_add_one {R : Type*} [Field R] [IsRealClosed R] :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
      rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
    simp [this, Finset.mem_Icc]
  · intro x
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
    intro h
    have : (-1 : R) = x * x := by linear_combination -h
    exact not_isSquare_neg_one ⟨x, this⟩

/-- X² + 1 is irreducible (as a Fact, for `AdjoinRoot.instField`). -/
instance instFactIrred_X_sq_add_one (R : Type*) [Field R] [IsRealClosed R] :
    Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irred_X_sq_add_one⟩

/-- Every element of R[i] decomposes as ι(a) + ι(b) · i with a, b ∈ R. -/
theorem Ri.repr_exists {R : Type*} [CommRing R] [Nontrivial R] (z : Ri R) :
    ∃ a b : R, z = algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R := by
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    set f := (X : R[X]) ^ 2 + 1
    have hfm : f.Monic := monic_X_pow_add_C 1 (by norm_num : (2 : ℕ) ≠ 0)
    set r := p %ₘ f
    have hmk : AdjoinRoot.mk f p = AdjoinRoot.mk f r := by
      rw [AdjoinRoot.mk_eq_mk]
      exact ⟨p /ₘ f, by have := modByMonic_eq_sub_mul_div p f; linear_combination -this⟩
    have hr_deg : r.natDegree ≤ 1 := by
      have hrd : r.degree < f.degree := degree_modByMonic_lt p hfm
      have hf_deg : f.degree = 2 := by
        have hnat : f.natDegree = 2 := by
          simp [f]
        rw [Polynomial.degree_eq_natDegree hfm.ne_zero, hnat]; norm_num
      rw [hf_deg] at hrd
      by_cases hr : r = 0
      · simp [hr]
      · rw [Polynomial.degree_eq_natDegree hr] at hrd
        exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp (by exact_mod_cast hrd))
    have hr_decomp := Polynomial.eq_X_add_C_of_natDegree_le_one hr_deg
    rw [hmk, show AdjoinRoot.mk f r = Polynomial.aeval (Ri.i R) r from
      (AdjoinRoot.aeval_eq r).symm, hr_decomp]
    simp [Polynomial.aeval_def, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    exact ⟨r.coeff 0, r.coeff 1, by ring⟩

/-- The norm squared z · z̄ in R[i]. -/
noncomputable def Ri.normSq {R : Type*} [CommRing R] (z : Ri R) : Ri R :=
  z * Ri.conj R z

/-- normSq(a + bi) = ι(a² + b²). -/
theorem Ri.normSq_repr {R : Type*} [CommRing R] (a b : R) :
    Ri.normSq (algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R) =
    algebraMap R (Ri R) (a ^ 2 + b ^ 2) := by
  simp only [Ri.normSq]
  have hconj : (Ri.conj R) (algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R) =
      algebraMap R (Ri R) a - algebraMap R (Ri R) b * Ri.i R := by
    simp only [map_add, map_mul, AlgHom.commutes, Ri.conj_i, mul_neg]
    ring
  rw [hconj, map_add, map_pow, map_pow]
  have hi_sq : (Ri.i R) ^ 2 = -(1 : Ri R) := Ri.i_sq R
  ring_nf
  rw [hi_sq]
  ring

/-- normSq z lies in the image of R. -/
theorem Ri.normSq_mem_range {R : Type*} [CommRing R] [Nontrivial R] (z : Ri R) :
    Ri.normSq z ∈ Set.range (algebraMap R (Ri R)) := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists z
  rw [hab, Ri.normSq_repr]
  exact ⟨a ^ 2 + b ^ 2, rfl⟩

/-- The norm squared z · z̄, projected to R via algebraMap injectivity. -/
noncomputable def Ri.normSqR {R : Type*} [Field R] [IsRealClosed R] (z : Ri R) : R :=
  Classical.choose (Ri.normSq_mem_range z)

/-- algebraMap (normSqR z) = normSq z. -/
theorem Ri.normSqR_spec {R : Type*} [Field R] [IsRealClosed R] (z : Ri R) :
    algebraMap R (Ri R) (Ri.normSqR z) = Ri.normSq z :=
  Classical.choose_spec (Ri.normSq_mem_range z)

/-- normSqR z ≥ 0. -/
theorem Ri.normSqR_nonneg {R : Type*} [Field R] [IsRealClosed R] (z : Ri R) :
    @LE.le R IsRealClosed.toLinearOrder.toLE 0 (Ri.normSqR z) := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists z
  have hinj : Function.Injective (algebraMap R (Ri R)) := (algebraMap R (Ri R)).injective
  have heq : Ri.normSqR z = a ^ 2 + b ^ 2 := hinj (by
    rw [Ri.normSqR_spec, hab, Ri.normSq_repr])
  rw [heq]
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  exact add_nonneg (sq_nonneg a) (sq_nonneg b)

/-- **Modulus** |z| = √(a² + b²), the unique nonneg r ∈ R with r² = normSqR z. -/
noncomputable def Ri.modulus {R : Type*} [Field R] [IsRealClosed R]
    (z : Ri R) : R :=
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  |(IsRealClosed.exists_eq_pow_of_nonneg (Ri.normSqR_nonneg z) two_ne_zero).choose|

/-- The modulus is nonneg. -/
theorem Ri.modulus_nonneg {R : Type*} [Field R] [IsRealClosed R]
    (z : Ri R) : @LE.le R IsRealClosed.toLinearOrder.toLE 0 (Ri.modulus z) := by
  unfold Ri.modulus
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  exact abs_nonneg _

/-- The modulus squared equals the norm squared. -/
theorem Ri.modulus_sq {R : Type*} [Field R] [IsRealClosed R]
    (z : Ri R) : Ri.modulus z ^ 2 = Ri.normSqR z := by
  unfold Ri.modulus
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  rw [sq_abs]
  exact (IsRealClosed.exists_eq_pow_of_nonneg (Ri.normSqR_nonneg z) two_ne_zero).choose_spec.symm

end Azurite.BPR
