/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.Realification
import Azurite.BasuPollackRoy.Chapter2.Section2_3.SemialgebraicSets
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-!
# BPR §4.7: semialgebraic subsets of `Cᵏ`

Using the realification `Cᵏ ≅ R^{2k}` (`realEquiv`), a subset of `Cᵏ = (Fin k → Ri R)` is
**semialgebraic over `C`** when its image in `R^{2k}` is a semialgebraic subset of `R^{2k}` in the
sense of §2.3. This transports all the boolean closure properties of semialgebraic sets, and lets us
express the basic complex conditions (e.g. "the `a`-th coordinate is nonzero") as semialgebraic.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

set_option linter.unusedSectionVars false in
/-- `R^n` is semialgebraic (it is the locus `1 > 0`). -/
theorem isSemialgebraicSet_univ {n : ℕ} :
    IsSemialgebraicSet (Set.univ : Set (Fin n → R)) := by
  have h : (Set.univ : Set (Fin n → R))
      = {x | MvPolynomial.eval x (1 : MvPolynomial (Fin n) R) > 0} := by
    ext x; simp [zero_lt_one]
  rw [h]; exact IsSemialgebraicSet.pos_locus 1

set_option linter.unusedSectionVars false in
/-- The empty set is semialgebraic. -/
theorem isSemialgebraicSet_empty {n : ℕ} :
    IsSemialgebraicSet (∅ : Set (Fin n → R)) := by
  rw [← Set.compl_univ]; exact isSemialgebraicSet_univ.compl

/-- **Semialgebraic subset of `Cᵏ`.** `S ⊆ Cᵏ` is semialgebraic when its realification
`realEquiv '' S ⊆ R^{2k}` is a semialgebraic subset of `R^{2k}`. -/
def IsSemialgebraicSetC (S : Set (Fin k → Ri R)) : Prop :=
  IsSemialgebraicSet (realEquiv '' S)

theorem IsSemialgebraicSetC.empty : IsSemialgebraicSetC (∅ : Set (Fin k → Ri R)) := by
  rw [IsSemialgebraicSetC, Set.image_empty]; exact isSemialgebraicSet_empty

theorem IsSemialgebraicSetC.univ : IsSemialgebraicSetC (Set.univ : Set (Fin k → Ri R)) := by
  rw [IsSemialgebraicSetC, Set.image_univ, realEquiv.surjective.range_eq]
  exact isSemialgebraicSet_univ

set_option linter.unusedSectionVars false in
theorem IsSemialgebraicSetC.union {S T : Set (Fin k → Ri R)}
    (hS : IsSemialgebraicSetC S) (hT : IsSemialgebraicSetC T) : IsSemialgebraicSetC (S ∪ T) := by
  rw [IsSemialgebraicSetC, Set.image_union]; exact IsSemialgebraicSet.union hS hT

set_option linter.unusedSectionVars false in
theorem IsSemialgebraicSetC.inter {S T : Set (Fin k → Ri R)}
    (hS : IsSemialgebraicSetC S) (hT : IsSemialgebraicSetC T) : IsSemialgebraicSetC (S ∩ T) := by
  rw [IsSemialgebraicSetC, Set.image_inter realEquiv.injective]
  exact IsSemialgebraicSet.inter hS hT

set_option linter.unusedSectionVars false in
theorem IsSemialgebraicSetC.compl {S : Set (Fin k → Ri R)}
    (hS : IsSemialgebraicSetC S) : IsSemialgebraicSetC Sᶜ := by
  rw [IsSemialgebraicSetC, Set.image_compl_eq realEquiv.bijective]
  exact IsSemialgebraicSet.compl hS

set_option linter.unusedSectionVars false in
/-- A finite intersection of semialgebraic-over-`C` sets is semialgebraic over `C`. -/
theorem IsSemialgebraicSetC.biInter_finset {ι : Type*} (s : Finset ι)
    {S : ι → Set (Fin k → Ri R)} (h : ∀ i ∈ s, IsSemialgebraicSetC (S i)) :
    IsSemialgebraicSetC (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
    exact IsSemialgebraicSetC.univ
  | @insert a s _ ih =>
    rw [Finset.set_biInter_insert]
    exact (h a (Finset.mem_insert_self a s)).inter
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The realification of a coordinate reindexing `σ : Fin a → Fin b`: it acts as `σ` separately on
the real block and the imaginary block of `R^{2·}`. -/
def doubleReindex {a b : ℕ} (σ : Fin a → Fin b) : Fin (a + a) → Fin (b + b) :=
  fun i => Fin.addCases (fun j => Fin.castAdd b (σ j)) (fun j => Fin.natAdd b (σ j)) i

set_option linter.unusedSectionVars false in
/-- Realification commutes with coordinate reindexing: `realEquiv (z ∘ σ) = realEquiv z ∘ σ̃`, where
`σ̃ = doubleReindex σ` reindexes the real and imaginary blocks by `σ`. -/
theorem realEquiv_comp_reindex {a b : ℕ} (σ : Fin a → Fin b) (z : Fin b → Ri R) :
    realEquiv (z ∘ σ) = realEquiv z ∘ doubleReindex σ := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [doubleReindex, Fin.addCases_left, Function.comp_apply, realEquiv_apply_castAdd]
  · simp only [doubleReindex, Fin.addCases_right, Function.comp_apply, realEquiv_apply_natAdd]

set_option linter.unusedSectionVars false in
/-- **Coordinate reindexing preserves semialgebraicity over `C`.** The complex analogue of
`IsSemialgebraicSet.comap`: pulling a semialgebraic-over-`C` set back along `σ : Fin a → Fin b`. -/
theorem IsSemialgebraicSetC.comap {a b : ℕ} (σ : Fin a → Fin b) {S : Set (Fin a → Ri R)}
    (hS : IsSemialgebraicSetC S) :
    IsSemialgebraicSetC {z : Fin b → Ri R | z ∘ σ ∈ S} := by
  rw [IsSemialgebraicSetC, Equiv.image_eq_preimage_symm]
  have hset : realEquiv.symm ⁻¹' {z : Fin b → Ri R | z ∘ σ ∈ S}
      = {w : Fin (b + b) → R | w ∘ doubleReindex σ ∈ realEquiv '' S} := by
    ext w
    have key : (realEquiv.symm w) ∘ σ = realEquiv.symm (w ∘ doubleReindex σ) := by
      apply realEquiv.injective
      rw [realEquiv_comp_reindex, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, key, Equiv.image_eq_preimage_symm]
  rw [hset]
  exact IsSemialgebraicSet.comap (doubleReindex σ) hS

set_option linter.unusedSectionVars false in
/-- A complex number `of c + (of d)·i` is zero iff both real and imaginary parts vanish. -/
theorem of_add_of_mul_i_eq_zero_iff (c d : R) :
    (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) c
      + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) d * Ri.i R = 0) ↔ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have hc := congrArg Ri.reL h
    have hd := congrArg Ri.imL h
    rw [Ri.reL_lin, map_zero] at hc
    rw [Ri.imL_lin, map_zero] at hd
    exact ⟨hc, hd⟩
  · rintro ⟨rfl, rfl⟩; simp

/-- The `a`-th complex coordinate of `realEquiv.symm w` vanishes iff its real and imaginary parts
(coordinates `castAdd a` and `natAdd a` of `w`) both vanish. -/
theorem realEquiv_symm_apply_eq_zero_iff (w : Fin (k + k) → R) (a : Fin k) :
    (realEquiv.symm w) a = 0 ↔ w (Fin.castAdd k a) = 0 ∧ w (Fin.natAdd k a) = 0 := by
  rw [realEquiv_symm_apply, of_add_of_mul_i_eq_zero_iff]

/-- **The locus where a complex coordinate is nonzero is semialgebraic over `C`.** This is the basic
open chart-overlap condition: `{z | z_a ≠ 0}` realifies to `{re ≠ 0 ∨ im ≠ 0}`, the complement of an
intersection of two coordinate-zero loci. -/
theorem isSemialgebraicSetC_coord_ne_zero (a : Fin k) :
    IsSemialgebraicSetC {z : Fin k → Ri R | z a ≠ 0} := by
  rw [IsSemialgebraicSetC, Equiv.image_eq_preimage_symm]
  have hset : (realEquiv.symm ⁻¹' {z : Fin k → Ri R | z a ≠ 0})
      = ({w : Fin (k + k) → R | eval w (X (Fin.castAdd k a)) = 0}
          ∩ {w | eval w (X (Fin.natAdd k a)) = 0})ᶜ := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_inter_iff, eval_X,
      ne_eq, realEquiv_symm_apply_eq_zero_iff, not_and]
  rw [hset]
  exact ((IsSemialgebraicSet.eqZero _).inter (IsSemialgebraicSet.eqZero _)).compl

end Azurite.BPR.Chapter4
