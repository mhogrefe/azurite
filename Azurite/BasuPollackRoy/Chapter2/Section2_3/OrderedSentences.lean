import Azurite.BasuPollackRoy.Chapter2.Section2_3.OrderedFieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula

/-! # Sentences in the language of ordered fields

The ordered-field analogue of `Chapter1/Section1_1/Sentences.lean`. A *sentence* is a
formula with no free variables (`isSentence`). Its realization does not depend on the
assignment, so over any ordered field `C` it is either empty or all of `Cᵏ`
(`sentence_trivial_realization_ordered`) — "false" or "true" respectively. This is what
makes the Tarski–Seidenberg transfer principle (Theorem 2.80) a statement about the
*truth value* of a sentence.

Only the atom case differs from the `FieldAtom` development; the logical connective and
quantifier cases are identical.
-/

open MvPolynomial

namespace Azurite.BPR
namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]
variable {C : Type*} [Field C] [LinearOrder C] [IsStrictOrderedRing C] [Algebra D C]

/-- The realization of an ordered-field formula depends only on the values of the
assignment on its free variables. -/
theorem realization_eq_of_agree_on_freeVars_ordered [DecidableEq σ]
    (Φ : Formula σ (OrderedFieldAtom σ D)) (y₁ y₂ : σ → C)
    (h : ∀ x ∈ Φ.freeVars, y₁ x = y₂ x) :
    y₁ ∈ Φ.realization (C := C) ↔ y₂ ∈ Φ.realization := by
  induction Φ generalizing y₁ y₂ with
  | atom a =>
    obtain ⟨poly, rel⟩ := a
    have hval : (MvPolynomial.aeval y₁) poly = (MvPolynomial.aeval y₂) poly := by
      simp only [MvPolynomial.aeval_def]
      apply MvPolynomial.eval₂_congr
      intro i c hi hc
      apply h
      simp only [freeVars, AtomVars.vars_orderedFieldAtom, OrderedFieldAtom.vars]
      rw [MvPolynomial.mem_vars_iff_mem_support]
      exact ⟨c, MvPolynomial.mem_support_iff.mpr hc, hi⟩
    cases rel <;> simp only [realization, AtomRealization.interpret, Set.mem_setOf_eq, hval]
  | not _ ih => simp only [realization, Set.mem_compl_iff]; rw [ih _ _ h]
  | and _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_inter_iff, freeVars] at *
    rw [ih₁ _ _ (fun x hx => h x (Finset.mem_union_left _ hx)),
        ih₂ _ _ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | or _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_union, freeVars] at *
    rw [ih₁ _ _ (fun x hx => h x (Finset.mem_union_left _ hx)),
        ih₂ _ _ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | exists_ z _ ih =>
    simp only [realization, Set.mem_setOf_eq]
    constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, ?_⟩
    · exact (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by
            simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mp hc
    · exact (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by
            simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mpr hc
  | forall_ z _ ih =>
    simp only [realization, Set.mem_setOf_eq]
    constructor <;> intro hc <;> intro c
    · exact (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by
            simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mp (hc c)
    · exact (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by
            simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mpr (hc c)
  | implies _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_union, Set.mem_compl_iff, freeVars] at *
    rw [ih₁ _ _ (fun x hx => h x (Finset.mem_union_left _ hx)),
        ih₂ _ _ (fun x hx => h x (Finset.mem_union_right _ hx))]

/-- A sentence in the language of ordered fields realizes to either `∅` (the sentence is
false in `C`) or all of `Cᵏ` (it is true), since its realization is independent of the
assignment. -/
theorem sentence_trivial_realization_ordered [DecidableEq σ]
    (Φ : Formula σ (OrderedFieldAtom σ D)) (hΦ : isSentence Φ) :
    Φ.realization (C := C) = ∅ ∨ Φ.realization (C := C) = Set.univ := by
  by_cases h : ∃ y, y ∈ Φ.realization (C := C)
  · right; ext y'
    obtain ⟨y, hy⟩ := h
    simp only [Set.mem_univ, iff_true]
    exact (realization_eq_of_agree_on_freeVars_ordered Φ y y'
      (by simp [isSentence] at hΦ; simp [hΦ])).mp hy
  · left; push Not at h; exact Set.subset_eq_empty h rfl

section BaseChange

variable {σ : Type*} [DecidableEq σ] {D D' : Type*} [CommRing D] [CommRing D'] [Algebra D D']

/-- Base-change of an ordered-field formula's coefficients along an algebra map `D → D'`,
mapping each atom's polynomial by `MvPolynomial.map (algebraMap D D')`. -/
noncomputable def mapCoeffO (Φ : Formula σ (OrderedFieldAtom σ D)) :
    Formula σ (OrderedFieldAtom σ D') :=
  Φ.mapAtom (fun a => ⟨a.poly.map (algebraMap D D'), a.rel⟩)

variable {S : Type*} [Field S] [LinearOrder S] [IsStrictOrderedRing S]
  [Algebra D' S] [Algebra D S] [IsScalarTower D D' S]

/-- Base change does not change the realization over a scalar tower `D → D' → S`: the
formula is interpreted by the same polynomial values. -/
theorem realization_mapCoeffO (Φ : Formula σ (OrderedFieldAtom σ D)) :
    (Φ.mapCoeffO (D' := D')).realization (C := S) = Φ.realization (C := S) := by
  induction Φ with
  | atom a =>
    obtain ⟨poly, rel⟩ := a
    show AtomRealization.interpret (⟨poly.map (algebraMap D D'), rel⟩ : OrderedFieldAtom σ D')
      = AtomRealization.interpret (⟨poly, rel⟩ : OrderedFieldAtom σ D)
    cases rel <;> simp only [AtomRealization.interpret, aeval_map_algebraMap D']
  | not _ ih => simp only [mapCoeffO, Formula.mapAtom, Formula.realization] at *; rw [ih]
  | and _ _ ih₁ ih₂ =>
    simp only [mapCoeffO, Formula.mapAtom, Formula.realization] at *; rw [ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp only [mapCoeffO, Formula.mapAtom, Formula.realization] at *; rw [ih₁, ih₂]
  | implies _ _ ih₁ ih₂ =>
    simp only [mapCoeffO, Formula.mapAtom, Formula.realization] at *; rw [ih₁, ih₂]
  | exists_ x _ ih =>
    simp only [mapCoeffO, Formula.mapAtom, Formula.realization] at *; rw [ih]
  | forall_ x _ ih =>
    simp only [mapCoeffO, Formula.mapAtom, Formula.realization] at *; rw [ih]

theorem freeVars_mapCoeffO_subset (Φ : Formula σ (OrderedFieldAtom σ D)) :
    (Φ.mapCoeffO (D' := D')).freeVars ⊆ Φ.freeVars := by
  induction Φ with
  | atom a =>
    obtain ⟨poly, rel⟩ := a
    simp only [mapCoeffO, Formula.mapAtom, freeVars, AtomVars.vars_orderedFieldAtom,
      OrderedFieldAtom.vars]
    exact MvPolynomial.vars_map poly (algebraMap D D')
  | not _ ih => simpa only [mapCoeffO, Formula.mapAtom, freeVars] using ih
  | and _ _ ih₁ ih₂ =>
    simp only [mapCoeffO, Formula.mapAtom, freeVars]; exact Finset.union_subset_union ih₁ ih₂
  | or _ _ ih₁ ih₂ =>
    simp only [mapCoeffO, Formula.mapAtom, freeVars]; exact Finset.union_subset_union ih₁ ih₂
  | implies _ _ ih₁ ih₂ =>
    simp only [mapCoeffO, Formula.mapAtom, freeVars]; exact Finset.union_subset_union ih₁ ih₂
  | exists_ x _ ih =>
    simp only [mapCoeffO, Formula.mapAtom, freeVars]; exact Finset.sdiff_subset_sdiff ih subset_rfl
  | forall_ x _ ih =>
    simp only [mapCoeffO, Formula.mapAtom, freeVars]; exact Finset.sdiff_subset_sdiff ih subset_rfl

/-- Base change preserves the sentence property (base change can only shrink the free
variables). -/
theorem isSentence_mapCoeffO {Φ : Formula σ (OrderedFieldAtom σ D)} (hΦ : isSentence Φ) :
    isSentence (Φ.mapCoeffO (D' := D')) := by
  rw [isSentence] at hΦ ⊢
  exact Finset.subset_empty.mp (hΦ ▸ freeVars_mapCoeffO_subset Φ)

end BaseChange

/-- For a sentence, truth in `C` (`IsTrue`) is the same as having a nonempty realization,
since a sentence's realization is `∅` (false) or all of `Cᵏ` (true). -/
theorem isTrue_iff_nonempty_of_isSentence [DecidableEq σ]
    (Φ : Formula σ (OrderedFieldAtom σ D)) (hΦ : isSentence Φ) :
    Φ.IsTrue (C := C) ↔ (Φ.realization (C := C)).Nonempty := by
  haveI : Nonempty (σ → C) := ⟨fun _ => 0⟩
  rcases sentence_trivial_realization_ordered (C := C) Φ hΦ with h | h <;>
    rw [Formula.IsTrue, h] <;> simp [Set.empty_ne_univ]

end Formula
end Azurite.BPR
