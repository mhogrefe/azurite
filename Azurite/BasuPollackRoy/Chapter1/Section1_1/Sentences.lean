import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization

/-!
# Sentences

A sentence is a formula with no free variables. The realisation of a formula
depends only on its free variables (`realization_eq_of_agree_on_freeVars`),
so a sentence's realisation is either empty or all of `Cᵏ`
(`sentence_trivial_realization`); equivalently, every sentence is C-equivalent
to either `trueFormula` or `falseFormula` (`sentence_equiv_true_or_false`).
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]
variable {C : Type*} [Field C] [Algebra D C]

theorem realization_eq_of_agree_on_freeVars
    [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (y₁ y₂ : σ → C)
    (h : ∀ x ∈ Φ.freeVars, y₁ x = y₂ x) :
    y₁ ∈ Φ.realization (C := C) ↔
    y₂ ∈ Φ.realization := by
  induction Φ generalizing y₁ y₂ with
  | atom a =>
    simp only [realization, freeVars, AtomVars.vars_fieldAtom,
      FieldAtom.vars, interpret_fieldAtom] at *
    have : (MvPolynomial.aeval y₁) a.poly = (MvPolynomial.aeval y₂) a.poly := by
      simp only [MvPolynomial.aeval_def]
      apply MvPolynomial.eval₂_congr
      · intro i c hi hc
        apply h
        rw [MvPolynomial.mem_vars_iff_mem_support]
        exact ⟨c, MvPolynomial.mem_support_iff.mpr hc, hi⟩
    split <;> simp only [Set.mem_ofPred_eq] <;> rw [this]
  | not _ ih =>
    simp only [realization, Set.mem_compl_iff]
    rw [ih _ _ h]
  | and _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_inter_iff, freeVars] at *
    rw [ih₁ _ _ (fun x hx => h x (Finset.mem_union_left _ hx)),
        ih₂ _ _ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | or _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_union, freeVars] at *
    rw [ih₁ _ _ (fun x hx => h x (Finset.mem_union_left _ hx)),
        ih₂ _ _ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | exists_ z _ ih =>
    simp only [realization, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨c, hc⟩
    · exact ⟨c, (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mp hc⟩
    · exact ⟨c, (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mpr hc⟩
  | forall_ z _ ih =>
    simp only [realization, Set.mem_ofPred_eq]
    constructor <;> intro hc <;> intro c
    · exact (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mp (hc c)
    · exact (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mpr (hc c)
  | implies _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_union, Set.mem_compl_iff, freeVars] at *
    rw [ih₁ _ _ (fun x hx => h x (Finset.mem_union_left _ hx)),
        ih₂ _ _ (fun x hx => h x (Finset.mem_union_right _ hx))]

theorem sentence_trivial_realization [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (hΦ : isSentence Φ) :
    Φ.realization (C := C) = ∅ ∨
    Φ.realization (C := C) = Set.univ := by
  by_cases h : ∃ y, y ∈ Φ.realization (C := C)
  · right; ext y'
    obtain ⟨y, hy⟩ := h
    simp only [Set.mem_univ, iff_true]
    exact (realization_eq_of_agree_on_freeVars Φ y y'
      (by simp [isSentence] at hΦ; simp [hΦ])).mp hy
  · left; push Not at h
    exact Set.subset_eq_empty h rfl

theorem sentence_equiv_true_or_false [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (hΦ : isSentence Φ) :
    CEquiv (C := C) Φ trueFormula ∨
    CEquiv (C := C) Φ falseFormula := by
  rcases sentence_trivial_realization (C := C) Φ hΦ with h | h
  · right; show Φ.realization = _
    rw [h, realization_falseFormula]
  · left; show Φ.realization = _
    rw [h, realization_trueFormula]

end Formula

end Azurite.BPR
