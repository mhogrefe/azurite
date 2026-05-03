import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula

/-!
# Realization

The **C-realization** of a formula Φ with free variables in `{Y₁, …, Yₖ}`,
denoted `Reali(Φ, Cᵏ)`, is the set of `y ∈ Cᵏ` such that `Φ(y)` is true.

Here `D` is a subring of `C` (expressed via `[Algebra D C]`), and `aeval`
handles the coercion of coefficients from `D` to `C`.

This file defines `realization`, the equivalence relation `CEquiv`, simp lemmas
identifying the realization of the basic formula constructors, and the helper
constructions `conjList` and `disjList` for finite conjunctions and disjunctions.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]
variable {C : Type*} [Field C] [Algebra D C]

/-- The C-realization of a field formula: the set of assignments
    y : σ → C such that Φ(y) is true.
    BPR notation: Reali(Φ, Cᵏ). -/
noncomputable def realization [DecidableEq σ] :
    Formula σ (FieldAtom σ D) → Set (σ → C)
  | .atom a      => if a.isEq then { y | aeval y a.poly = 0}
                     else { y | aeval y a.poly ≠ 0}
  | .not Φ       => (Φ.realization)ᶜ
  | .and Φ₁ Φ₂   => Φ₁.realization ∩ Φ₂.realization
  | .or Φ₁ Φ₂    => Φ₁.realization ∪ Φ₂.realization
  | .implies Φ₁ Φ₂ => (Φ₁.realization)ᶜ ∪ Φ₂.realization
  | .exists_ x Φ =>
    { y | ∃ c : C, Function.update y x c ∈ Φ.realization}
  | .forall_ x Φ =>
    { y | ∀ c : C, Function.update y x c ∈ Φ.realization}

def CEquiv [DecidableEq σ]
    (Φ Ψ : Formula σ (FieldAtom σ D)) : Prop :=
  (realization (C := C) Φ) = (realization (C := C) Ψ)

@[simp] theorem realization_trueFormula [DecidableEq σ] :
    (trueFormula : Formula σ (FieldAtom σ D)).realization (C := C) =
      Set.univ := by
  ext y; simp [trueFormula, eq_zero, realization, FieldAtom.eqZero, map_zero]

@[simp] theorem realization_falseFormula [DecidableEq σ] :
    (falseFormula : Formula σ (FieldAtom σ D)).realization (C := C) =
      ∅ := by
  ext y; simp [falseFormula, ne_zero, realization, FieldAtom.neZero, map_zero]

@[simp] theorem realization_eq_zero [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (eq_zero P : Formula σ (FieldAtom σ D)).realization (C := C) =
      { y | MvPolynomial.aeval y P = 0} := by
  simp [eq_zero, realization, FieldAtom.eqZero]

@[simp] theorem realization_ne_zero [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (ne_zero P : Formula σ (FieldAtom σ D)).realization (C := C) =
      { y | MvPolynomial.aeval y P ≠ 0} := by
  simp [ne_zero, realization, FieldAtom.neZero]

@[simp] theorem realization_and [DecidableEq σ]
    (Φ₁ Φ₂ : Formula σ (FieldAtom σ D)) :
    (Formula.and Φ₁ Φ₂).realization (C := C) =
      Φ₁.realization ∩ Φ₂.realization := rfl

@[simp] theorem realization_or [DecidableEq σ]
    (Φ₁ Φ₂ : Formula σ (FieldAtom σ D)) :
    (Formula.or Φ₁ Φ₂).realization (C := C) =
      Φ₁.realization ∪ Φ₂.realization := rfl

/-- Conjunction of a list of formulas; empty list yields `trueFormula`. -/
noncomputable def conjList : List (Formula σ (FieldAtom σ D)) →
    Formula σ (FieldAtom σ D)
  | [] => trueFormula
  | Φ :: Φs => .and Φ (conjList Φs)

/-- Disjunction of a list of formulas; empty list yields `falseFormula`. -/
noncomputable def disjList : List (Formula σ (FieldAtom σ D)) →
    Formula σ (FieldAtom σ D)
  | [] => falseFormula
  | Φ :: Φs => .or Φ (disjList Φs)

@[simp] theorem realization_conjList [DecidableEq σ]
    (Φs : List (Formula σ (FieldAtom σ D))) :
    (conjList Φs).realization (C := C) =
      { y | ∀ Φ ∈ Φs, y ∈ Φ.realization } := by
  induction Φs with
  | nil => simp [conjList]
  | cons Φ Φs ih =>
    simp only [conjList, realization_and, ih]
    ext y; simp [Set.mem_inter_iff, Set.mem_setOf_eq,
      List.mem_cons, forall_eq_or_imp]

@[simp] theorem realization_disjList [DecidableEq σ]
    (Φs : List (Formula σ (FieldAtom σ D))) :
    (disjList Φs).realization (C := C) =
      { y | ∃ Φ ∈ Φs, y ∈ Φ.realization } := by
  induction Φs with
  | nil => simp [disjList]
  | cons Φ Φs ih =>
    simp only [disjList, realization_or, ih]
    ext y; simp [Set.mem_union, Set.mem_setOf_eq,
      List.mem_cons, exists_eq_or_imp]

end Formula

end Azurite.BPR
