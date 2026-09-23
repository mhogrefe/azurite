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

/-- `FieldAtom` instance of `AtomRealization`: equality or inequality in the
    ambient field, mediated by `aeval`. -/
noncomputable instance {σ : Type*} {D : Type*} [CommRing D]
    {C : Type*} [Field C] [Algebra D C] :
    AtomRealization (FieldAtom σ D) σ C where
  interpret a := if a.isEq then { y | aeval y a.poly = 0}
                            else { y | aeval y a.poly ≠ 0}

namespace Formula

section Generic

variable {σ : Type*} {α : Type*} {C : Type*}

/-- The C-realization of a formula, generic over any atom type carrying an
    `AtomRealization` interpretation into `Set (σ → C)`.
    For field formulas (`α := FieldAtom σ D`) this is BPR's `Reali(Φ, Cᵏ)`. -/
noncomputable def realization [AtomRealization α σ C] [DecidableEq σ] :
    Formula σ α → Set (σ → C)
  | .atom a      => AtomRealization.interpret a
  | .not Φ       => (Φ.realization)ᶜ
  | .and Φ₁ Φ₂   => Φ₁.realization ∩ Φ₂.realization
  | .or Φ₁ Φ₂    => Φ₁.realization ∪ Φ₂.realization
  | .implies Φ₁ Φ₂ => (Φ₁.realization)ᶜ ∪ Φ₂.realization
  | .exists_ x Φ =>
    { y | ∃ c : C, Function.update y x c ∈ Φ.realization}
  | .forall_ x Φ =>
    { y | ∀ c : C, Function.update y x c ∈ Φ.realization}

@[simp] theorem realization_and [AtomRealization α σ C] [DecidableEq σ]
    (Φ₁ Φ₂ : Formula σ α) :
    (Formula.and Φ₁ Φ₂).realization (C := C) =
      Φ₁.realization ∩ Φ₂.realization := rfl

@[simp] theorem realization_or [AtomRealization α σ C] [DecidableEq σ]
    (Φ₁ Φ₂ : Formula σ α) :
    (Formula.or Φ₁ Φ₂).realization (C := C) =
      Φ₁.realization ∪ Φ₂.realization := rfl

@[simp] theorem realization_not [AtomRealization α σ C] [DecidableEq σ]
    (Φ : Formula σ α) :
    (Formula.not Φ).realization (C := C) = (Φ.realization)ᶜ := rfl

@[simp] theorem realization_atom [AtomRealization α σ C] [DecidableEq σ]
    (a : α) :
    (Formula.atom a).realization (C := C) = AtomRealization.interpret a := rfl

/-- A formula is *true* (valid) in `C` when its realization is all of `σ → C` — that is,
every assignment satisfies it. For a sentence (no free variables) this is exactly the
sentence's truth value in `C`. -/
def IsTrue [AtomRealization α σ C] [DecidableEq σ] (Φ : Formula σ α) : Prop :=
  Φ.realization (C := C) = Set.univ

theorem isTrue_iff_forall [AtomRealization α σ C] [DecidableEq σ] (Φ : Formula σ α) :
    Φ.IsTrue (C := C) ↔ ∀ y, y ∈ Φ.realization (C := C) := Set.eq_univ_iff_forall

end Generic

section FieldAtom

variable {σ : Type*} {D : Type*} [CommRing D]
variable {C : Type*} [Field C] [Algebra D C]

/-- Atom realization of a `FieldAtom`: `P = 0` or `P ≠ 0` according to `isEq`.
    This is the bridge that lets `simp only [realization]` (which exposes
    `AtomRealization.interpret a`) continue to make progress on field atoms. -/
@[simp] theorem interpret_fieldAtom [DecidableEq σ] (a : FieldAtom σ D) :
    (AtomRealization.interpret a : Set (σ → C)) =
      if a.isEq then { y | MvPolynomial.aeval y a.poly = 0 }
                 else { y | MvPolynomial.aeval y a.poly ≠ 0 } :=
  rfl

def CEquiv [DecidableEq σ]
    (Φ Ψ : Formula σ (FieldAtom σ D)) : Prop :=
  (realization (C := C) Φ) = (realization (C := C) Ψ)

@[simp] theorem realization_trueFormula [DecidableEq σ] :
    (trueFormula : Formula σ (FieldAtom σ D)).realization (C := C) =
      Set.univ := by
  ext y; simp [trueFormula, eq_zero, FieldAtom.eqZero, map_zero]

@[simp] theorem realization_falseFormula [DecidableEq σ] :
    (falseFormula : Formula σ (FieldAtom σ D)).realization (C := C) =
      ∅ := by
  ext y; simp [falseFormula, ne_zero, FieldAtom.neZero, map_zero]

set_option linter.unusedSimpArgs false in
@[simp] theorem realization_eq_zero [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (eq_zero P : Formula σ (FieldAtom σ D)).realization (C := C) =
      { y | MvPolynomial.aeval y P = 0} := by
  simp [eq_zero, FieldAtom.eqZero]

set_option linter.unusedSimpArgs false in
@[simp] theorem realization_ne_zero [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (ne_zero P : Formula σ (FieldAtom σ D)).realization (C := C) =
      { y | MvPolynomial.aeval y P ≠ 0} := by
  simp [ne_zero, FieldAtom.neZero]

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
      { y | ∀ Φ ∈ Φs, y ∈ Φ.realization (C := C) } := by
  induction Φs with
  | nil => simp [conjList]
  | cons Φ Φs ih =>
    simp only [conjList, realization_and, ih]
    ext y; simp [Set.mem_inter_iff, Set.mem_ofPred_eq,
      List.mem_cons, forall_eq_or_imp]

@[simp] theorem realization_disjList [DecidableEq σ]
    (Φs : List (Formula σ (FieldAtom σ D))) :
    (disjList Φs).realization (C := C) =
      { y | ∃ Φ ∈ Φs, y ∈ Φ.realization (C := C) } := by
  induction Φs with
  | nil => simp [disjList]
  | cons Φ Φs ih =>
    simp only [disjList, realization_or, ih]
    ext y; simp [Set.mem_union, Set.mem_ofPred_eq,
      List.mem_cons, exists_eq_or_imp]

end FieldAtom

end Formula

end Azurite.BPR
