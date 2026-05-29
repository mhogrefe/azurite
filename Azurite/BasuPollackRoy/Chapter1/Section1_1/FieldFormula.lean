import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula

/-!
# Atoms and Formulas for the Language of Fields

For algebraically closed fields, atoms are `P = 0` or `P ≠ 0`,
encoded as a polynomial together with a boolean flag.

This file introduces the `FieldAtom` structure together with field-specific
formula operations: the atomic formulas `eq_zero P` and `ne_zero P`, the free-
and bound-variable analyses, the sentence predicate, the constant `true`/`false`
formulas, and the `IsBasicFormula` predicate (a conjunction of atoms).
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

/-! ### Atom typeclasses

We expose two minimal typeclasses on atom types:

* `AtomVars α σ` provides the set of free variables of an atom.
* `AtomRealization α σ C` interprets an atom as a set of assignments `σ → C`.

These power generic `Formula.freeVars`, `Formula.boundVars`, `Formula.isSentence`,
and `Formula.realization` definitions that work for any atom type with the
appropriate instance — for example `FieldAtom σ D` (this file) and
`OrderedFieldAtom σ D` (Section 2.3). -/

/-- Typeclass for atom types that can report their free variables. -/
class AtomVars (α : Type*) (σ : outParam (Type*)) where
  /-- The variables appearing in an atom. -/
  vars : α → Finset σ

/-- Typeclass for atom types interpreted as sets of assignments `σ → C`. -/
class AtomRealization (α : Type*) (σ : outParam (Type*)) (C : Type*) where
  /-- The set of assignments at which the atom holds. -/
  interpret : α → Set (σ → C)

/-- An atom in the language of fields: a polynomial `P` together
    with `isEq = true` for `P = 0` or `isEq = false` for `P ≠ 0`. -/
structure FieldAtom (σ : Type*) (D : Type*) [CommRing D] where
  poly : MvPolynomial σ D
  isEq : Bool

namespace FieldAtom

variable {σ : Type*} {D : Type*} [CommRing D]

/-- The atom `P = 0`. -/
def eqZero (P : MvPolynomial σ D) : FieldAtom σ D := ⟨P, true⟩

/-- The atom `P ≠ 0`. -/
def neZero (P : MvPolynomial σ D) : FieldAtom σ D := ⟨P, false⟩

/-- Free variables of a field atom. -/
noncomputable def vars [DecidableEq σ] (a : FieldAtom σ D) : Finset σ :=
  a.poly.vars

/-- Rename variables in a field atom. -/
noncomputable def renameVars (f : σ → τ) (a : FieldAtom σ D) :
    FieldAtom τ D :=
  ⟨a.poly.rename f, a.isEq⟩

end FieldAtom

/-- `FieldAtom` instance of `AtomVars`: variables are those of the polynomial. -/
noncomputable instance {σ : Type*} [DecidableEq σ] {D : Type*} [CommRing D] :
    AtomVars (FieldAtom σ D) σ where
  vars := FieldAtom.vars

/-- Unfold `AtomVars.vars` on a `FieldAtom` to `FieldAtom.vars`.
    This lets `simp only [FieldAtom.vars]` continue to work after the
    generalization of `freeVars`. -/
@[simp] theorem AtomVars.vars_fieldAtom {σ : Type*} [DecidableEq σ]
    {D : Type*} [CommRing D] (a : FieldAtom σ D) :
    (AtomVars.vars a : Finset σ) = FieldAtom.vars a := rfl

namespace Formula

variable {σ : Type*} {α : Type*}

/-- The free variables of a formula, generic over any atom type with `AtomVars`. -/
noncomputable def freeVars [AtomVars α σ] [DecidableEq σ] :
    Formula σ α → Finset σ
  | .atom a      => AtomVars.vars a
  | .not Φ       => Φ.freeVars
  | .and Φ₁ Φ₂   => Φ₁.freeVars ∪ Φ₂.freeVars
  | .or Φ₁ Φ₂    => Φ₁.freeVars ∪ Φ₂.freeVars
  | .implies Φ₁ Φ₂ => Φ₁.freeVars ∪ Φ₂.freeVars
  | .exists_ x Φ => Φ.freeVars \ {x}
  | .forall_ x Φ => Φ.freeVars \ {x}

/-- The bound variables of a formula: variables attached to a quantifier (∃ or ∀). -/
noncomputable def boundVars [DecidableEq σ] :
    Formula σ α → Finset σ
  | .atom _        => ∅
  | .not Φ         => Φ.boundVars
  | .and Φ₁ Φ₂     => Φ₁.boundVars ∪ Φ₂.boundVars
  | .or Φ₁ Φ₂      => Φ₁.boundVars ∪ Φ₂.boundVars
  | .implies Φ₁ Φ₂ => Φ₁.boundVars ∪ Φ₂.boundVars
  | .exists_ x Φ   => Φ.boundVars ∪ {x}
  | .forall_ x Φ   => Φ.boundVars ∪ {x}

/-- A sentence is a formula with no free variables. -/
def isSentence [AtomVars α σ] [DecidableEq σ] (Φ : Formula σ α) :
    Prop :=
  Φ.freeVars = ∅

variable {D : Type*} [CommRing D]

/-- P = 0 as a formula. -/
noncomputable def eq_zero (P : MvPolynomial σ D) :
    Formula σ (FieldAtom σ D) :=
  .atom (FieldAtom.eqZero P)

/-- P ≠ 0 as a formula. -/
noncomputable def ne_zero (P : MvPolynomial σ D) :
    Formula σ (FieldAtom σ D) :=
  .atom (FieldAtom.neZero P)

/-- The formula "True": 0 = 0. -/
noncomputable def trueFormula : Formula σ (FieldAtom σ D) :=
  eq_zero 0

/-- The formula "False": 0 ≠ 0. -/
noncomputable def falseFormula : Formula σ (FieldAtom σ D) :=
  ne_zero 0

/-- A basic formula is a conjunction of atoms. -/
inductive IsBasicFormula : Formula σ (FieldAtom σ D) → Prop where
  | atom (a : FieldAtom σ D) :
      IsBasicFormula (.atom a)
  | and {Φ₁ Φ₂} :
      IsBasicFormula Φ₁ → IsBasicFormula Φ₂ →
      IsBasicFormula (.and Φ₁ Φ₂)

theorem IsBasicFormula.isQuantifierFree
    {Φ : Formula σ (FieldAtom σ D)} (h : IsBasicFormula Φ) :
    Φ.IsQuantifierFree := by
  induction h with
  | atom _ => trivial
  | and _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

end Formula

end Azurite.BPR
