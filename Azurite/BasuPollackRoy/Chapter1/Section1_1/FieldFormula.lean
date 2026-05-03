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

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]

/-- P = 0 as a formula. -/
noncomputable def eq_zero (P : MvPolynomial σ D) :
    Formula σ (FieldAtom σ D) :=
  .atom (FieldAtom.eqZero P)

/-- P ≠ 0 as a formula. -/
noncomputable def ne_zero (P : MvPolynomial σ D) :
    Formula σ (FieldAtom σ D) :=
  .atom (FieldAtom.neZero P)

/-- The free variables of a field formula. -/
noncomputable def freeVars [DecidableEq σ] :
    Formula σ (FieldAtom σ D) → Finset σ
  | .atom a      => a.vars
  | .not Φ       => Φ.freeVars
  | .and Φ₁ Φ₂   => Φ₁.freeVars ∪ Φ₂.freeVars
  | .or Φ₁ Φ₂    => Φ₁.freeVars ∪ Φ₂.freeVars
  | .implies Φ₁ Φ₂ => Φ₁.freeVars ∪ Φ₂.freeVars
  | .exists_ x Φ => Φ.freeVars \ {x}
  | .forall_ x Φ => Φ.freeVars \ {x}

/-- The bound variables of a field formula: variables attached to a quantifier (∃ or ∀). -/
noncomputable def boundVars [DecidableEq σ] :
    Formula σ (FieldAtom σ D) → Finset σ
  | .atom _        => ∅
  | .not Φ         => Φ.boundVars
  | .and Φ₁ Φ₂     => Φ₁.boundVars ∪ Φ₂.boundVars
  | .or Φ₁ Φ₂      => Φ₁.boundVars ∪ Φ₂.boundVars
  | .implies Φ₁ Φ₂ => Φ₁.boundVars ∪ Φ₂.boundVars
  | .exists_ x Φ   => Φ.boundVars ∪ {x}
  | .forall_ x Φ   => Φ.boundVars ∪ {x}

/-- A sentence is a formula with no free variables. -/
def isSentence [DecidableEq σ] (Φ : Formula σ (FieldAtom σ D)) :
    Prop :=
  Φ.freeVars = ∅

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
