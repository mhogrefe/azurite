/-
  Computable operations on Formula with atoms that provide variable information.

  Defines the `AtomVars` typeclass, generic `freeVarsOf`, modular simplification
  passes, and AzFieldAtom-specific constructors.
-/
import Azurite.AzFormula.Atom
import Azurite.BasuPollackRoy.Chapter1.Section1_1

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR

/-! ### AtomVars typeclass -/

/-- Typeclass for atom types that can report their free variables.
    This enables generic `freeVarsOf` and simplifications on any `Formula σ α`. -/
class AtomVars (α : Type*) (σ : outParam Type*) where
  /-- The variables appearing in an atom. -/
  vars : α → Finset σ

/-- `AzFieldAtom` instance: computable via `AzMvPolynomial.vars`. -/
instance {n : ℕ} {σ : Type*} [LinearOrder σ] [Var σ n]
    {R : Type*} [Semiring R] {ord : MonomialOrder} :
    AtomVars (AzFieldAtom σ R ord) σ where
  vars := AzFieldAtom.vars

/-- `FieldAtom` instance: noncomputable (uses `MvPolynomial.vars`). -/
noncomputable instance {σ : Type*} [DecidableEq σ]
    {D : Type*} [CommRing D] :
    AtomVars (FieldAtom σ D) σ where
  vars := FieldAtom.vars

/-! ### Generic free variables -/

variable {σ : Type*} {α : Type*}

/-- Free variables of a formula, generic over any atom type with `AtomVars`. -/
def freeVarsOf [AtomVars α σ] [DecidableEq σ] :
    Formula σ α → Finset σ
  | .atom a        => AtomVars.vars a
  | .not Φ         => freeVarsOf Φ
  | .and Φ₁ Φ₂     => freeVarsOf Φ₁ ∪ freeVarsOf Φ₂
  | .or Φ₁ Φ₂      => freeVarsOf Φ₁ ∪ freeVarsOf Φ₂
  | .implies Φ₁ Φ₂ => freeVarsOf Φ₁ ∪ freeVarsOf Φ₂
  | .exists_ x Φ   => freeVarsOf Φ \ {x}
  | .forall_ x Φ   => freeVarsOf Φ \ {x}

/-- A formula is a sentence if it has no free variables. -/
def isSentenceOf [AtomVars α σ] [DecidableEq σ]
    (Φ : Formula σ α) : Bool :=
  freeVarsOf Φ = ∅

/-! ### Modular simplification passes -/

/-- Eliminate double negations bottom-up: `¬¬Φ → Φ`.
    Does not require `AtomVars`. -/
def elimDoubleNeg : Formula σ α → Formula σ α
  | .atom a => .atom a
  | .not Φ =>
    match elimDoubleNeg Φ with
    | .not Ψ => Ψ
    | Φ'     => .not Φ'
  | .and Φ₁ Φ₂     => .and (elimDoubleNeg Φ₁) (elimDoubleNeg Φ₂)
  | .or Φ₁ Φ₂      => .or (elimDoubleNeg Φ₁) (elimDoubleNeg Φ₂)
  | .implies Φ₁ Φ₂ => .implies (elimDoubleNeg Φ₁) (elimDoubleNeg Φ₂)
  | .exists_ x Φ   => .exists_ x (elimDoubleNeg Φ)
  | .forall_ x Φ   => .forall_ x (elimDoubleNeg Φ)

/-- Remove vacuous quantifiers bottom-up: `∃x, Φ → Φ` and `∀x, Φ → Φ`
    when `x ∉ freeVars Φ`. -/
def elimVacuousQuantifiers [AtomVars α σ] [DecidableEq σ] :
    Formula σ α → Formula σ α
  | .atom a => .atom a
  | .not Φ  => .not (elimVacuousQuantifiers Φ)
  | .and Φ₁ Φ₂     => .and (elimVacuousQuantifiers Φ₁) (elimVacuousQuantifiers Φ₂)
  | .or Φ₁ Φ₂      => .or (elimVacuousQuantifiers Φ₁) (elimVacuousQuantifiers Φ₂)
  | .implies Φ₁ Φ₂ => .implies (elimVacuousQuantifiers Φ₁) (elimVacuousQuantifiers Φ₂)
  | .exists_ x Φ =>
    let Φ' := elimVacuousQuantifiers Φ
    if x ∈ freeVarsOf Φ' then .exists_ x Φ' else Φ'
  | .forall_ x Φ =>
    let Φ' := elimVacuousQuantifiers Φ
    if x ∈ freeVarsOf Φ' then .forall_ x Φ' else Φ'

/-- Apply all simplifications: double negation elimination followed by
    vacuous quantifier removal. -/
def simplify [AtomVars α σ] [DecidableEq σ] (Φ : Formula σ α) : Formula σ α :=
  elimVacuousQuantifiers (elimDoubleNeg Φ)

/-! ### AzFieldAtom-specific constructors -/

variable {n : ℕ} [LinearOrder σ] [Var σ n]
    {R : Type*} [Semiring R] {ord : MonomialOrder}

/-- P = 0 as a formula. -/
def azEqZero (P : AzMvPolynomial σ R ord) :
    Formula σ (AzFieldAtom σ R ord) :=
  .atom (AzFieldAtom.eqZero P)

/-- P ≠ 0 as a formula. -/
def azNeZero (P : AzMvPolynomial σ R ord) :
    Formula σ (AzFieldAtom σ R ord) :=
  .atom (AzFieldAtom.neZero P)

/-- The true formula: 0 = 0. -/
def azTrueFormula : Formula σ (AzFieldAtom σ R ord) :=
  azEqZero 0

/-- The false formula: 0 ≠ 0. -/
def azFalseFormula : Formula σ (AzFieldAtom σ R ord) :=
  azNeZero 0

/-! ### Conjunction of equalities -/

/-- Conjunction of `P = 0` atoms from a list of polynomials. -/
def azConjEqZero :
    List (AzMvPolynomial σ R ord) → Formula σ (AzFieldAtom σ R ord)
  | []     => azTrueFormula
  | [P]    => azEqZero P
  | P :: rest => .and (azEqZero P) (azConjEqZero rest)

end Azurite
