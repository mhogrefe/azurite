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

/-! ### AtomRename typeclass -/

/-- Typeclass for atom types that support variable renaming via an equivalence
    (permutation). Used by the prenex conversion to rename bound variables. -/
class AtomRename (α : Type*) (σ : outParam Type*) where
  /-- Rename variables in an atom using a variable permutation. -/
  renameEquiv : (σ ≃ σ) → α → α

/-- `AzFieldAtom` instance: computable via `renameVarsInjective`. -/
instance {n : ℕ} {σ : Type*} [LinearOrder σ] [Var σ n]
    {R : Type*} [Semiring R] {ord : MonomialOrder} :
    AtomRename (AzFieldAtom σ R ord) σ where
  renameEquiv e a := a.renameVarsInjective e e.injective

/-- `FieldAtom` instance: noncomputable (uses `MvPolynomial.rename`). -/
noncomputable instance {σ : Type*} [DecidableEq σ]
    {D : Type*} [CommRing D] :
    AtomRename (FieldAtom σ D) σ where
  renameEquiv e a := FieldAtom.renameVars e a

/-! ### AtomNeg typeclass -/

/-- Typeclass for atom types that support negation at the atom level.
    For field atoms, negation flips `= 0` to `≠ 0` and vice versa.
    This enables `toNNF` to absorb negation into atoms rather than
    wrapping them in `Formula.not`. -/
class AtomNeg (α : Type*) where
  /-- Negate an atom. Must satisfy `interpret (neg a) = (interpret a)ᶜ`
      when combined with `AtomRealization`. -/
  neg : α → α

/-- `AzFieldAtom` instance: flips the `isEq` flag. -/
instance {n : ℕ} {σ : Type*} [LinearOrder σ] [Var σ n]
    {R : Type*} [Semiring R] {ord : MonomialOrder} :
    AtomNeg (AzFieldAtom σ R ord) where
  neg a := ⟨a.poly, !a.isEq⟩

/-- `FieldAtom` instance: flips the `isEq` flag. -/
instance {σ : Type*} {D : Type*} [CommRing D] :
    AtomNeg (FieldAtom σ D) where
  neg a := ⟨a.poly, !a.isEq⟩

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

/-- All variables mentioned in a formula, including bound variables. -/
def allVarsOf [AtomVars α σ] [DecidableEq σ] :
    Formula σ α → Finset σ
  | .atom a        => AtomVars.vars a
  | .not Φ         => allVarsOf Φ
  | .and Φ₁ Φ₂     => allVarsOf Φ₁ ∪ allVarsOf Φ₂
  | .or Φ₁ Φ₂      => allVarsOf Φ₁ ∪ allVarsOf Φ₂
  | .implies Φ₁ Φ₂ => allVarsOf Φ₁ ∪ allVarsOf Φ₂
  | .exists_ x Φ   => allVarsOf Φ ∪ {x}
  | .forall_ x Φ   => allVarsOf Φ ∪ {x}

theorem freeVarsOf_subset_allVarsOf [AtomVars α σ] [DecidableEq σ]
    (Φ : Formula σ α) : freeVarsOf Φ ⊆ allVarsOf Φ := by
  induction Φ with
  | atom a => exact Finset.Subset.refl _
  | not Φ ih => exact ih
  | and Φ₁ Φ₂ ih₁ ih₂ => exact Finset.union_subset_union ih₁ ih₂
  | or Φ₁ Φ₂ ih₁ ih₂ => exact Finset.union_subset_union ih₁ ih₂
  | implies Φ₁ Φ₂ ih₁ ih₂ => exact Finset.union_subset_union ih₁ ih₂
  | exists_ x Φ ih =>
    intro v hv; simp only [freeVarsOf, allVarsOf, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton] at hv ⊢; exact .inl (ih hv.1)
  | forall_ x Φ ih =>
    intro v hv; simp only [freeVarsOf, allVarsOf, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton] at hv ⊢; exact .inl (ih hv.1)

/-- Bound variables of a formula: variables attached to a quantifier (∃ or ∀).
    Generic over any atom type. -/
def boundVarsOf [AtomVars α σ] [DecidableEq σ] :
    Formula σ α → Finset σ
  | .atom _        => ∅
  | .not Φ         => boundVarsOf Φ
  | .and Φ₁ Φ₂     => boundVarsOf Φ₁ ∪ boundVarsOf Φ₂
  | .or Φ₁ Φ₂      => boundVarsOf Φ₁ ∪ boundVarsOf Φ₂
  | .implies Φ₁ Φ₂ => boundVarsOf Φ₁ ∪ boundVarsOf Φ₂
  | .exists_ x Φ   => boundVarsOf Φ ∪ {x}
  | .forall_ x Φ   => boundVarsOf Φ ∪ {x}

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

/-! ### Negation normal form -/

/-- Convert a formula to negation normal form (positive position).
    Pushes negations into atoms using `AtomNeg`. Handles `implies` inline. -/
def toNNFPos [AtomNeg α] : Formula σ α → Formula σ α
  | .atom a => .atom a
  | .not Φ => toNNFNeg Φ
  | .and Φ₁ Φ₂ => .and (toNNFPos Φ₁) (toNNFPos Φ₂)
  | .or Φ₁ Φ₂ => .or (toNNFPos Φ₁) (toNNFPos Φ₂)
  | .implies Φ₁ Φ₂ => .or (toNNFNeg Φ₁) (toNNFPos Φ₂)
  | .exists_ x Φ => .exists_ x (toNNFPos Φ)
  | .forall_ x Φ => .forall_ x (toNNFPos Φ)
where
  /-- Convert a formula to NNF in negative position (under a negation).
      Absorbs negation into atoms via `AtomNeg.neg`. -/
  toNNFNeg : Formula σ α → Formula σ α
    | .atom a => .atom (AtomNeg.neg a)
    | .not Φ => toNNFPos Φ
    | .and Φ₁ Φ₂ => .or (toNNFNeg Φ₁) (toNNFNeg Φ₂)
    | .or Φ₁ Φ₂ => .and (toNNFNeg Φ₁) (toNNFNeg Φ₂)
    | .implies Φ₁ Φ₂ => .and (toNNFPos Φ₁) (toNNFNeg Φ₂)
    | .exists_ x Φ => .forall_ x (toNNFNeg Φ)
    | .forall_ x Φ => .exists_ x (toNNFNeg Φ)

/-- Convert a formula to negation normal form.
    Pushes all negations into atoms and eliminates `implies`. -/
def toNNF [AtomNeg α] : Formula σ α → Formula σ α := toNNFPos

/-! ### Formula renaming via AtomRename -/

/-- Rename all variables in a formula (both structural and inside atoms)
    using an equivalence (permutation). -/
def renameFormulaEquiv [AtomRename α σ] (e : σ ≃ σ) (Φ : Formula σ α) : Formula σ α :=
  Φ.rename e (AtomRename.renameEquiv e)

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
