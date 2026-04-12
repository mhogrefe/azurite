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
instance {n : ℕ} {R : Type*} [Semiring R] {ord : MonomialOrder} :
    AtomVars (AzFieldAtom n R ord) (Fin n) where
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
instance {n : ℕ} {R : Type*} [Semiring R] {ord : MonomialOrder} :
    AtomRename (AzFieldAtom n R ord) (Fin n) where
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
instance {n : ℕ} {R : Type*} [Semiring R] {ord : MonomialOrder} :
    AtomNeg (AzFieldAtom n R ord) where
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

variable {n : ℕ} {R : Type*} [Semiring R] {ord : MonomialOrder}

/-- P = 0 as a formula. -/
def azEqZero (P : AzMvPolynomial n R ord) :
    Formula (Fin n) (AzFieldAtom n R ord) :=
  .atom (AzFieldAtom.eqZero P)

/-- P ≠ 0 as a formula. -/
def azNeZero (P : AzMvPolynomial n R ord) :
    Formula (Fin n) (AzFieldAtom n R ord) :=
  .atom (AzFieldAtom.neZero P)

/-- The true formula: 0 = 0. -/
def azTrueFormula : Formula (Fin n) (AzFieldAtom n R ord) :=
  azEqZero 0

/-- The false formula: 0 ≠ 0. -/
def azFalseFormula : Formula (Fin n) (AzFieldAtom n R ord) :=
  azNeZero 0

/-! ### Trivial atom elimination -/

/-- Check whether a formula is a trivially true atom (`P = 0` with `P = 0`). -/
def isAzTrue [DecidableEq R] (Φ : Formula (Fin n) (AzFieldAtom n R ord)) : Bool :=
  match Φ with
  | .atom a => a.isEq && a.poly == 0
  | _ => false

/-- Check whether a formula is a trivially false atom (`P ≠ 0` with `P = 0`). -/
def isAzFalse [DecidableEq R] (Φ : Formula (Fin n) (AzFieldAtom n R ord)) : Bool :=
  match Φ with
  | .atom a => !a.isEq && a.poly == 0
  | _ => false

/-- Smart conjunction: absorbs trivially true/false atoms.
    Semantically equivalent to `.and Φ₁ Φ₂`, but simplifies when either
    argument is trivially true or false. -/
def azSmartAnd [DecidableEq R]
    (Φ₁ Φ₂ : Formula (Fin n) (AzFieldAtom n R ord)) :
    Formula (Fin n) (AzFieldAtom n R ord) :=
  if isAzTrue Φ₁ then Φ₂
  else if isAzTrue Φ₂ then Φ₁
  else if isAzFalse Φ₁ || isAzFalse Φ₂ then azFalseFormula
  else .and Φ₁ Φ₂

/-- Smart disjunction: absorbs trivially true/false atoms.
    Semantically equivalent to `.or Φ₁ Φ₂`, but simplifies when either
    argument is trivially true or false. -/
def azSmartOr [DecidableEq R]
    (Φ₁ Φ₂ : Formula (Fin n) (AzFieldAtom n R ord)) :
    Formula (Fin n) (AzFieldAtom n R ord) :=
  if isAzFalse Φ₁ then Φ₂
  else if isAzFalse Φ₂ then Φ₁
  else if isAzTrue Φ₁ || isAzTrue Φ₂ then azTrueFormula
  else .or Φ₁ Φ₂

/-- Eliminate trivially true (`0 = 0`) and trivially false (`0 ≠ 0`) atoms
    using boolean absorption rules. -/
def elimTrivialAtoms [DecidableEq R] :
    Formula (Fin n) (AzFieldAtom n R ord) → Formula (Fin n) (AzFieldAtom n R ord)
  | .atom a => .atom a
  | .not Φ =>
    let Φ' := elimTrivialAtoms Φ
    if isAzTrue Φ' then azFalseFormula
    else if isAzFalse Φ' then azTrueFormula
    else .not Φ'
  | .and Φ₁ Φ₂ =>
    let Φ₁' := elimTrivialAtoms Φ₁
    let Φ₂' := elimTrivialAtoms Φ₂
    if isAzTrue Φ₁' then Φ₂'
    else if isAzTrue Φ₂' then Φ₁'
    else if isAzFalse Φ₁' || isAzFalse Φ₂' then azFalseFormula
    else .and Φ₁' Φ₂'
  | .or Φ₁ Φ₂ =>
    let Φ₁' := elimTrivialAtoms Φ₁
    let Φ₂' := elimTrivialAtoms Φ₂
    if isAzFalse Φ₁' then Φ₂'
    else if isAzFalse Φ₂' then Φ₁'
    else if isAzTrue Φ₁' || isAzTrue Φ₂' then azTrueFormula
    else .or Φ₁' Φ₂'
  | .implies Φ₁ Φ₂ =>
    let Φ₁' := elimTrivialAtoms Φ₁
    let Φ₂' := elimTrivialAtoms Φ₂
    if isAzTrue Φ₁' then Φ₂'
    else if isAzFalse Φ₁' || isAzTrue Φ₂' then azTrueFormula
    else .implies Φ₁' Φ₂'
  | .exists_ x Φ => .exists_ x (elimTrivialAtoms Φ)
  | .forall_ x Φ => .forall_ x (elimTrivialAtoms Φ)

/-! ### Combined AzFieldAtom simplification -/

/-- Helper for the `.not` case of `azSimplify`: eliminates double negation
    and absorbs trivially true/false children. -/
def azSimplifyNot [DecidableEq R]
    (Φ' : Formula (Fin n) (AzFieldAtom n R ord)) :
    Formula (Fin n) (AzFieldAtom n R ord) :=
  match Φ' with
  | .not Ψ => Ψ
  | _ =>
    if isAzTrue Φ' then azFalseFormula
    else if isAzFalse Φ' then azTrueFormula
    else .not Φ'

/-- Apply all AzFieldAtom-specific simplifications in a single recursive pass:
    double negation elimination, trivial atom absorption, and vacuous
    quantifier removal. A single pass avoids interactions where one
    transformation undoes another (e.g. `elimTrivialAtoms` can create
    double negations). -/
def azSimplify [DecidableEq R] :
    Formula (Fin n) (AzFieldAtom n R ord) → Formula (Fin n) (AzFieldAtom n R ord)
  | .atom a => .atom a
  | .not Φ => azSimplifyNot (azSimplify Φ)
  | .and Φ₁ Φ₂ =>
    let Φ₁' := azSimplify Φ₁
    let Φ₂' := azSimplify Φ₂
    if isAzTrue Φ₁' then Φ₂'
    else if isAzTrue Φ₂' then Φ₁'
    else if isAzFalse Φ₁' || isAzFalse Φ₂' then azFalseFormula
    else .and Φ₁' Φ₂'
  | .or Φ₁ Φ₂ =>
    let Φ₁' := azSimplify Φ₁
    let Φ₂' := azSimplify Φ₂
    if isAzFalse Φ₁' then Φ₂'
    else if isAzFalse Φ₂' then Φ₁'
    else if isAzTrue Φ₁' || isAzTrue Φ₂' then azTrueFormula
    else .or Φ₁' Φ₂'
  | .implies Φ₁ Φ₂ =>
    let Φ₁' := azSimplify Φ₁
    let Φ₂' := azSimplify Φ₂
    if isAzTrue Φ₁' then Φ₂'
    else if isAzFalse Φ₁' || isAzTrue Φ₂' then azTrueFormula
    else .implies Φ₁' Φ₂'
  | .exists_ x Φ =>
    let Φ' := azSimplify Φ
    if x ∈ freeVarsOf Φ' then .exists_ x Φ' else Φ'
  | .forall_ x Φ =>
    let Φ' := azSimplify Φ
    if x ∈ freeVarsOf Φ' then .forall_ x Φ' else Φ'

/-- Check whether a formula is fully simplified: no double negations, no trivial
    atoms under connectives, and no vacuous quantifiers. -/
def isAzSimplified [DecidableEq R] :
    Formula (Fin n) (AzFieldAtom n R ord) → Bool
  | .atom _ => true
  | .not (.not _) => false
  | .not Φ => !isAzTrue Φ && !isAzFalse Φ && isAzSimplified Φ
  | .and Φ₁ Φ₂ =>
    !isAzTrue Φ₁ && !isAzTrue Φ₂ && !isAzFalse Φ₁ && !isAzFalse Φ₂
      && isAzSimplified Φ₁ && isAzSimplified Φ₂
  | .or Φ₁ Φ₂ =>
    !isAzFalse Φ₁ && !isAzFalse Φ₂ && !isAzTrue Φ₁ && !isAzTrue Φ₂
      && isAzSimplified Φ₁ && isAzSimplified Φ₂
  | .implies Φ₁ Φ₂ =>
    !isAzTrue Φ₁ && !isAzFalse Φ₁ && !isAzTrue Φ₂
      && isAzSimplified Φ₁ && isAzSimplified Φ₂
  | .exists_ x Φ => decide (x ∈ freeVarsOf Φ) && isAzSimplified Φ
  | .forall_ x Φ => decide (x ∈ freeVarsOf Φ) && isAzSimplified Φ

/-! ### Conjunction of equalities -/

/-- Conjunction of `P = 0` atoms from a list of polynomials. -/
def azConjEqZero :
    List (AzMvPolynomial n R ord) → Formula (Fin n) (AzFieldAtom n R ord)
  | []     => azTrueFormula
  | [P]    => azEqZero P
  | P :: rest => .and (azEqZero P) (azConjEqZero rest)

end Azurite
