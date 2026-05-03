import Azurite.BasuPollackRoy.Chapter1.Section1_1.Definitions

/-!
# First-Order Formulas (Generic)

We define first-order formulas generically over an **atom type** `α`.
The connectives are `not`, `and`, `or`, `implies`, and the quantifiers `exists_` and `forall_`.
The functions `eliminateForall` and `eliminateImplies` convert these to the minimal basis.

For algebraically closed fields (Chapter 1), atoms are `FieldAtom σ D`,
encoding `P = 0` or `P ≠ 0` via a boolean flag.
For real closed fields (Chapter 2), atoms will encode sign conditions.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

/-- First-order formulas over atom type `α`, with variables
    indexed by type `σ`. -/
inductive Formula (σ : Type*) (α : Type*) where
  | atom    : α → Formula σ α
  | not     : Formula σ α → Formula σ α
  | and     : Formula σ α → Formula σ α → Formula σ α
  | or      : Formula σ α → Formula σ α → Formula σ α
  | implies : Formula σ α → Formula σ α → Formula σ α
  | exists_ : σ → Formula σ α → Formula σ α
  | forall_ : σ → Formula σ α → Formula σ α

namespace Formula

variable {σ : Type*} {α : Type*}

/-- Map atoms in a formula via `f : α → β`, preserving all logical structure. -/
def mapAtom (f : α → β) : Formula σ α → Formula σ β
  | .atom a      => .atom (f a)
  | .not Φ       => .not (Φ.mapAtom f)
  | .and Φ₁ Φ₂   => .and (Φ₁.mapAtom f) (Φ₂.mapAtom f)
  | .or Φ₁ Φ₂    => .or (Φ₁.mapAtom f) (Φ₂.mapAtom f)
  | .implies Φ₁ Φ₂ => .implies (Φ₁.mapAtom f) (Φ₂.mapAtom f)
  | .exists_ x Φ => .exists_ x (Φ.mapAtom f)
  | .forall_ x Φ => .forall_ x (Φ.mapAtom f)

/-- A formula is quantifier-free if no quantifier (∃ or ∀)
    appears in it. -/
def IsQuantifierFree : Formula σ α → Prop
  | .atom _        => True
  | .not Φ         => Φ.IsQuantifierFree
  | .and Φ₁ Φ₂     => Φ₁.IsQuantifierFree ∧ Φ₂.IsQuantifierFree
  | .or Φ₁ Φ₂      => Φ₁.IsQuantifierFree ∧ Φ₂.IsQuantifierFree
  | .implies Φ₁ Φ₂ => Φ₁.IsQuantifierFree ∧ Φ₂.IsQuantifierFree
  | .exists_ _ _   => False
  | .forall_ _ _   => False

/-- Quantifier depth of a formula. -/
def quantifierDepth : Formula σ α → ℕ
  | .atom _        => 0
  | .not Φ         => Φ.quantifierDepth
  | .and Φ₁ Φ₂     => Φ₁.quantifierDepth + Φ₂.quantifierDepth
  | .or Φ₁ Φ₂      => Φ₁.quantifierDepth + Φ₂.quantifierDepth
  | .implies Φ₁ Φ₂ => Φ₁.quantifierDepth + Φ₂.quantifierDepth
  | .exists_ _ Φ   => Φ.quantifierDepth + 1
  | .forall_ _ Φ   => Φ.quantifierDepth + 1

/-- A formula in prenex normal form. -/
inductive IsPrenex : Formula σ α → Prop where
  | qf {Φ} : Φ.IsQuantifierFree → IsPrenex Φ
  | exists_ {x : σ} {Φ} :
      IsPrenex Φ → IsPrenex (.exists_ x Φ)
  | forall_ {x : σ} {Φ} :
      IsPrenex Φ → IsPrenex (.forall_ x Φ)

/-- Rename variables in a formula via `f : σ → τ`. -/
def rename (f : σ → τ) (renameAtom : α → β) :
    Formula σ α → Formula τ β
  | .atom a      => .atom (renameAtom a)
  | .not Φ       => .not (Φ.rename f renameAtom)
  | .and Φ₁ Φ₂   => .and (Φ₁.rename f renameAtom) (Φ₂.rename f renameAtom)
  | .or Φ₁ Φ₂    => .or (Φ₁.rename f renameAtom) (Φ₂.rename f renameAtom)
  | .implies Φ₁ Φ₂ => .implies (Φ₁.rename f renameAtom) (Φ₂.rename f renameAtom)
  | .exists_ x Φ => .exists_ (f x) (Φ.rename f renameAtom)
  | .forall_ x Φ => .forall_ (f x) (Φ.rename f renameAtom)

/-- Eliminate `forall_` in favour of `¬∃x, ¬Φ`. -/
def eliminateForall : Formula σ α → Formula σ α
  | .atom a      => .atom a
  | .not Φ       => .not Φ.eliminateForall
  | .and Φ₁ Φ₂   => .and Φ₁.eliminateForall Φ₂.eliminateForall
  | .or Φ₁ Φ₂    => .or Φ₁.eliminateForall Φ₂.eliminateForall
  | .implies Φ₁ Φ₂ => .implies Φ₁.eliminateForall Φ₂.eliminateForall
  | .exists_ x Φ => .exists_ x Φ.eliminateForall
  | .forall_ x Φ => .not (.exists_ x (.not Φ.eliminateForall))

/-- Eliminate `implies` in favour of `¬Φ ∨ Ψ`. -/
def eliminateImplies : Formula σ α → Formula σ α
  | .atom a        => .atom a
  | .not Φ         => .not Φ.eliminateImplies
  | .and Φ₁ Φ₂     => .and Φ₁.eliminateImplies Φ₂.eliminateImplies
  | .or Φ₁ Φ₂      => .or Φ₁.eliminateImplies Φ₂.eliminateImplies
  | .implies Φ₁ Φ₂ => .or (.not Φ₁.eliminateImplies) Φ₂.eliminateImplies
  | .exists_ x Φ   => .exists_ x Φ.eliminateImplies
  | .forall_ x Φ   => .forall_ x Φ.eliminateImplies

theorem rename_isQF (f : σ → τ) (ra : α → β) :
    ∀ (Φ : Formula σ α), Φ.IsQuantifierFree →
    (Φ.rename f ra).IsQuantifierFree
  | .atom _, _ => trivial
  | .not Φ, h => rename_isQF f ra Φ h
  | .and Φ₁ Φ₂, ⟨h₁, h₂⟩ =>
    ⟨rename_isQF f ra Φ₁ h₁, rename_isQF f ra Φ₂ h₂⟩
  | .or Φ₁ Φ₂, ⟨h₁, h₂⟩ =>
    ⟨rename_isQF f ra Φ₁ h₁, rename_isQF f ra Φ₂ h₂⟩
  | .implies Φ₁ Φ₂, ⟨h₁, h₂⟩ =>
    ⟨rename_isQF f ra Φ₁ h₁, rename_isQF f ra Φ₂ h₂⟩

theorem rename_isPrenex (f : σ → τ) (ra : α → β)
    {Φ : Formula σ α}
    (h : IsPrenex Φ) : IsPrenex (Φ.rename f ra) := by
  induction h with
  | qf hqf => exact .qf (rename_isQF f ra _ hqf)
  | exists_ _ ih => exact .exists_ ih
  | forall_ _ ih => exact .forall_ ih

theorem rename_quantifierDepth (f : σ → τ) (ra : α → β)
    (Φ : Formula σ α) :
    (Φ.rename f ra).quantifierDepth = Φ.quantifierDepth := by
  induction Φ with
  | atom => simp [rename, quantifierDepth]
  | not _ ih => simp [rename, quantifierDepth, ih]
  | and _ _ ih₁ ih₂ =>
    simp [rename, quantifierDepth, ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp [rename, quantifierDepth, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ =>
    simp [rename, quantifierDepth, ih₁, ih₂]
  | exists_ _ _ ih =>
    simp [rename, quantifierDepth, ih]
  | forall_ _ _ ih =>
    simp [rename, quantifierDepth, ih]

end Formula

end Azurite.BPR
