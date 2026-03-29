/-
  Computable prenex normal form conversion.

  The algorithm:
  1. Convert to NNF (toNNF)
  2. Recursively convert subformulas to prenex form
  3. Merge prenex subformulas by pulling quantifiers out of ∧/∨

  Fresh variables are drawn from a pre-computed list to avoid
  bound variable capture during quantifier pulling.
-/
import Azurite.AzFormula.Basic

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR Formula

variable {σ : Type*} {α : Type*}

/-! ### Quantifier depth preserved by rename -/

theorem renameFormulaEquiv_quantifierDepth [AtomRename α σ]
    (e : σ ≃ σ) (Φ : Formula σ α) :
    (renameFormulaEquiv e Φ).quantifierDepth = Φ.quantifierDepth := by
  simp [renameFormulaEquiv, rename_quantifierDepth]

/-! ### Merge two prenex formulas under ∧ or ∨ -/

/-- Pull all quantifiers from both sides of a binary connective to the front.
    Fresh variables are consumed from the list as needed. -/
def mergePrenex [DecidableEq σ] [AtomRename α σ]
    (op : Formula σ α → Formula σ α → Formula σ α)
    (left right : Formula σ α) (freshVars : List σ) :
    Formula σ α × List σ :=
  match left, right, freshVars with
  -- Left ∃: peel
  | .exists_ x body, right, fresh :: rest =>
    let body' := renameFormulaEquiv (Equiv.swap x fresh) body
    let (result, rest') := mergePrenex op body' right rest
    (.exists_ fresh result, rest')
  -- Left ∀: peel
  | .forall_ x body, right, fresh :: rest =>
    let body' := renameFormulaEquiv (Equiv.swap x fresh) body
    let (result, rest') := mergePrenex op body' right rest
    (.forall_ fresh result, rest')
  -- Left is QF, Right ∃: peel
  | left, .exists_ y body, fresh :: rest =>
    if quantifierDepth left = 0 then
      let body' := renameFormulaEquiv (Equiv.swap y fresh) body
      let (result, rest') := mergePrenex op left body' rest
      (.exists_ fresh result, rest')
    else (op left (.exists_ y body), fresh :: rest)
  -- Left is QF, Right ∀: peel
  | left, .forall_ y body, fresh :: rest =>
    if quantifierDepth left = 0 then
      let body' := renameFormulaEquiv (Equiv.swap y fresh) body
      let (result, rest') := mergePrenex op left body' rest
      (.forall_ fresh result, rest')
    else (op left (.forall_ y body), fresh :: rest)
  -- Both QF or out of fresh variables
  | _, _, _ => (op left right, freshVars)
termination_by left.quantifierDepth + right.quantifierDepth
decreasing_by
  all_goals simp_all [renameFormulaEquiv_quantifierDepth, quantifierDepth]

/-! ### Prenex conversion on NNF formulas -/

/-- Convert an NNF formula to prenex form. Structurally recursive.
    The `mergePrenex` helper handles the ∧/∨ cases. -/
def toPrenexNNF [DecidableEq σ] [AtomRename α σ] :
    Formula σ α → List σ → Formula σ α × List σ
  | .atom a, fv => (.atom a, fv)
  | .not Φ, fv => (.not Φ, fv)  -- after NNF, only on atoms
  | .exists_ x Φ, fv =>
    let (Φ', fv') := toPrenexNNF Φ fv
    (.exists_ x Φ', fv')
  | .forall_ x Φ, fv =>
    let (Φ', fv') := toPrenexNNF Φ fv
    (.forall_ x Φ', fv')
  | .and Φ₁ Φ₂, fv =>
    let (Φ₁', fv₁) := toPrenexNNF Φ₁ fv
    let (Φ₂', fv₂) := toPrenexNNF Φ₂ fv₁
    mergePrenex .and Φ₁' Φ₂' fv₂
  | .or Φ₁ Φ₂, fv =>
    let (Φ₁', fv₁) := toPrenexNNF Φ₁ fv
    let (Φ₂', fv₂) := toPrenexNNF Φ₂ fv₁
    mergePrenex .or Φ₁' Φ₂' fv₂
  | .implies Φ₁ Φ₂, fv =>
    (.implies Φ₁ Φ₂, fv)

/-! ### Full prenex pipeline -/

/-- Generate a list of fresh `IndexedVar m` variables starting at index `start`. -/
def freshIndexedVars (m start count : ℕ) (h : start + count ≤ m) :
    List (IndexedVar m) :=
  (List.finRange count).map fun i => ⟨⟨start + i.val, by omega⟩⟩

/-- Convert a formula over `IndexedVar n` to prenex normal form.
    Returns a formula over `IndexedVar m` where `m = n + quantifierDepth Φ`.

    Pipeline: `toNNF → embed to IndexedVar m → toPrenexNNF` -/
def toPrenex {n : ℕ} {R : Type*} [Semiring R] {ord : MonomialOrder}
    (Φ : Formula (IndexedVar n) (AzFieldAtom (IndexedVar n) R ord)) :
    let m := n + Φ.quantifierDepth
    Formula (IndexedVar m) (AzFieldAtom (IndexedVar m) R ord) :=
  let depth := Φ.quantifierDepth
  let m := n + depth
  let nnf := toNNF Φ
  let h_le : n ≤ m := Nat.le_add_right n depth
  let embedded : Formula (IndexedVar m) (AzFieldAtom (IndexedVar m) R ord) :=
    nnf.rename (Var.embed h_le)
      (AzFieldAtom.renameVarsMonotone (Var.embed h_le)
        (Var.embed_fin_strictMono h_le))
  have h_bound : n + depth ≤ m := le_refl m
  let freshVarList := freshIndexedVars m n depth h_bound
  (toPrenexNNF embedded freshVarList).1

end Azurite
