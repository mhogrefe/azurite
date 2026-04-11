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
import Azurite.AzFormula.ToString
import Azurite.AzMvPolynomial.Parse

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR Formula

variable {σ : Type*} {α : Type*}

/-! ### Quantifier depth preserved by rename -/

theorem renameFormulaEquiv_quantifierDepth [AtomRename α σ]
    (e : σ ≃ σ) (Φ : Formula σ α) :
    (renameFormulaEquiv e Φ).quantifierDepth = Φ.quantifierDepth := by
  simp [renameFormulaEquiv, rename_quantifierDepth]

/-- The number of fresh variables needed by `toPrenexNNF` to fully pull all
    quantifiers to the front. This is `quantifierDepth` for pure quantifier
    chains, but larger for formulas with nested `and`/`or` because each binary
    node's `mergePrenex` call also consumes fresh variables equal to the sum
    of quantifier depths of its prenex arguments. -/
def freshVarsNeeded : Formula σ α → ℕ
  | .atom _ => 0
  | .not Φ => freshVarsNeeded Φ
  | .exists_ _ Φ => freshVarsNeeded Φ
  | .forall_ _ Φ => freshVarsNeeded Φ
  | .and Φ₁ Φ₂ => freshVarsNeeded Φ₁ + freshVarsNeeded Φ₂ +
      Φ₁.quantifierDepth + Φ₂.quantifierDepth
  | .or Φ₁ Φ₂ => freshVarsNeeded Φ₁ + freshVarsNeeded Φ₂ +
      Φ₁.quantifierDepth + Φ₂.quantifierDepth
  | .implies Φ₁ Φ₂ => freshVarsNeeded Φ₁ + freshVarsNeeded Φ₂

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

/-- Generate a list of fresh `Fin m` variables, starting at index `start`. -/
def freshVars (m start count : ℕ) (h : start + count ≤ m) : List (Fin m) :=
  (List.finRange count).map fun i => ⟨start + i.val, by omega⟩

/-- Convert a formula over `Fin n` to prenex normal form. Returns a formula
    over `Fin m` where `m = n + freshVarsNeeded (toNNF Φ)`.

    Pipeline: `toNNF → embed to Fin m → toPrenexNNF` -/
def toPrenex {n : ℕ}
    {R : Type*} [Semiring R] {ord : MonomialOrder}
    (Φ : Formula (Fin n) (AzFieldAtom n R ord)) :
    let m := n + freshVarsNeeded (toNNF Φ)
    Formula (Fin m) (AzFieldAtom m R ord) :=
  let fvn := freshVarsNeeded (toNNF Φ)
  let m := n + fvn
  let nnf := toNNF Φ
  let h_le : n ≤ m := Nat.le_add_right n fvn
  let embedded : Formula (Fin m) (AzFieldAtom m R ord) :=
    nnf.rename (Fin.castLE h_le)
      (AzFieldAtom.renameVarsMonotone (Fin.castLE h_le)
        (fun _ _ hab => hab))
  have h_bound : n + fvn ≤ m := le_refl m
  let freshVarList := freshVars m n fvn h_bound
  (toPrenexNNF embedded freshVarList).1

end Azurite

/-! ### #guard examples -/

open Azurite AzMvPolynomial MonicMonomial Monomial BPR Formula

section PrenexExamples

open Azurite

/-- Parse a polynomial in ℤ[x₀, x₁] as an abbreviation. -/
private def p₂ (s : String) : AzMvPolynomial 2 ℤ .Degrevlex :=
  (AzMvPolynomial.parse s.toList).getD 0

private abbrev F₂ := Formula (Fin 2) (AzFieldAtom 2 ℤ .Degrevlex)

/-- Variables x₀ and x₁ for quantifying. -/
private def x₀ : Fin 2 := ⟨0, by omega⟩
private def x₁ : Fin 2 := ⟨1, by omega⟩

-- Example 1: A simple atom (already prenex, no quantifiers)
-- toPrenex (x₀ = 0) = (x₀ = 0)
#guard toString (toPrenex (azEqZero (p₂ "x₀") : F₂)) == "x₀ = 0"

-- Example 2: eliminateImplies on (x₀ = 0) → (x₁ = 0)
-- becomes ¬(x₀ = 0) ∨ (x₁ = 0)  (eliminateImplies doesn't use AtomNeg)
private def ex2 : F₂ := .implies (azEqZero (p₂ "x₀")) (azEqZero (p₂ "x₁"))
#guard toString (ex2.eliminateImplies) == "¬(x₀ = 0) ∨ x₁ = 0"

-- Example 3: toNNF on ¬(A ∧ B) — De Morgan with atom-level negation
-- ¬(x₀ = 0 ∧ x₁ = 0) becomes (x₀ ≠ 0) ∨ (x₁ ≠ 0)
private def ex3 : F₂ := .not (.and (azEqZero (p₂ "x₀")) (azEqZero (p₂ "x₁")))
#guard toString (toNNF ex3) == "x₀ ≠ 0 ∨ x₁ ≠ 0"

-- Example 4: toNNF on ¬∃x₀, (x₀ = 0) — becomes ∀x₀, (x₀ ≠ 0)
private def ex4 : F₂ := .not (.exists_ x₀ (azEqZero (p₂ "x₀")))
#guard toString (toNNF ex4) == "∀x₀, x₀ ≠ 0"

-- Example 5: toPrenex on (∃x₀, x₀ = 0) ∧ (x₁ = 0)
-- Should pull the ∃ out: ∃x₂, (x₂ = 0 ∧ x₁ = 0)  (fresh variable x₂)
private def ex5 : F₂ := .and (.exists_ x₀ (azEqZero (p₂ "x₀"))) (azEqZero (p₂ "x₁"))
#guard toString (toPrenex ex5) == "∃x₂, x₂ = 0 ∧ x₁ = 0"

-- Example 6: toPrenex on ∀x₀, ∃x₁, (x₀ + x₁ = 0)
-- Already prenex, so should stay the same
private def ex6 : F₂ := .forall_ x₀ (.exists_ x₁ (azEqZero (p₂ "x₀+x₁")))
#guard toString (toPrenex ex6) == "∀x₀, ∃x₁, x₀+x₁ = 0"

-- Example 7: toPrenex on (∃x₀, x₀ = 0) ∨ (∃x₁, x₁ = 0)
-- Should produce ∃x₂, ∃x₃, (x₂ = 0 ∨ x₃ = 0) with two fresh vars
private def ex7 : F₂ := .or (.exists_ x₀ (azEqZero (p₂ "x₀")))
                             (.exists_ x₁ (azEqZero (p₂ "x₁")))
#guard toString (toPrenex ex7) == "∃x₂, ∃x₃, x₂ = 0 ∨ x₃ = 0"

end PrenexExamples
