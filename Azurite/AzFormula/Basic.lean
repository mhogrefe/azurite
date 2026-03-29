/-
  Computable operations on Formula (AzFieldAtom).

  These mirror the noncomputable definitions in BPR §1.1, but are
  fully computable because AzMvPolynomial operations are computable.
-/
import Azurite.AzFormula.Atom
import Azurite.BasuPollackRoy.Chapter1.Section1_1

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR

variable {σ : Type*} {n : ℕ} [LinearOrder σ] [Var σ n]
    {R : Type*} [Semiring R] {ord : MonomialOrder}

/-! ### Formula constructors -/

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

/-! ### Free variables (computable) -/

/-- Free variables of an `AzFieldAtom` formula.
    Unlike the BPR `freeVars`, this is fully computable. -/
def azFreeVars [DecidableEq σ] :
    Formula σ (AzFieldAtom σ R ord) → Finset σ
  | .atom a        => a.vars
  | .not Φ         => azFreeVars Φ
  | .and Φ₁ Φ₂     => azFreeVars Φ₁ ∪ azFreeVars Φ₂
  | .or Φ₁ Φ₂      => azFreeVars Φ₁ ∪ azFreeVars Φ₂
  | .implies Φ₁ Φ₂ => azFreeVars Φ₁ ∪ azFreeVars Φ₂
  | .exists_ x Φ   => azFreeVars Φ \ {x}
  | .forall_ x Φ   => azFreeVars Φ \ {x}

/-- A formula is a sentence if it has no free variables. Decidable. -/
def azIsSentence [DecidableEq σ]
    (Φ : Formula σ (AzFieldAtom σ R ord)) : Bool :=
  azFreeVars Φ = ∅

/-! ### Conjunction of equalities -/

/-- Conjunction of `P = 0` atoms from a list of polynomials. -/
def azConjEqZero :
    List (AzMvPolynomial σ R ord) → Formula σ (AzFieldAtom σ R ord)
  | []     => azTrueFormula
  | [P]    => azEqZero P
  | P :: rest => .and (azEqZero P) (azConjEqZero rest)

end Azurite
