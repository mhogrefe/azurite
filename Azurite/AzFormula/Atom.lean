/-
  Atom types for AzFormula, analogous to FieldAtom but using AzMvPolynomial.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial

/-- An atom in the language of fields, using `AzMvPolynomial`:
    a polynomial `P` together with `isEq = true` for `P = 0`
    or `isEq = false` for `P ≠ 0`. -/
structure AzFieldAtom (σ : Type*) {n : ℕ} [LinearOrder σ] [Var σ n]
    (R : Type*) [Semiring R] (ord : MonomialOrder := .Degrevlex) where
  poly : AzMvPolynomial σ R ord
  isEq : Bool

namespace AzFieldAtom

variable {σ : Type*} {n : ℕ} [LinearOrder σ] [Var σ n]
    {R : Type*} [Semiring R] {ord : MonomialOrder}

/-- The atom `P = 0`. -/
def eqZero (P : AzMvPolynomial σ R ord) : AzFieldAtom σ R ord := ⟨P, true⟩

/-- The atom `P ≠ 0`. -/
def neZero (P : AzMvPolynomial σ R ord) : AzFieldAtom σ R ord := ⟨P, false⟩

end AzFieldAtom

end Azurite
