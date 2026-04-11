/-
  Atom types for AzFormula, analogous to FieldAtom but using AzMvPolynomialNew.
-/
import Azurite.AzMvPolynomial.New.Vars
import Azurite.AzMvPolynomial.New.Rename

namespace Azurite

open AzMvPolynomialNew MonicMonomialNew MonomialNew

/-- An atom in the language of fields, using `AzMvPolynomialNew`:
    a polynomial `P` together with `isEq = true` for `P = 0`
    or `isEq = false` for `P ≠ 0`. -/
structure AzFieldAtom (n : ℕ) (R : Type*) [Semiring R]
    (ord : MonomialOrder := .Degrevlex) where
  poly : AzMvPolynomialNew n R ord
  isEq : Bool

namespace AzFieldAtom

variable {n : ℕ} {R : Type*} [Semiring R] {ord : MonomialOrder}

/-- The atom `P = 0`. -/
def eqZero (P : AzMvPolynomialNew n R ord) : AzFieldAtom n R ord := ⟨P, true⟩

/-- The atom `P ≠ 0`. -/
def neZero (P : AzMvPolynomialNew n R ord) : AzFieldAtom n R ord := ⟨P, false⟩

/-- Free variables of an `AzFieldAtom`. Computable. -/
def vars (a : AzFieldAtom n R ord) : Finset (Fin n) :=
  a.poly.vars

/-- Rename variables in an `AzFieldAtom` using a strictly-monotone
    variable map. Computable. -/
def renameVarsMonotone {n₂ : ℕ}
    (f : Fin n → Fin n₂) (hg : StrictMono f)
    (a : AzFieldAtom n R ord) : AzFieldAtom n₂ R ord :=
  ⟨a.poly.renameMonotone f hg, a.isEq⟩

/-- Rename variables in an `AzFieldAtom` using an injective variable map.
    Computable. -/
def renameVarsInjective {n₂ : ℕ}
    (f : Fin n → Fin n₂) (hf : Function.Injective f)
    (a : AzFieldAtom n R ord) (ord₂ : MonomialOrder := ord) :
    AzFieldAtom n₂ R ord₂ :=
  ⟨a.poly.renameInjective f hf ord₂, a.isEq⟩

/-- Rename variables in an `AzFieldAtom` using a general variable map.
    Non-injective maps may merge monomials. Computable. -/
def renameVars {n₂ : ℕ} [DecidableEq R] (f : Fin n → Fin n₂)
    (a : AzFieldAtom n R ord) (ord₂ : MonomialOrder := ord) :
    AzFieldAtom n₂ R ord₂ :=
  ⟨a.poly.rename f ord₂, a.isEq⟩

end AzFieldAtom

end Azurite
