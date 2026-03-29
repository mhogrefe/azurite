/-
  Atom types for AzFormula, analogous to FieldAtom but using AzMvPolynomial.
-/
import Azurite.AzMvPolynomial.Vars
import Azurite.AzMvPolynomial.Rename

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

/-- Free variables of an `AzFieldAtom`. Computable. -/
def vars (a : AzFieldAtom σ R ord) : Finset σ :=
  a.poly.vars

/-- Rename variables in an `AzFieldAtom` using a strictly-monotone
    variable map. Computable. -/
def renameVarsMonotone {τ : Type*} {m : ℕ} [LinearOrder τ] [Var τ m]
    (f : σ → τ) (hg : StrictMono (fun i : Fin n => Var.toFin (f (Var.ofFin i))))
    (a : AzFieldAtom σ R ord) : AzFieldAtom τ R ord :=
  ⟨a.poly.renameMonotone f hg, a.isEq⟩

/-- Rename variables in an `AzFieldAtom` using an injective variable map.
    Computable. -/
def renameVarsInjective {τ : Type*} {m : ℕ} [LinearOrder τ] [Var τ m]
    (f : σ → τ) (hf : Function.Injective f)
    (a : AzFieldAtom σ R ord) (ord₂ : MonomialOrder := ord) :
    AzFieldAtom τ R ord₂ :=
  ⟨a.poly.renameInjective f hf ord₂, a.isEq⟩

/-- Rename variables in an `AzFieldAtom` using a general variable map.
    Non-injective maps may merge monomials. Computable. -/
def renameVars {τ : Type*} {m : ℕ} [LinearOrder τ] [Var τ m]
    [DecidableEq R] (f : σ → τ)
    (a : AzFieldAtom σ R ord) (ord₂ : MonomialOrder := ord) :
    AzFieldAtom τ R ord₂ :=
  ⟨a.poly.rename f ord₂, a.isEq⟩

end AzFieldAtom

end Azurite
