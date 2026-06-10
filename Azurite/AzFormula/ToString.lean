/-
  ToString instances for AzFieldAtom and Formula.
-/
import Azurite.AzFormula.Basic
import Azurite.AzMvPolynomial.ToString

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR Formula

namespace AzFieldAtom

variable {n : ℕ} {R : Type _} [DecidableEq R] [Semiring R] [NeZero (1 : R)] [ParsableCoeff R]
    {ord : MonomialOrder}

section Display

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- Convert an `AzFieldAtom` to a string using the display naming scheme `F`. -/
def toStrWith (a : AzFieldAtom n R ord) : String :=
  let p := a.poly.toStrWith F
  if a.isEq then s!"{p} = 0" else s!"{p} ≠ 0"

end Display

/-- Default `toStr`: uses `IndexedVar n` naming (`x₀, x₁, …`). -/
@[inline] def toStr (a : AzFieldAtom n R ord) : String :=
  a.toStrWith (IndexedVar n)

end AzFieldAtom

instance instToStringAzFieldAtom {n : ℕ} {R : Type*} [DecidableEq R] [Semiring R] [NeZero (1 : R)] [ParsableCoeff R]
    {ord : MonomialOrder} :
    ToString (AzFieldAtom n R ord) where
  toString := AzFieldAtom.toStr

/-! ### Formula display with a Var-based naming scheme

    When `σ = Fin n` and atoms are `AzFieldAtom n R ord`, we can display
    the formula by threading a `ParsableVar F n` display type through both
    atoms and quantifier-bound variables. -/

namespace BPR.Formula

variable {n : ℕ} {R : Type _} [DecidableEq R] [Semiring R] [NeZero (1 : R)] [ParsableCoeff R]
    {ord : MonomialOrder}

section Display

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- Render a `Fin n` variable as a string via the display type `F`. -/
def varStrWith (x : Fin n) : String :=
  String.ofList (ParsableVar.toChars (Var.ofFin x : F))

/-- Display a `Formula (Fin n) (AzFieldAtom n R ord)` using naming scheme `F`
    for both the atoms and the quantifier-bound variables. -/
def toStrWithGo (parens : Bool) :
    Formula (Fin n) (AzFieldAtom n R ord) → String
  | .atom a => a.toStrWith F
  | .not (.atom a) => s!"¬({a.toStrWith F})"
  | .not Φ => s!"¬({toStrWithGo false Φ})"
  | .and Φ₁ Φ₂ =>
    let s := s!"{toStrWithGo true Φ₁} ∧ {toStrWithGo true Φ₂}"
    if parens then s!"({s})" else s
  | .or Φ₁ Φ₂ =>
    let s := s!"{toStrWithGo true Φ₁} ∨ {toStrWithGo true Φ₂}"
    if parens then s!"({s})" else s
  | .implies Φ₁ Φ₂ =>
    let s := s!"{toStrWithGo true Φ₁} → {toStrWithGo true Φ₂}"
    if parens then s!"({s})" else s
  | .exists_ x Φ => s!"∃{varStrWith F x}, {toStrWithGo false Φ}"
  | .forall_ x Φ => s!"∀{varStrWith F x}, {toStrWithGo false Φ}"

/-- Display a `Formula (Fin n) (AzFieldAtom n R ord)` using naming scheme `F`
    for both the atoms and the quantifier-bound variables. -/
def toStrWith (Φ : Formula (Fin n) (AzFieldAtom n R ord)) : String :=
  toStrWithGo F false Φ

end Display

/-- Default `toStr` for `Formula (Fin n) (AzFieldAtom n R ord)`:
    uses `IndexedVar n` naming (`x₀, x₁, …`). -/
@[inline] def toStr (Φ : Formula (Fin n) (AzFieldAtom n R ord)) : String :=
  Φ.toStrWith (IndexedVar n)

end BPR.Formula

/-- Preferred `ToString` for `Formula (Fin n) (AzFieldAtom n R ord)`, using
    `IndexedVar n` naming for both atoms and quantifier variables. -/
instance (priority := high) instToStringFormula {n : ℕ} {R : Type*} [DecidableEq R] [Semiring R]
    [NeZero (1 : R)] [ParsableCoeff R] {ord : MonomialOrder} :
    ToString (Formula (Fin n) (AzFieldAtom n R ord)) where
  toString := BPR.Formula.toStr

/-! ### Generic fallback `ToString` for arbitrary `Formula σ α` -/

/-- Display a `Formula` in a readable form. -/
instance instToStringFormulaAzFieldAtom {σ : Type*} [ToString σ] {α : Type*} [ToString α] :
    ToString (Formula σ α) where
  toString := go false
where
  go (parens : Bool) : Formula σ α → String
    | .atom a => toString a
    | .not (.atom a) => s!"¬({toString a})"
    | .not Φ => s!"¬({go false Φ})"
    | .and Φ₁ Φ₂ =>
      let s := s!"{go true Φ₁} ∧ {go true Φ₂}"
      if parens then s!"({s})" else s
    | .or Φ₁ Φ₂ =>
      let s := s!"{go true Φ₁} ∨ {go true Φ₂}"
      if parens then s!"({s})" else s
    | .implies Φ₁ Φ₂ =>
      let s := s!"{go true Φ₁} → {go true Φ₂}"
      if parens then s!"({s})" else s
    | .exists_ x Φ => s!"∃{x}, {go false Φ}"
    | .forall_ x Φ => s!"∀{x}, {go false Φ}"

end Azurite
