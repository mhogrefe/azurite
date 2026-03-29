/-
  ToString instances for AzFieldAtom and Formula.
-/
import Azurite.AzFormula.Basic
import Azurite.AzMvPolynomial.ToString

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR Formula

/-- Display an `AzFieldAtom` as `P = 0` or `P ≠ 0`. -/
instance {σ : Type*} {n : ℕ} [LinearOrder σ] [ParsableVar σ n]
    {R : Type*} [DecidableEq R] [Semiring R] [ParsableCoeff R]
    {ord : MonomialOrder} :
    ToString (AzFieldAtom σ R ord) where
  toString a :=
    let p := toString a.poly
    if a.isEq then s!"{p} = 0" else s!"{p} ≠ 0"

/-- Display a `Formula` in a readable form. -/
instance {σ : Type*} [ToString σ] {α : Type*} [ToString α] :
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
