/-
  Equivalence proofs: freeVarsOf agrees with BPR freeVars.
-/
import Azurite.AzFormula.Equiv.Basic
import Azurite.AzMvPolynomial.Equiv.Vars

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR Formula

variable {σ : Type*} [DecidableEq σ]
    {n : ℕ} {D : Type*} [CommRing D] {ord : MonomialOrder}

/-- The generic `freeVarsOf` agrees with the BPR-specialized `freeVars`
    for `FieldAtom`, directly. -/
theorem freeVarsOf_eq_freeVars_fieldAtom
    (Φ : Formula σ (FieldAtom σ D)) :
    freeVarsOf Φ = Φ.freeVars := by
  induction Φ with
  | atom _ => rfl
  | not _ ih => simp only [freeVarsOf, freeVars]; exact ih
  | and _ _ ih₁ ih₂ => simp only [freeVarsOf, freeVars]; rw [ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp only [freeVarsOf, freeVars]; rw [ih₁, ih₂]
  | implies _ _ ih₁ ih₂ => simp only [freeVarsOf, freeVars]; rw [ih₁, ih₂]
  | exists_ _ _ ih => simp only [freeVarsOf, freeVars]; rw [ih]
  | forall_ _ _ ih => simp only [freeVarsOf, freeVars]; rw [ih]

/-- The generic `freeVarsOf` on an `AzFieldAtom` formula agrees with the
    BPR `freeVars` after converting via `azFormulaToFieldFormula`. -/
theorem freeVarsOf_eq_freeVars_azFieldAtom
    (Φ : Formula (Fin n) (AzFieldAtom n D ord)) :
    freeVarsOf Φ = (azFormulaToFieldFormula Φ).freeVars := by
  induction Φ with
  | atom a =>
    show a.poly.vars = (azFormulaToFieldFormula (.atom a)).freeVars
    simp only [azFormulaToFieldFormula, mapAtom, freeVars, AzFieldAtom.toFieldAtom]
    convert (toMvPoly_vars a.poly).symm
  | not _ ih =>
    simp only [freeVarsOf, show azFormulaToFieldFormula (.not _) =
      .not (azFormulaToFieldFormula _) from rfl, freeVars]; exact ih
  | and _ _ ih₁ ih₂ =>
    simp only [freeVarsOf, show azFormulaToFieldFormula (.and _ _) =
      .and (azFormulaToFieldFormula _) (azFormulaToFieldFormula _) from rfl, freeVars]
    rw [ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp only [freeVarsOf, show azFormulaToFieldFormula (.or _ _) =
      .or (azFormulaToFieldFormula _) (azFormulaToFieldFormula _) from rfl, freeVars]
    rw [ih₁, ih₂]
  | implies _ _ ih₁ ih₂ =>
    simp only [freeVarsOf, show azFormulaToFieldFormula (.implies _ _) =
      .implies (azFormulaToFieldFormula _) (azFormulaToFieldFormula _) from rfl, freeVars]
    rw [ih₁, ih₂]
  | exists_ _ _ ih =>
    simp only [freeVarsOf, show azFormulaToFieldFormula (.exists_ _ _) =
      .exists_ _ (azFormulaToFieldFormula _) from rfl, freeVars]
    rw [ih]
  | forall_ _ _ ih =>
    simp only [freeVarsOf, show azFormulaToFieldFormula (.forall_ _ _) =
      .forall_ _ (azFormulaToFieldFormula _) from rfl, freeVars]
    rw [ih]

end Azurite
