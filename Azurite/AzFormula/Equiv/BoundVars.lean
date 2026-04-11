/-
  Equivalence proofs: boundVarsOf agrees with BPR boundVars.
-/
import Azurite.AzFormula.Equiv.Basic

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR Formula

variable {σ : Type*} [DecidableEq σ]
    {n : ℕ} {D : Type*} [CommRing D] {ord : MonomialOrder}

/-- The generic `boundVarsOf` agrees with the BPR-specialized `boundVars`
    for `FieldAtom`, directly. -/
theorem boundVarsOf_eq_boundVars_fieldAtom
    (Φ : Formula σ (FieldAtom σ D)) :
    boundVarsOf Φ = Φ.boundVars := by
  induction Φ with
  | atom _ => rfl
  | not _ ih => simp only [boundVarsOf, boundVars]; exact ih
  | and _ _ ih₁ ih₂ => simp only [boundVarsOf, boundVars]; rw [ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp only [boundVarsOf, boundVars]; rw [ih₁, ih₂]
  | implies _ _ ih₁ ih₂ => simp only [boundVarsOf, boundVars]; rw [ih₁, ih₂]
  | exists_ _ _ ih => simp only [boundVarsOf, boundVars]; rw [ih]
  | forall_ _ _ ih => simp only [boundVarsOf, boundVars]; rw [ih]

/-- The generic `boundVarsOf` on an `AzFieldAtom` formula agrees with the
    BPR `boundVars` after converting via `azFormulaToFieldFormula`. -/
theorem boundVarsOf_eq_boundVars_azFieldAtom
    (Φ : Formula (Fin n) (AzFieldAtom n D ord)) :
    boundVarsOf Φ = (azFormulaToFieldFormula Φ).boundVars := by
  induction Φ with
  | atom a =>
    show ∅ = (azFormulaToFieldFormula (.atom a)).boundVars
    simp only [azFormulaToFieldFormula, mapAtom, boundVars]
  | not _ ih =>
    simp only [boundVarsOf, show azFormulaToFieldFormula (.not _) =
      .not (azFormulaToFieldFormula _) from rfl, boundVars]; exact ih
  | and _ _ ih₁ ih₂ =>
    simp only [boundVarsOf, show azFormulaToFieldFormula (.and _ _) =
      .and (azFormulaToFieldFormula _) (azFormulaToFieldFormula _) from rfl, boundVars]
    rw [ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp only [boundVarsOf, show azFormulaToFieldFormula (.or _ _) =
      .or (azFormulaToFieldFormula _) (azFormulaToFieldFormula _) from rfl, boundVars]
    rw [ih₁, ih₂]
  | implies _ _ ih₁ ih₂ =>
    simp only [boundVarsOf, show azFormulaToFieldFormula (.implies _ _) =
      .implies (azFormulaToFieldFormula _) (azFormulaToFieldFormula _) from rfl, boundVars]
    rw [ih₁, ih₂]
  | exists_ _ _ ih =>
    simp only [boundVarsOf, show azFormulaToFieldFormula (.exists_ _ _) =
      .exists_ _ (azFormulaToFieldFormula _) from rfl, boundVars]
    rw [ih]
  | forall_ _ _ ih =>
    simp only [boundVarsOf, show azFormulaToFieldFormula (.forall_ _ _) =
      .forall_ _ (azFormulaToFieldFormula _) from rfl, boundVars]
    rw [ih]

end Azurite
