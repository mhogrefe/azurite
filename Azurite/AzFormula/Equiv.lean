/-
  Equivalence proofs between computable AzFormula operations and their
  noncomputable BPR counterparts.
-/
import Azurite.AzFormula.Basic
import Azurite.AzFormula.Realization
import Azurite.AzMvPolynomial.Equiv.Vars

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR Formula

/-! ### mapAtom functor laws -/

variable {σ : Type*} {α β γ : Type*}

@[simp] theorem mapAtom_id (Φ : Formula σ α) :
    Φ.mapAtom id = Φ := by
  induction Φ with
  | atom _ => rfl
  | not _ ih => simp [mapAtom, ih]
  | and _ _ ih₁ ih₂ => simp [mapAtom, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [mapAtom, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ => simp [mapAtom, ih₁, ih₂]
  | exists_ _ _ ih => simp [mapAtom, ih]
  | forall_ _ _ ih => simp [mapAtom, ih]

theorem mapAtom_comp (f : β → γ) (g : α → β) (Φ : Formula σ α) :
    (Φ.mapAtom g).mapAtom f = Φ.mapAtom (f ∘ g) := by
  induction Φ with
  | atom _ => rfl
  | not _ ih => simp [mapAtom, ih]
  | and _ _ ih₁ ih₂ => simp [mapAtom, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [mapAtom, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ => simp [mapAtom, ih₁, ih₂]
  | exists_ _ _ ih => simp [mapAtom, ih]
  | forall_ _ _ ih => simp [mapAtom, ih]

/-! ### Formula conversion round-trips -/

variable {n : ℕ} [LinearOrder σ] [Var σ n] [DecidableEq σ]
    {D : Type*} [CommRing D] {ord : MonomialOrder}

theorem fieldFormulaToAzFormula_azFormulaToFieldFormula
    (Φ : Formula σ (AzFieldAtom σ D ord)) :
    fieldFormulaToAzFormula (azFormulaToFieldFormula Φ) = Φ := by
  simp only [fieldFormulaToAzFormula, azFormulaToFieldFormula, mapAtom_comp]
  show Φ.mapAtom (azFieldAtomOfFieldAtom ∘ AzFieldAtom.toFieldAtom) = Φ
  conv_rhs => rw [← mapAtom_id Φ]
  congr 1; funext a; exact azFieldAtomOfFieldAtom_toFieldAtom a

theorem azFormulaToFieldFormula_fieldFormulaToAzFormula
    (Φ : Formula σ (FieldAtom σ D)) :
    azFormulaToFieldFormula (fieldFormulaToAzFormula (ord := ord) Φ) = Φ := by
  simp only [azFormulaToFieldFormula, fieldFormulaToAzFormula, mapAtom_comp]
  show Φ.mapAtom (AzFieldAtom.toFieldAtom ∘ azFieldAtomOfFieldAtom) = Φ
  conv_rhs => rw [← mapAtom_id Φ]
  congr 1; funext a; exact toFieldAtom_azFieldAtomOfFieldAtom a

/-! ### Free variables equivalence -/

/-- The computable `azFreeVars` agrees with the noncomputable `freeVars`
    after converting via `azFormulaToFieldFormula`. -/
theorem azFreeVars_eq_freeVars
    (Φ : Formula σ (AzFieldAtom σ D ord)) :
    azFreeVars Φ = (azFormulaToFieldFormula Φ).freeVars := by
  induction Φ with
  | atom a =>
    simp only [azFreeVars, azFormulaToFieldFormula, mapAtom, freeVars,
      AzFieldAtom.vars, FieldAtom.vars, AzFieldAtom.toFieldAtom]
    convert (toMvPoly_vars a.poly).symm
  | not _ ih =>
    simp only [azFreeVars, azFormulaToFieldFormula, mapAtom, freeVars, ih]
  | and _ _ ih₁ ih₂ =>
    simp only [azFreeVars, azFormulaToFieldFormula, mapAtom, freeVars, ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp only [azFreeVars, azFormulaToFieldFormula, mapAtom, freeVars, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ =>
    simp only [azFreeVars, azFormulaToFieldFormula, mapAtom, freeVars, ih₁, ih₂]
  | exists_ _ _ ih =>
    simp only [azFreeVars, azFormulaToFieldFormula, mapAtom, freeVars, ih]
  | forall_ _ _ ih =>
    simp only [azFreeVars, azFormulaToFieldFormula, mapAtom, freeVars, ih]

/-! ### Realization -/

/-- The `azRealization` is definitionally equal to the realization of the
    converted formula — this is `rfl` by definition. -/
theorem azRealization_eq_realization {C : Type*} [Field C] [Algebra D C]
    (Φ : Formula σ (AzFieldAtom σ D ord)) :
    azRealization (C := C) Φ = (azFormulaToFieldFormula Φ).realization := rfl

end Azurite
