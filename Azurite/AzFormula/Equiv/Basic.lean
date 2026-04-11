/-
  Core equivalence proofs: mapAtom functor laws, formula conversion round-trips,
  and realization equivalence.
-/
import Azurite.AzFormula.Basic
import Azurite.AzFormula.Realization

namespace Azurite

open AzMvPolynomialNew MonicMonomialNew MonomialNew BPR Formula

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

/-! ### freeVarsOf and mapAtom -/

/-- `freeVarsOf` commutes with `mapAtom` when the atom mapping preserves variables. -/
theorem freeVarsOf_mapAtom [AtomVars α σ] [AtomVars β σ] [DecidableEq σ]
    (f : α → β) (hf : ∀ a, AtomVars.vars (f a) = AtomVars.vars a)
    (Φ : Formula σ α) :
    freeVarsOf (Φ.mapAtom f) = freeVarsOf Φ := by
  induction Φ with
  | atom a => simp [freeVarsOf, mapAtom, hf]
  | not _ ih => simp [freeVarsOf, mapAtom, ih]
  | and _ _ ih₁ ih₂ => simp [freeVarsOf, mapAtom, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [freeVarsOf, mapAtom, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ => simp [freeVarsOf, mapAtom, ih₁, ih₂]
  | exists_ _ _ ih => simp [freeVarsOf, mapAtom, ih]
  | forall_ _ _ ih => simp [freeVarsOf, mapAtom, ih]

/-! ### Formula conversion round-trips -/

variable {n : ℕ} {D : Type*} [CommRing D] {ord : MonomialOrder}

theorem fieldFormulaToAzFormula_azFormulaToFieldFormula
    (Φ : Formula (Fin n) (AzFieldAtom n D ord)) :
    fieldFormulaToAzFormula (azFormulaToFieldFormula Φ) = Φ := by
  simp only [fieldFormulaToAzFormula, azFormulaToFieldFormula, mapAtom_comp]
  show Φ.mapAtom (azFieldAtomOfFieldAtom ∘ AzFieldAtom.toFieldAtom) = Φ
  conv_rhs => rw [← mapAtom_id Φ]
  congr 1; funext a; exact azFieldAtomOfFieldAtom_toFieldAtom a

theorem azFormulaToFieldFormula_fieldFormulaToAzFormula
    (Φ : Formula (Fin n) (FieldAtom (Fin n) D)) :
    azFormulaToFieldFormula (fieldFormulaToAzFormula (ord := ord) Φ) = Φ := by
  simp only [azFormulaToFieldFormula, fieldFormulaToAzFormula, mapAtom_comp]
  show Φ.mapAtom (AzFieldAtom.toFieldAtom ∘ azFieldAtomOfFieldAtom) = Φ
  conv_rhs => rw [← mapAtom_id Φ]
  congr 1; funext a; exact toFieldAtom_azFieldAtomOfFieldAtom a

/-! ### Realization -/

/-- The `azRealization` is definitionally equal to the realization of the
    converted formula — this is `rfl` by definition. -/
theorem azRealization_eq_realization {C : Type*} [Field C] [Algebra D C]
    (Φ : Formula (Fin n) (AzFieldAtom n D ord)) :
    azRealization (C := C) Φ = (azFormulaToFieldFormula Φ).realization := rfl

end Azurite
