/-
  Conversions between AzFieldAtom / FieldAtom, and between their Formula types.
  Also defines a noncomputable realization for Formula (AzFieldAtom).
-/
import Azurite.AzFormula.Atom
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.BasuPollackRoy.Chapter1.Section1_1

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR

/-! ### Atom conversions -/

variable {σ : Type*} {n : ℕ} [LinearOrder σ] [Var σ n] [DecidableEq σ]
    {D : Type*} [CommRing D] {ord : MonomialOrder}

/-- Convert `AzFieldAtom` to `FieldAtom` by sending the polynomial through `toMvPoly`. -/
noncomputable def AzFieldAtom.toFieldAtom (a : AzFieldAtom σ D ord) : FieldAtom σ D :=
  ⟨a.poly.toMvPoly, a.isEq⟩

/-- Convert `FieldAtom` to `AzFieldAtom` by sending the polynomial through `ofMvPoly`. -/
noncomputable def azFieldAtomOfFieldAtom (a : FieldAtom σ D) : AzFieldAtom σ D ord :=
  ⟨AzMvPolynomial.ofMvPoly a.poly, a.isEq⟩

/-- Round-trip: converting an `AzFieldAtom` to `FieldAtom` and back is the identity. -/
theorem azFieldAtomOfFieldAtom_toFieldAtom (a : AzFieldAtom σ D ord) :
    azFieldAtomOfFieldAtom (ord := ord) a.toFieldAtom = a := by
  simp only [AzFieldAtom.toFieldAtom, azFieldAtomOfFieldAtom, ofMvPoly_toMvPoly]

/-- Round-trip: converting a `FieldAtom` to `AzFieldAtom` and back is the identity. -/
theorem toFieldAtom_azFieldAtomOfFieldAtom (a : FieldAtom σ D) :
    (azFieldAtomOfFieldAtom (ord := ord) a).toFieldAtom = a := by
  simp only [azFieldAtomOfFieldAtom, AzFieldAtom.toFieldAtom, toMvPoly_ofMvPoly]

/-! ### Formula conversions -/

/-- Convert a `Formula σ (AzFieldAtom σ D ord)` to a `Formula σ (FieldAtom σ D)`. -/
noncomputable def azFormulaToFieldFormula
    (Φ : Formula σ (AzFieldAtom σ D ord)) : Formula σ (FieldAtom σ D) :=
  Φ.mapAtom AzFieldAtom.toFieldAtom

/-- Convert a `Formula σ (FieldAtom σ D)` to a `Formula σ (AzFieldAtom σ D ord)`. -/
noncomputable def fieldFormulaToAzFormula
    (Φ : Formula σ (FieldAtom σ D)) : Formula σ (AzFieldAtom σ D ord) :=
  Φ.mapAtom azFieldAtomOfFieldAtom

/-! ### Realization for AzFieldAtom formulas -/

variable {C : Type*} [Field C] [Algebra D C]

/-- The C-realization of an `AzFieldAtom` formula, defined by converting to the
    `FieldAtom` form and using the standard realization from BPR §1.1. -/
noncomputable def azRealization
    (Φ : Formula σ (AzFieldAtom σ D ord)) : Set (σ → C) :=
  (azFormulaToFieldFormula Φ).realization

end Azurite
