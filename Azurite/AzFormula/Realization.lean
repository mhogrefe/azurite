/-
  Conversions between AzFieldAtom / FieldAtom, and between their Formula types.
  Also defines a noncomputable realization for Formula (AzFieldAtom).
-/
import Azurite.AzFormula.Atom
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleQF
import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleSets
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Definitions
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Example1_2
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_1
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_2
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_3
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_4
import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Notation1_1
import Azurite.BasuPollackRoy.Chapter1.Section1_1.PrenexNormalForm
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization
import Azurite.BasuPollackRoy.Chapter1.Section1_1.RealizationInvariance
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Sentences

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR

/-! ### Atom conversions -/

variable {n : ℕ} {D : Type*} [CommRing D] {ord : MonomialOrder}

/-- Convert `AzFieldAtom` to `FieldAtom` by sending the polynomial through `toMvPoly`. -/
noncomputable def AzFieldAtom.toFieldAtom (a : AzFieldAtom n D ord) :
    FieldAtom (Fin n) D :=
  ⟨a.poly.toMvPoly, a.isEq⟩

/-- Convert `FieldAtom` to `AzFieldAtom` by sending the polynomial through `ofMvPoly`. -/
noncomputable def azFieldAtomOfFieldAtom (a : FieldAtom (Fin n) D) :
    AzFieldAtom n D ord :=
  ⟨AzMvPolynomial.ofMvPoly a.poly, a.isEq⟩

/-- Round-trip: converting an `AzFieldAtom` to `FieldAtom` and back is the identity. -/
theorem azFieldAtomOfFieldAtom_toFieldAtom (a : AzFieldAtom n D ord) :
    azFieldAtomOfFieldAtom (ord := ord) a.toFieldAtom = a := by
  simp only [AzFieldAtom.toFieldAtom, azFieldAtomOfFieldAtom, ofMvPoly_toMvPoly]

/-- Round-trip: converting a `FieldAtom` to `AzFieldAtom` and back is the identity. -/
theorem toFieldAtom_azFieldAtomOfFieldAtom (a : FieldAtom (Fin n) D) :
    (azFieldAtomOfFieldAtom (ord := ord) a).toFieldAtom = a := by
  simp only [azFieldAtomOfFieldAtom, AzFieldAtom.toFieldAtom, toMvPoly_ofMvPoly]

/-! ### Formula conversions -/

/-- Convert a `Formula (Fin n) (AzFieldAtom n D ord)` to a `Formula (Fin n) (FieldAtom (Fin n) D)`. -/
noncomputable def azFormulaToFieldFormula
    (Φ : Formula (Fin n) (AzFieldAtom n D ord)) :
    Formula (Fin n) (FieldAtom (Fin n) D) :=
  Φ.mapAtom AzFieldAtom.toFieldAtom

/-- Convert a `Formula (Fin n) (FieldAtom (Fin n) D)` to a `Formula (Fin n) (AzFieldAtom n D ord)`. -/
noncomputable def fieldFormulaToAzFormula
    (Φ : Formula (Fin n) (FieldAtom (Fin n) D)) :
    Formula (Fin n) (AzFieldAtom n D ord) :=
  Φ.mapAtom azFieldAtomOfFieldAtom

/-! ### Realization for AzFieldAtom formulas -/

variable {C : Type*} [Field C] [Algebra D C]

/-- The C-realization of an `AzFieldAtom` formula, defined by converting to the
    `FieldAtom` form and using the standard realization from BPR §1.1. -/
noncomputable def azRealization
    (Φ : Formula (Fin n) (AzFieldAtom n D ord)) : Set (Fin n → C) :=
  (azFormulaToFieldFormula Φ).realization

end Azurite
