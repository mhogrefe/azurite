/-
  Proof that `elimTrivialAtoms` preserves the az-realization.
-/
import Azurite.AzFormula.Equiv.DegFormula

namespace Azurite

open AzMvPolynomial BPR

variable {k : ℕ} {D : Type*} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}
variable {C : Type*} [Field C] [Algebra D C]

/-! ### Additional azRealization simp lemmas -/

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_not
    (Φ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (Formula.not Φ) (C := C) =
      (azRealization Φ)ᶜ := rfl

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_implies
    (Φ₁ Φ₂ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (Formula.implies Φ₁ Φ₂) (C := C) =
      (azRealization Φ₁)ᶜ ∪ azRealization Φ₂ := rfl

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_exists_
    (x : Fin k) (Φ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (Formula.exists_ x Φ) (C := C) =
      { y | ∃ c, Function.update y x c ∈ azRealization Φ } := rfl

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_forall_
    (x : Fin k) (Φ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (Formula.forall_ x Φ) (C := C) =
      { y | ∀ c, Function.update y x c ∈ azRealization Φ } := rfl

/-! ### elimTrivialAtoms preserves realization -/

omit [IsDomain D] in
private theorem isAzTrue_azRealization
    (Φ : Formula (Fin k) (AzFieldAtom k D ord))
    (h : isAzTrue Φ = true) : azRealization Φ (C := C) = Set.univ := by
  match Φ with
  | .atom ⟨_, true⟩ =>
    simp only [isAzTrue, Bool.true_and, beq_iff_eq] at h; subst h
    exact azRealization_azTrueFormula
  | .atom ⟨_, false⟩ | .not _ | .and _ _ | .or _ _ | .implies _ _
  | .exists_ _ _ | .forall_ _ _ => simp [isAzTrue] at h

omit [IsDomain D] in
private theorem isAzFalse_azRealization
    (Φ : Formula (Fin k) (AzFieldAtom k D ord))
    (h : isAzFalse Φ = true) : azRealization Φ (C := C) = ∅ := by
  match Φ with
  | .atom ⟨_, false⟩ =>
    simp only [isAzFalse, Bool.not_false, Bool.true_and, beq_iff_eq] at h; subst h
    exact azRealization_azFalseFormula
  | .atom ⟨_, true⟩ | .not _ | .and _ _ | .or _ _ | .implies _ _
  | .exists_ _ _ | .forall_ _ _ => simp [isAzFalse] at h

omit [IsDomain D] in
/-- Eliminating trivially true/false atoms preserves the az-realization. -/
theorem azRealization_elimTrivialAtoms
    (Φ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (elimTrivialAtoms Φ) (C := C) = azRealization Φ := by
  induction Φ with
  | atom _ => rfl
  | not Φ ih =>
    simp only [elimTrivialAtoms]
    split
    next h =>
      have := isAzTrue_azRealization (C := C) _ h
      rw [azRealization_azFalseFormula, azRealization_not, ← ih, this, Set.compl_univ]
    next _ =>
      split
      next h =>
        have := isAzFalse_azRealization (C := C) _ h
        rw [azRealization_azTrueFormula, azRealization_not, ← ih, this, Set.compl_empty]
      next _ =>
        simp only [azRealization_not, ih]
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [elimTrivialAtoms]
    split
    next h =>
      have := isAzTrue_azRealization (C := C) _ h
      rw [ih₂, azRealization_and, ← ih₁, this, Set.univ_inter]
    next _ =>
      split
      next h =>
        have := isAzTrue_azRealization (C := C) _ h
        rw [ih₁, azRealization_and, ← ih₂, this, Set.inter_univ]
      next _ =>
        split
        next h =>
          simp only [Bool.or_eq_true] at h
          rw [azRealization_azFalseFormula, azRealization_and]
          rcases h with h | h
          · rw [← ih₁, isAzFalse_azRealization _ h, Set.empty_inter]
          · rw [← ih₂, isAzFalse_azRealization _ h, Set.inter_empty]
        next _ =>
          simp only [azRealization_and, ih₁, ih₂]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [elimTrivialAtoms]
    split
    next h =>
      have := isAzFalse_azRealization (C := C) _ h
      rw [ih₂, azRealization_or, ← ih₁, this, Set.empty_union]
    next _ =>
      split
      next h =>
        have := isAzFalse_azRealization (C := C) _ h
        rw [ih₁, azRealization_or, ← ih₂, this, Set.union_empty]
      next _ =>
        split
        next h =>
          simp only [Bool.or_eq_true] at h
          rw [azRealization_azTrueFormula, azRealization_or]
          rcases h with h | h
          · rw [← ih₁, isAzTrue_azRealization _ h, Set.univ_union]
          · rw [← ih₂, isAzTrue_azRealization _ h, Set.union_univ]
        next _ =>
          simp only [azRealization_or, ih₁, ih₂]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [elimTrivialAtoms]
    split
    next h =>
      have := isAzTrue_azRealization (C := C) _ h
      rw [ih₂, azRealization_implies, ← ih₁, this, Set.compl_univ, Set.empty_union]
    next _ =>
      split
      next h =>
        simp only [Bool.or_eq_true] at h
        rw [azRealization_azTrueFormula, azRealization_implies]
        rcases h with h | h
        · rw [← ih₁, isAzFalse_azRealization _ h, Set.compl_empty, Set.univ_union]
        · rw [← ih₂, isAzTrue_azRealization _ h, Set.union_univ]
      next _ =>
        simp only [azRealization_implies, ih₁, ih₂]
  | exists_ x Φ ih =>
    simp only [elimTrivialAtoms, azRealization_exists_, ih]
  | forall_ x Φ ih =>
    simp only [elimTrivialAtoms, azRealization_forall_, ih]

end Azurite
