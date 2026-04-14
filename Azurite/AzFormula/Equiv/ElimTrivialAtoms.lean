/-
  Proof that `elimTrivialAtoms` preserves the az-realization.
-/
import Azurite.AzFormula.Equiv.DegFormula
import Azurite.AzFormula.Equiv.FreeVars

namespace Azurite

open AzMvPolynomial BPR Formula

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
/-- Eliminating trivially true/false atoms preserves the az-realization. -/
theorem azRealization_elimTrivialAtoms [FaithfulSMul D C]
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

/-! ### elimDoubleNeg preserves azRealization -/

omit [IsDomain D] [DecidableEq D] in
theorem azRealization_elimDoubleNeg
    (Φ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (elimDoubleNeg Φ) (C := C) = azRealization Φ := by
  induction Φ with
  | atom _ => rfl
  | not Ψ ih =>
    simp only [elimDoubleNeg]
    generalize hΨ' : elimDoubleNeg Ψ = Ψ'
    have ih' : azRealization Ψ' (C := C) = azRealization Ψ := hΨ' ▸ ih
    match Ψ' with
    | .not Ψ'' =>
      simp only [azRealization_not] at ih' ⊢
      rw [← ih', compl_compl]
    | .atom _ | .and _ _ | .or _ _ | .implies _ _ | .exists_ _ _ | .forall_ _ _ =>
      simp only [azRealization_not]; exact congrArg _ ih'
  | and _ _ ih₁ ih₂ => simp only [elimDoubleNeg, azRealization_and, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp only [elimDoubleNeg, azRealization_or, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ =>
    simp only [elimDoubleNeg, azRealization_implies, ih₁, ih₂]
  | exists_ _ _ ih => simp only [elimDoubleNeg, azRealization_exists_, ih]
  | forall_ _ _ ih => simp only [elimDoubleNeg, azRealization_forall_, ih]

/-! ### elimVacuousQuantifiers preserves azRealization -/

omit [IsDomain D] [DecidableEq D] in
theorem azRealization_elimVacuousQuantifiers
    (Φ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (elimVacuousQuantifiers Φ) (C := C) = azRealization Φ := by
  induction Φ with
  | atom _ => rfl
  | not _ ih => simp only [elimVacuousQuantifiers, azRealization_not, ih]
  | and _ _ ih₁ ih₂ =>
    simp only [elimVacuousQuantifiers, azRealization_and, ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp only [elimVacuousQuantifiers, azRealization_or, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ =>
    simp only [elimVacuousQuantifiers, azRealization_implies, ih₁, ih₂]
  | exists_ x Ψ ih =>
    simp only [elimVacuousQuantifiers]
    split
    · simp only [azRealization_exists_, ih]
    · rename_i hx
      have hx' : x ∉ (azFormulaToFieldFormula (elimVacuousQuantifiers Ψ)).freeVars := by
        rwa [← freeVarsOf_eq_freeVars_azFieldAtom]
      ext y; simp only [azRealization_exists_, Set.mem_setOf_eq]
      constructor
      · intro hy
        exact ⟨y x, by rw [Function.update_eq_self, ← ih]; exact hy⟩
      · rintro ⟨c, hc⟩
        have : Function.update y x c ∈ azRealization (elimVacuousQuantifiers Ψ) := ih ▸ hc
        exact (realization_invariant_update _ x hx' y c).mpr this
  | forall_ x Ψ ih =>
    simp only [elimVacuousQuantifiers]
    split
    · simp only [azRealization_forall_, ih]
    · rename_i hx
      have hx' : x ∉ (azFormulaToFieldFormula (elimVacuousQuantifiers Ψ)).freeVars := by
        rwa [← freeVarsOf_eq_freeVars_azFieldAtom]
      ext y; simp only [azRealization_forall_, Set.mem_setOf_eq]
      constructor
      · intro hy c
        exact ih ▸ (realization_invariant_update _ x hx' y c).mp hy
      · intro hy
        have : Function.update y x (y x) ∈ azRealization (elimVacuousQuantifiers Ψ) := by
          rw [ih]; exact hy (y x)
        rwa [Function.update_eq_self] at this

/-! ### azSimplify preserves azRealization -/

omit [IsDomain D] in
private theorem azRealization_azSimplifyNot [FaithfulSMul D C]
    (Φ' : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (azSimplifyNot Φ') (C := C) = (azRealization Φ')ᶜ := by
  simp only [azSimplifyNot]
  split
  · simp only [azRealization_not, compl_compl]
  all_goals (
    split
    next h =>
      rw [azRealization_azFalseFormula, isAzTrue_azRealization (C := C) _ h, Set.compl_univ]
    next _ =>
      split
      next h =>
        rw [azRealization_azTrueFormula, isAzFalse_azRealization (C := C) _ h, Set.compl_empty]
      next _ =>
        rfl)

/-! ### azSimplify produces simplified formulas -/

omit [IsDomain D] in
private theorem isAzSimplified_azSimplifyNot
    (Φ' : Formula (Fin k) (AzFieldAtom k D ord))
    (h : isAzSimplified Φ' = true) :
    isAzSimplified (azSimplifyNot Φ') = true := by
  match Φ' with
  | .not Ψ =>
    -- azSimplifyNot (.not Ψ) = Ψ; need isAzSimplified Ψ
    revert h; match Ψ with
    | .not _ => simp [isAzSimplified]
    | .atom _ => intro; rfl
    | .and _ _ | .or _ _ | .implies _ _ | .exists_ _ _ | .forall_ _ _ => exact id
  | .atom _ =>
    simp only [azSimplifyNot]
    split_ifs <;> first | rfl | simp_all [isAzSimplified]
  | .and _ _ | .or _ _ | .implies _ _ | .exists_ _ _ | .forall_ _ _ =>
    exact h

omit [IsDomain D] in
/-- `azSimplify` always produces a simplified formula. -/
theorem isAzSimplified_azSimplify
    (Φ : Formula (Fin k) (AzFieldAtom k D ord)) :
    isAzSimplified (azSimplify Φ) = true := by
  induction Φ with
  | atom _ => rfl
  | not Φ ih =>
    simp only [azSimplify]
    exact isAzSimplified_azSimplifyNot _ ih
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [azSimplify]
    split
    · exact ih₂
    · split
      · exact ih₁
      · split
        · rfl
        · simp_all [isAzSimplified]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [azSimplify]
    split
    · exact ih₂
    · split
      · exact ih₁
      · split
        · rfl
        · simp_all [isAzSimplified]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [azSimplify]
    split
    · exact ih₂
    · split
      · rfl
      · simp_all [isAzSimplified]
  | exists_ x Φ ih =>
    simp only [azSimplify]
    split
    · rename_i hx
      simp only [isAzSimplified, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hx, ih⟩
    · exact ih
  | forall_ x Φ ih =>
    simp only [azSimplify]
    split
    · rename_i hx
      simp only [isAzSimplified, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hx, ih⟩
    · exact ih

omit [IsDomain D] in
/-- The combined AzFieldAtom simplification preserves the az-realization. -/
theorem azRealization_azSimplify [FaithfulSMul D C]
    (Φ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (azSimplify Φ) (C := C) = azRealization Φ := by
  induction Φ with
  | atom _ => rfl
  | not Φ ih =>
    simp only [azSimplify, azRealization_azSimplifyNot, ih, azRealization_not]
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [azSimplify]
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
    simp only [azSimplify]
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
    simp only [azSimplify]
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
    simp only [azSimplify]
    split
    · simp only [azRealization_exists_, ih]
    · rename_i hx
      have hx' : x ∉ (azFormulaToFieldFormula (azSimplify Φ)).freeVars := by
        rwa [← freeVarsOf_eq_freeVars_azFieldAtom]
      ext y; simp only [azRealization_exists_, Set.mem_setOf_eq]
      constructor
      · intro hy
        exact ⟨y x, by rw [Function.update_eq_self, ← ih]; exact hy⟩
      · rintro ⟨c, hc⟩
        have : Function.update y x c ∈ azRealization (azSimplify Φ) := ih ▸ hc
        exact (realization_invariant_update _ x hx' y c).mpr this
  | forall_ x Φ ih =>
    simp only [azSimplify]
    split
    · simp only [azRealization_forall_, ih]
    · rename_i hx
      have hx' : x ∉ (azFormulaToFieldFormula (azSimplify Φ)).freeVars := by
        rwa [← freeVarsOf_eq_freeVars_azFieldAtom]
      ext y; simp only [azRealization_forall_, Set.mem_setOf_eq]
      constructor
      · intro hy c
        exact ih ▸ (realization_invariant_update _ x hx' y c).mp hy
      · intro hy
        have : Function.update y x (y x) ∈ azRealization (azSimplify Φ) := by
          rw [ih]; exact hy (y x)
        rwa [Function.update_eq_self] at this

end Azurite
