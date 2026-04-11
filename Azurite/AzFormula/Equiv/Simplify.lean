/-
  Proof that each simplification pass preserves realizability.
-/
import Azurite.AzFormula.Equiv.FreeVars

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial BPR Formula

variable {σ : Type*} [DecidableEq σ] {D : Type*} [CommRing D]
    {C : Type*} [Field C] [Algebra D C]

/-! ### elimDoubleNeg preserves realization -/

/-- Double negation elimination preserves the C-realization. -/
theorem elimDoubleNeg_realization
    (Φ : Formula σ (FieldAtom σ D)) :
    (elimDoubleNeg Φ).realization (C := C) = Φ.realization := by
  induction Φ with
  | atom _ => rfl
  | not Ψ ih =>
    simp only [elimDoubleNeg]
    -- The simplified Ψ either starts with .not or doesn't
    generalize hΨ' : elimDoubleNeg Ψ = Ψ'
    -- ih : Ψ'.realization = Ψ.realization (after hΨ')
    have ih' : Ψ'.realization (C := C) = Ψ.realization := hΨ' ▸ ih
    match Ψ' with
    | .not Ψ'' =>
      -- Goal: Ψ''.realization = (Formula.not Ψ).realization
      simp only [realization] at ih' ⊢
      -- ih' : Ψ''.realization^c = Ψ.realization
      rw [← ih', compl_compl (α := Set (σ → C))]
    | .atom _       => simp only [realization]; exact congrArg _ ih'
    | .and _ _      => simp only [realization]; exact congrArg _ ih'
    | .or _ _       => simp only [realization]; exact congrArg _ ih'
    | .implies _ _ => simp only [realization]; exact congrArg _ ih'
    | .exists_ _ _ => simp only [realization]; exact congrArg _ ih'
    | .forall_ _ _ => simp only [realization]; exact congrArg _ ih'
  | and _ _ ih₁ ih₂ =>
    simp only [elimDoubleNeg, realization, ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp only [elimDoubleNeg, realization, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ =>
    simp only [elimDoubleNeg, realization, ih₁, ih₂]
  | exists_ _ _ ih =>
    simp only [elimDoubleNeg, realization, ih]
  | forall_ _ _ ih =>
    simp only [elimDoubleNeg, realization, ih]

/-! ### elimVacuousQuantifiers preserves realization -/

/-- Vacuous quantifier removal preserves the C-realization.
    Uses `realization_invariant_update` from BPR §1.1. -/
theorem elimVacuousQuantifiers_realization
    (Φ : Formula σ (FieldAtom σ D)) :
    (elimVacuousQuantifiers Φ).realization (C := C) = Φ.realization := by
  induction Φ with
  | atom _ => rfl
  | not _ ih =>
    simp only [elimVacuousQuantifiers, realization, ih]
  | and _ _ ih₁ ih₂ =>
    simp only [elimVacuousQuantifiers, realization, ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp only [elimVacuousQuantifiers, realization, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ =>
    simp only [elimVacuousQuantifiers, realization, ih₁, ih₂]
  | exists_ x Ψ ih =>
    simp only [elimVacuousQuantifiers]
    split
    · simp only [realization, ih]
    · -- x ∉ freeVarsOf (elimVacuousQuantifiers Ψ)
      rename_i hx
      have hx' : x ∉ (elimVacuousQuantifiers Ψ).freeVars := by
        rwa [freeVarsOf_eq_freeVars_fieldAtom] at hx
      -- Goal: (elimVacuousQuantifiers Ψ).realization = (∃x, Ψ).realization
      -- Strategy: show both are equal to (elimVacuousQuantifiers Ψ).realization
      -- since the quantifier is vacuous for the simplified formula
      ext y; simp only [realization, Set.mem_setOf_eq]
      constructor
      · -- (elimVacuousQuantifiers Ψ).realization → (∃x, Ψ).realization
        intro hy
        exact ⟨y x, by
          rw [Function.update_eq_self]
          rw [← ih]; exact hy⟩
      · -- (∃x, Ψ).realization → (elimVacuousQuantifiers Ψ).realization
        rintro ⟨c, hc⟩
        have : Function.update y x c ∈ (elimVacuousQuantifiers Ψ).realization := by
          rw [ih]; exact hc
        exact (realization_invariant_update _ x hx' y c).mpr this
  | forall_ x Ψ ih =>
    simp only [elimVacuousQuantifiers]
    split
    · simp only [realization, ih]
    · rename_i hx
      have hx' : x ∉ (elimVacuousQuantifiers Ψ).freeVars := by
        rwa [freeVarsOf_eq_freeVars_fieldAtom] at hx
      ext y; simp only [realization, Set.mem_setOf_eq]
      constructor
      · intro hy c
        have : y ∈ (elimVacuousQuantifiers Ψ).realization := hy
        exact ih ▸ (realization_invariant_update _ x hx' y c).mp this
      · intro hy
        have : Function.update y x (y x) ∈ (elimVacuousQuantifiers Ψ).realization := by
          rw [ih]; exact hy (y x)
        rwa [Function.update_eq_self] at this

/-! ### simplify preserves realization -/

/-- The combined simplification (double negation + vacuous quantifiers)
    preserves the C-realization. -/
theorem simplify_realization
    (Φ : Formula σ (FieldAtom σ D)) :
    (simplify Φ).realization (C := C) = Φ.realization := by
  simp only [simplify, elimVacuousQuantifiers_realization, elimDoubleNeg_realization]

end Azurite
