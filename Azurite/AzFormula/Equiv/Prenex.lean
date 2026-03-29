/-
  Generic correctness proofs for prenex conversion.

  Defines `AtomRealization` typeclass and `gRealization` for generic formula
  semantics, then proves that `eliminateImplies` and `toNNF` preserve realization.
-/
import Azurite.AzFormula.Prenex

namespace Azurite

open BPR Formula

/-! ### Generic formula semantics -/

/-- Typeclass for atom types that can be interpreted as sets of variable assignments.
    Includes a law for `AtomNeg`: negating an atom complements its interpretation. -/
class AtomRealization (α σ K : Type*) [AtomNeg α] where
  /-- Interpret an atom as a set of variable assignments. -/
  interpret : α → Set (σ → K)
  /-- Negating an atom complements its interpretation. -/
  neg_interpret : ∀ a : α, interpret (AtomNeg.neg a) = (interpret a)ᶜ

/-- Generic first-order realization of a formula.
    This is the standard Tarskian semantics: negation is complement,
    conjunction is intersection, etc. -/
noncomputable def gRealization {σ : Type*} [DecidableEq σ] {α K : Type*}
    [AtomNeg α] [AtomRealization α σ K] :
    Formula σ α → Set (σ → K)
  | .atom a        => AtomRealization.interpret a
  | .not Φ         => (gRealization Φ)ᶜ
  | .and Φ₁ Φ₂     => gRealization Φ₁ ∩ gRealization Φ₂
  | .or Φ₁ Φ₂      => gRealization Φ₁ ∪ gRealization Φ₂
  | .implies Φ₁ Φ₂ => (gRealization Φ₁)ᶜ ∪ gRealization Φ₂
  | .exists_ x Φ   => { y | ∃ c, Function.update y x c ∈ gRealization Φ }
  | .forall_ x Φ   => { y | ∀ c, Function.update y x c ∈ gRealization Φ }

variable {σ : Type*} [DecidableEq σ] {α : Type*} [AtomNeg α]
    {K : Type*} [AtomRealization α σ K]

/-! ### eliminateImplies preserves gRealization -/

/-- `eliminateImplies` preserves the generic realization. -/
theorem eliminateImplies_gRealization
    (Φ : Formula σ α) :
    gRealization (K := K) (Φ.eliminateImplies) = gRealization Φ := by
  induction Φ with
  | atom _ => rfl
  | not _ ih => simp only [eliminateImplies, gRealization, ih]
  | and _ _ ih₁ ih₂ => simp only [eliminateImplies, gRealization, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp only [eliminateImplies, gRealization, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ => simp only [eliminateImplies, gRealization, ih₁, ih₂]
  | exists_ _ _ ih => simp only [eliminateImplies, gRealization, ih]
  | forall_ _ _ ih => simp only [eliminateImplies, gRealization, ih]

/-! ### toNNF preserves gRealization -/

/-- Both `toNNFPos` and `toNNFNeg` preserve realization (proved together).
    Uses `AtomRealization.neg_interpret` for the atom negation case. -/
private theorem toNNF_gRealization_aux
    (Φ : Formula σ α) :
    gRealization (K := K) (toNNFPos Φ) = gRealization Φ ∧
    gRealization (K := K) (toNNFPos.toNNFNeg Φ) = (gRealization Φ)ᶜ := by
  induction Φ with
  | atom a =>
    refine ⟨rfl, ?_⟩
    simp only [toNNFPos.toNNFNeg, gRealization]
    exact AtomRealization.neg_interpret a
  | not Ψ ih =>
    refine ⟨?_, ?_⟩
    · simp only [toNNFPos, gRealization]
      exact ih.2
    · simp only [toNNFPos.toNNFNeg, gRealization, compl_compl (α := Set (σ → K))]
      exact ih.1
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    refine ⟨?_, ?_⟩
    · simp only [toNNFPos, gRealization, ih₁.1, ih₂.1]
    · simp only [toNNFPos.toNNFNeg, gRealization, ih₁.2, ih₂.2, Set.compl_inter]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    refine ⟨?_, ?_⟩
    · simp only [toNNFPos, gRealization, ih₁.1, ih₂.1]
    · simp only [toNNFPos.toNNFNeg, gRealization, ih₁.2, ih₂.2, Set.compl_union]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    refine ⟨?_, ?_⟩
    · simp only [toNNFPos, gRealization, ih₁.2, ih₂.1]
    · simp only [toNNFPos.toNNFNeg, gRealization, ih₁.1, ih₂.2]
      ext y; simp [Set.mem_compl_iff, Set.mem_inter_iff]
  | exists_ x Ψ ih =>
    refine ⟨?_, ?_⟩
    · simp only [toNNFPos, gRealization, ih.1]
    · simp only [toNNFPos.toNNFNeg, gRealization, ih.2]
      ext y; simp [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists]
  | forall_ x Ψ ih =>
    refine ⟨?_, ?_⟩
    · simp only [toNNFPos, gRealization, ih.1]
    · simp only [toNNFPos.toNNFNeg, gRealization, ih.2]
      ext y; simp [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]

/-- `toNNF` preserves the generic realization. -/
theorem toNNF_gRealization
    (Φ : Formula σ α) :
    gRealization (K := K) (toNNF Φ) = gRealization Φ :=
  (toNNF_gRealization_aux Φ).1

end Azurite
