import Azurite.BasuPollackRoy.Chapter2.Section2_1
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_d_a
import Mathlib.Order.Zorn
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# BPR Theorem 2.31: Algebraically closed fields contain real closed subfields

**Theorem 2.31 (BPR).** If `C` is an algebraically closed field of characteristic zero,
there exists a real closed subfield `R ⊂ C` such that `R[i] = C`.

**Proof strategy.**
1. The set of semireal (`IsSemireal`) intermediate fields `ℚ ⊂ S ⊂ C` is nonempty
   (contains `⊥ ≅ ℚ`) and chain-complete (sums of squares are finite, so live in a
   single chain member).
2. By Zorn's lemma, choose a maximal semireal intermediate field `R`.
3. `R` has no nontrivial real algebraic extension: any such extension embeds into `C`
   (by `IsAlgClosed.lift`), giving a semireal intermediate field `≥ R` that must equal `R`
   by maximality.
4. By Theorem 2.11 (d⇒a), `R` is real closed.
-/

namespace Azurite.BPR.Theorem2_31

open Polynomial IntermediateField

/-! ### Transferring IsSumSq along ring homs -/

/-- Sums of squares are preserved by ring homomorphisms. -/
private lemma isSumSq_map {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {x : R} (h : IsSumSq x) : IsSumSq (f x) := by
  induction h with
  | zero => exact map_zero f ▸ .zero
  | sq_add a _ ih =>
    rw [map_add, map_mul]
    exact .sq_add (f a) ih

/-! ### Step 1: The set of semireal intermediate fields is nonempty and chain-complete -/

section ChainComplete

variable (C : Type*) [Field C] [CharZero C]

/-- `⊥` is semireal: it is isomorphic to `ℚ`, which is semireal. -/
private lemma bot_isSemireal : IsSemireal ↥(⊥ : IntermediateField ℚ C) := by
  apply IsSemireal.of_not_isSumSq_neg_one
  intro h
  have h' := isSumSq_map (botEquiv ℚ C).toAlgHom.toRingHom h
  simp at h'
  exact IsSemireal.not_isSumSq_neg_one ℚ h'

/-- The supremum of a chain of semireal intermediate fields is semireal.

    Key idea: `IsSumSq (-1)` involves finitely many elements; in a directed union,
    finitely many elements come from a single member of the chain. -/
private lemma sSup_isSemireal_of_chain
    {c : Set (IntermediateField ℚ C)} (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) (hsemi : ∀ S ∈ c, IsSemireal ↥S) :
    IsSemireal ↥(sSup c) := by
  apply IsSemireal.of_not_isSumSq_neg_one
  intro h
  have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
  -- Elements of sSup c lie in some chain member (directed union)
  have hmem : ∀ (x : C), x ∈ (sSup c : IntermediateField ℚ C) → ∃ S ∈ c, x ∈ S := by
    intro x hx
    have hx' : x ∈ (sSup c).toSubfield := hx
    rw [sSup_toSubfield c hne] at hx'
    have hne' : (IntermediateField.toSubfield '' c).Nonempty := hne.image _
    have hdir' : DirectedOn (· ≤ ·) (IntermediateField.toSubfield '' c) := by
      rintro _ ⟨Sa, hSa, rfl⟩ _ ⟨Sb, hSb, rfl⟩
      obtain ⟨Sc, hSc, haSc, hbSc⟩ := hdir Sa hSa Sb hSb
      exact ⟨Sc.toSubfield, ⟨Sc, hSc, rfl⟩, haSc, hbSc⟩
    obtain ⟨s, ⟨S, hS, rfl⟩, hxs⟩ := (Subfield.mem_sSup_of_directedOn hne' hdir').mp hx'
    exact ⟨S, hS, hxs⟩
  -- By induction on IsSumSq, find a single chain member containing all squares
  suffices ∀ (x : ↥(sSup c)), IsSumSq x →
      ∃ S ∈ c, ∃ y : ↥S, (y : C) = (x : C) ∧ IsSumSq y by
    obtain ⟨S, hS, y, hy, hsy⟩ := this _ h
    have : y = -1 := Subtype.val_injective (by simp [hy])
    exact absurd (by rwa [this] at hsy) (hsemi S hS).not_isSumSq_neg_one
  intro x hx
  induction hx with
  | zero =>
    obtain ⟨S, hS⟩ := hne
    exact ⟨S, hS, 0, by simp, .zero⟩
  | sq_add a _ ih =>
    obtain ⟨S₁, hS₁, y₁, hy₁, hsy₁⟩ := ih
    obtain ⟨S₂, hS₂, ha_S₂⟩ := hmem a.val a.2
    obtain ⟨S₃, hS₃, h₁₃, h₂₃⟩ := hdir S₁ hS₁ S₂ hS₂
    refine ⟨S₃, hS₃,
      ⟨a.val, h₂₃ ha_S₂⟩ * ⟨a.val, h₂₃ ha_S₂⟩ + inclusion h₁₃ y₁, ?_, ?_⟩
    · simp [coe_inclusion, hy₁]
    · exact .sq_add _ (isSumSq_map (inclusion h₁₃).toRingHom hsy₁)

end ChainComplete

/-! ### Step 2: Zorn's lemma — maximal semireal intermediate field -/

section Zorn

variable (C : Type*) [Field C] [IsAlgClosed C] [CharZero C]

omit [IsAlgClosed C] in
/-- There exists a maximal semireal intermediate field of `C` over `ℚ`. -/
private lemma exists_maximal_semireal :
    ∃ R : IntermediateField ℚ C,
      IsSemireal ↥R ∧ ∀ S : IntermediateField ℚ C, IsSemireal ↥S → R ≤ S → S = R := by
  have ⟨R, ⟨hR_semi, hR_max⟩⟩ := zorn_le₀
    {S : IntermediateField ℚ C | IsSemireal ↥S}
    (fun c hc_sub hc_chain => by
      rcases c.eq_empty_or_nonempty with rfl | hne
      · exact ⟨⊥, bot_isSemireal C, fun _ h => h.elim⟩
      · exact ⟨sSup c, sSup_isSemireal_of_chain C hc_chain hne (fun S hS => hc_sub hS),
          fun S hS => le_sSup hS⟩)
  exact ⟨R, hR_semi, fun S hS hle => le_antisymm (hR_max hS hle) hle⟩

end Zorn

/-! ### Step 3: Maximality implies HasNoNontrivialRealAlgebraicExtension -/

/-- The maximal semireal intermediate field has no nontrivial real algebraic extension.

    Given a real algebraic extension `F₁` of `R`, use `IsAlgClosed.lift` to embed
    `F₁` into `C`. The image is a semireal intermediate field containing `R`.
    By maximality, the image equals `R`, so `algebraMap R F₁` is surjective. -/
private lemma maximal_hasNoNontrivialRealAlgebraicExtension
    (C : Type*) [Field C] [IsAlgClosed C] [CharZero C]
    (R : IntermediateField ℚ C) (hR : IsSemireal ↥R)
    (hmax : ∀ S : IntermediateField ℚ C, IsSemireal ↥S → R ≤ S → S = R) :
    Azurite.BPR.HasNoNontrivialRealAlgebraicExtension ↥R := by
  constructor
  · exact hR
  · intro F₁ _ _ halg hreal x
    -- Embed F₁ into C via IsAlgClosed.lift
    letI : Algebra ℚ F₁ := (algebraMap ↥R F₁).comp (algebraMap ℚ ↥R) |>.toAlgebra
    haveI : IsScalarTower ℚ ↥R F₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let f : F₁ →ₐ[↥R] C := IsAlgClosed.lift
    -- The field range, restricted to ℚ-scalars, is an IntermediateField ℚ C
    let S : IntermediateField ℚ C := f.fieldRange.restrictScalars ℚ
    -- S contains R
    have hRS : R ≤ S := by
      intro y hy
      show y ∈ f.fieldRange
      exact AlgHom.mem_fieldRange.mpr ⟨algebraMap ↥R F₁ ⟨y, hy⟩, f.commutes ⟨y, hy⟩⟩
    -- S is semireal: transfer IsSumSq back to F₁ via preimages under f
    have hS_semi : IsSemireal ↥S := by
      apply IsSemireal.of_not_isSumSq_neg_one
      intro h
      -- By induction, find preimage in F₁
      suffices ∀ (s : ↥S), IsSumSq s → ∃ t : F₁, f t = s.val ∧ IsSumSq t by
        obtain ⟨t, ht, hst⟩ := this _ h
        have : t = -1 := f.injective (by simp [ht])
        exact absurd (by rwa [this] at hst) hreal.not_isSumSq_neg_one
      intro s hs
      induction hs with
      | zero => exact ⟨0, by simp, .zero⟩
      | sq_add a _ ih =>
        obtain ⟨t₁, ht₁, hst₁⟩ := ih
        have ha_mem : a.val ∈ f.fieldRange := a.2
        obtain ⟨b, hb⟩ := AlgHom.mem_fieldRange.mp ha_mem
        exact ⟨b * b + t₁, by simp [map_add, map_mul, hb, ht₁], .sq_add b hst₁⟩
    -- By maximality, S = R
    have hSR := hmax S hS_semi hRS
    -- f x ∈ R
    have hfx_mem : (f x : C) ∈ R := by
      have : (f x : C) ∈ S := AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩
      convert this using 1
      exact hSR.symm
    exact ⟨⟨f x, hfx_mem⟩, f.injective (by simp [f.commutes])⟩

/-! ### Conclusion -/

/-- **Theorem 2.31 (BPR).** Every algebraically closed field of characteristic zero
    contains a real closed subfield (as an intermediate field over `ℚ`). -/
theorem theorem_2_31 (C : Type*) [Field C] [IsAlgClosed C] [CharZero C] :
    ∃ R : IntermediateField ℚ C, IsRealClosed ↥R := by
  obtain ⟨R, hR, hmax⟩ := exists_maximal_semireal C
  exact ⟨R, Azurite.BPR.Theorem2_11.theorem_2_11_d_a
    (maximal_hasNoNontrivialRealAlgebraicExtension C R hR hmax)⟩

end Azurite.BPR.Theorem2_31
