import Azurite.BasuPollackRoy.Chapter2.Section2_3.BasicSemialgebraicSets
import Azurite.BasuPollackRoy.Chapter2.Section2_3.OrderedFieldFormula

/-!
# BPR Section 2.3 — Semialgebraic ↔ QF-Realizable

A subset of `R^k` is semialgebraic iff it is the realization of a
quantifier-free formula over the language of ordered fields
(`OrderedFieldAtom`). This is the real-closed analogue of
`constructible_iff_qfRealizable` from
`Azurite/BasuPollackRoy/Chapter1/Section1_1/ConstructibleQF.lean`.

The backward direction (QF realization is semialgebraic) inducts on the
formula; each atomic ordered-field comparison (`= 0`, `≠ 0`, `< 0`,
`> 0`, `≤ 0`, `≥ 0`) lands in the corresponding
`IsSemialgebraicSet`-lemma from `SemialgebraicSets.lean`, and the
boolean connectives reduce to the closure properties.

The forward direction (every semialgebraic set is a QF realization)
inducts on `IsSemialgebraicSet`: an algebraic set arising as
`Zer poly_set` is the realization of a conjunction of equality atoms
(helper `conjEqZeroO`); a positivity locus `{P > 0}` is `gtZeroO P`;
complement and intersection lift to `Formula.not` and `Formula.and`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]

/-- Conjunction of `eqZeroO` atoms from a list of polynomials. -/
noncomputable def conjEqZeroO :
    List (MvPolynomial σ D) → Formula σ (OrderedFieldAtom σ D)
  | [] => eqZeroO 0
  | [P] => eqZeroO P
  | P :: Ps => .and (eqZeroO P) (conjEqZeroO Ps)

theorem conjEqZeroO_isQF :
    ∀ (L : List (MvPolynomial σ D)),
    (conjEqZeroO L).IsQuantifierFree
  | [] => trivial
  | [_] => trivial
  | _ :: _ :: Ps =>
    ⟨trivial, conjEqZeroO_isQF (_ :: Ps)⟩

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R]

theorem conjEqZeroO_realization [DecidableEq σ] :
    ∀ (L : List (MvPolynomial σ D)),
    (conjEqZeroO L).realization (C := R) =
      { y | ∀ P ∈ L, MvPolynomial.aeval y P = 0}
  | [] => by
    ext y; simp [conjEqZeroO]
  | [P] => by
    ext y; simp [conjEqZeroO]
  | P :: Q :: Ps => by
    ext y
    simp only [conjEqZeroO, realization, Set.mem_inter_iff,
      Set.mem_setOf_eq, List.mem_cons]
    rw [show (conjEqZeroO (Q :: Ps)).realization (C := R) =
      { y | ∀ P ∈ (Q :: Ps), MvPolynomial.aeval y P = 0}
      from conjEqZeroO_realization (Q :: Ps)]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hP, hrest⟩ R hR
      rcases hR with rfl | hR
      · exact hP
      · exact hrest R (List.mem_cons.mpr hR)
    · intro h
      exact ⟨h P (Or.inl rfl),
        fun R hR => h R (Or.inr (List.mem_cons.mp hR))⟩

end Formula

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

open Formula in
/-- Backward: a quantifier-free formula's realization is semialgebraic. -/
theorem qfRealizable_isSemialgebraic
    {Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)}
    (hqf : Φ.IsQuantifierFree) :
    IsSemialgebraicSet (Φ.realization (C := R)) := by
  induction Φ with
  | atom a =>
    obtain ⟨P, rel⟩ := a
    cases rel
    · exact IsSemialgebraicSet.eqZero P
    · exact IsSemialgebraicSet.neZero P
    · exact IsSemialgebraicSet.ltZero P
    · exact IsSemialgebraicSet.gtZero P
    · exact IsSemialgebraicSet.leZero P
    · exact IsSemialgebraicSet.geZero P
  | not _ ih => exact (ih hqf).compl
  | and _ _ ih₁ ih₂ => exact (ih₁ hqf.1).inter (ih₂ hqf.2)
  | or _ _ ih₁ ih₂ => exact (ih₁ hqf.1).union (ih₂ hqf.2)
  | implies _ _ ih₁ ih₂ =>
    exact ((ih₁ hqf.1).compl).union (ih₂ hqf.2)
  | exists_ _ _ _ => exact absurd hqf id
  | forall_ _ _ _ => exact absurd hqf id

open Formula in
/-- Forward: every semialgebraic set is the realization of a
quantifier-free formula. -/
theorem semialgebraic_isQFRealizable
    (V : Set (Fin k → R)) (hV : IsSemialgebraicSet V) :
    ∃ Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R),
      Φ.IsQuantifierFree ∧ V = Φ.realization (C := R) := by
  induction hV with
  | algebraic hA =>
    obtain ⟨poly_set, rfl⟩ := hA
    refine ⟨conjEqZeroO poly_set.toList, conjEqZeroO_isQF _, ?_⟩
    rw [conjEqZeroO_realization]
    ext y; simp [Zer]
  | pos_locus P =>
    exact ⟨gtZeroO P, trivial, rfl⟩
  | compl _ ih =>
    obtain ⟨Φ, hqf, rfl⟩ := ih
    exact ⟨.not Φ, hqf, rfl⟩
  | inter _ _ ih₁ ih₂ =>
    obtain ⟨Φ₁, hqf₁, rfl⟩ := ih₁
    obtain ⟨Φ₂, hqf₂, rfl⟩ := ih₂
    exact ⟨.and Φ₁ Φ₂, ⟨hqf₁, hqf₂⟩, rfl⟩

/-- A subset of `R^k` is semialgebraic iff it is the realization of a
quantifier-free formula over ordered field atoms. -/
theorem semialgebraic_iff_qfRealizable
    (V : Set (Fin k → R)) :
    IsSemialgebraicSet V ↔
    ∃ Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R),
      Φ.IsQuantifierFree ∧ V = Φ.realization (C := R) :=
  ⟨semialgebraic_isQFRealizable V,
   fun ⟨_, hqf, hV⟩ => hV ▸ qfRealizable_isSemialgebraic hqf⟩

end Azurite.BPR
