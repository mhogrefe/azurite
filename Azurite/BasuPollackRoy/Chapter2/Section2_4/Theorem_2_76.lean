import Azurite.BasuPollackRoy.Chapter2.Section2_3.SemialgebraicQF
import Azurite.BasuPollackRoy.Chapter2.Section2_3.BasicSemialgebraicSetsOver
import Azurite.BasuPollackRoy.Chapter2.Section2_3.Theorem_2_62

/-! # BPR Theorem 2.76: Projection theorem for semialgebraic sets

**Theorem 2.76 (BPR).** The projection of a semialgebraic subset of `Rᵏ⁺¹` defined
over `D` to `Rᵏ` is a semialgebraic set defined over `D`.

## Structure of the formalization

This file sets up the **reduction** of Theorem 2.76 to a single kernel statement.
The reduction is purely formal:

* `semialgebraic_isQFRealizableOver` / `semialgebraic_iff_qfRealizableOver` — the
  over-`D` quantifier-free characterization of semialgebraic sets (the missing
  forward direction, mirroring the absolute `semialgebraic_isQFRealizable`);
* `Fin.init_image_eq_setOf_exists_snoc` — the projection is `{y | ∃ x, (y,x) ∈ V}`;
* `theorem_2_76_of_basicCellProjection` — Theorem 2.76 *given* the kernel that the
  projection of every **basic cell** `{(y,x) | P=0 ∧ ⋀ q∈𝒬, q>0}` over `D` is
  semialgebraic over `D`. The disjunctive normal form over `D`
  (`IsFinUnionOfBasicOver.of_isSemialgebraicSetOver`, in
  `Section2_3/BasicSemialgebraicSetsOver.lean`) decomposes the input into a finite
  union of cells; projection commutes with union.

The **kernel** — the projection of a basic cell — is the genuine content of the
projection theorem. Following BPR, it is proved by the parametrized
sign-determination of Lemmas 2.74 / 2.75 over `D[Y₁,…,Y_k]` (extending the
`P = 0` machinery of Theorem 2.62 / `fiberFormula_high` to sign conditions). That
kernel is the next milestone and is *not* yet formalized here.
-/

namespace Azurite.BPR

open Azurite.BPR.Formula MvPolynomial

/-- The projection (drop the last coordinate, `Fin.init`) of `V ⊆ Rᵏ⁺¹` is the set
of `y ∈ Rᵏ` admitting some `x` with `(y, x) ∈ V`. -/
theorem Fin.init_image_eq_setOf_exists_snoc {k : ℕ} {R : Type*} {V : Set (Fin (k+1) → R)} :
    Fin.init '' V = {y : Fin k → R | ∃ x : R, Fin.snoc y x ∈ V} := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z (Fin.last k), by rwa [Fin.snoc_init_self]⟩
  · rintro ⟨x, hx⟩
    exact ⟨Fin.snoc y x, hx, by funext i; simp [Fin.init, Fin.snoc_castSucc]⟩

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {D : Type*} [CommRing D] [Algebra D R]

/-- Over-`D` forward direction: every set semialgebraic over `D` is the realization
of a quantifier-free formula with `D`-coefficient atoms. (Over-`D` analogue of
`semialgebraic_isQFRealizable`; the induction over `IsSemialgebraicSetOver`
constructors mirrors the absolute proof.) -/
theorem semialgebraic_isQFRealizableOver
    (V : Set (Fin k → R)) (hV : IsSemialgebraicSetOver D V) :
    ∃ Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) D),
      Φ.IsQuantifierFree ∧ V = Φ.realization (C := R) := by
  induction hV with
  | algebraic hA =>
    obtain ⟨poly_set, rfl⟩ := hA
    refine ⟨conjEqZeroO poly_set.toList, conjEqZeroO_isQF _, ?_⟩
    rw [conjEqZeroO_realization]; ext y; simp
  | pos_locus P => exact ⟨gtZeroO P, trivial, rfl⟩
  | compl _ ih => obtain ⟨Φ, hqf, rfl⟩ := ih; exact ⟨.not Φ, hqf, rfl⟩
  | inter _ _ ih₁ ih₂ =>
    obtain ⟨Φ₁, hqf₁, rfl⟩ := ih₁; obtain ⟨Φ₂, hqf₂, rfl⟩ := ih₂
    exact ⟨.and Φ₁ Φ₂, ⟨hqf₁, hqf₂⟩, rfl⟩

/-- Over-`D` quantifier-free characterization of semialgebraic sets: a set is
semialgebraic over `D` iff it is the realization of a quantifier-free formula with
`D`-coefficient atoms. -/
theorem semialgebraic_iff_qfRealizableOver (V : Set (Fin k → R)) :
    IsSemialgebraicSetOver D V ↔
      ∃ Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) D),
        Φ.IsQuantifierFree ∧ V = Φ.realization (C := R) :=
  ⟨semialgebraic_isQFRealizableOver V,
   fun ⟨_, hqf, hV⟩ => hV ▸ qfRealizable_isSemialgebraicSetOver hqf⟩

omit [IsStrictOrderedRing R] in
/-- The empty set is semialgebraic over `D` (complement of the universe). -/
theorem IsSemialgebraicSetOver.empty :
    IsSemialgebraicSetOver D (∅ : Set (Fin k → R)) := by
  have huniv : IsSemialgebraicSetOver D (Set.univ : Set (Fin k → R)) :=
    .algebraic ⟨∅, by ext x; simp⟩
  have h := huniv.compl
  rwa [Set.compl_univ] at h

/-- **Reduction for BPR Theorem 2.76.** The projection (drop the last variable) of a
set semialgebraic over `D` is semialgebraic over `D`, *given* the kernel: the
projection of every **basic cell** `{(y,x) | P(y,x) = 0 ∧ ⋀ q ∈ 𝒬, q(y,x) > 0}`
over `D` is semialgebraic over `D`.

By the disjunctive normal form over `D`
(`IsFinUnionOfBasicOver.of_isSemialgebraicSetOver`) the input is a finite union of
basic cells; projection commutes with union, so the kernel handles each cell and
`IsSemialgebraicSetOver.union` reassembles. The kernel is the remaining content —
the parametrized Sturm–Tarski sign determination of Lemmas 2.74 / 2.75. -/
theorem theorem_2_76_of_basicCellProjection
    (hcell : ∀ (P : MvPolynomial (Fin (k+1)) D) (Q : Finset (MvPolynomial (Fin (k+1)) D)),
        IsSemialgebraicSetOver D
          (Fin.init '' {x : Fin (k+1) → R | aeval x P = 0 ∧ ∀ q ∈ Q, aeval x q > 0}))
    {S : Set (Fin (k+1) → R)} (hS : IsSemialgebraicSetOver D S) :
    IsSemialgebraicSetOver D (Fin.init '' S) := by
  have hFUB := IsFinUnionOfBasicOver.of_isSemialgebraicSetOver hS
  clear hS
  induction hFUB with
  | empty => rw [Set.image_empty]; exact IsSemialgebraicSetOver.empty
  | basic hB => obtain ⟨P, Q, rfl⟩ := hB; exact hcell P Q
  | union _ _ ih1 ih2 => rw [Set.image_union]; exact ih1.union ih2

/-- The basic-cell projection kernel in the case of no positivity constraints
(`Q = ∅`): it is exactly Theorem 2.62's fiber-non-empty result. The general
`Q ≠ ∅` case is the remaining content (parametrized Sturm–Tarski via
Lemmas 2.74 / 2.75). -/
theorem basicCellProjection_empty [IsRealClosed R] [IsDomain D]
    (hinj : Function.Injective (algebraMap D R)) (P : MvPolynomial (Fin (k+1)) D) :
    IsSemialgebraicSetOver D
      (Fin.init '' {x : Fin (k+1) → R | aeval x P = 0 ∧
        ∀ q ∈ (∅ : Finset (MvPolynomial (Fin (k+1)) D)), aeval x q > 0}) := by
  have hset : {x : Fin (k+1) → R | aeval x P = 0 ∧
      ∀ q ∈ (∅ : Finset (MvPolynomial (Fin (k+1)) D)), aeval x q > 0}
      = {x | aeval x P = 0} := by ext x; simp
  rw [hset, Fin.init_image_eq_exists_aeval]
  exact fiber_nonempty_isSemialgebraicSetOver hinj P

end Azurite.BPR
