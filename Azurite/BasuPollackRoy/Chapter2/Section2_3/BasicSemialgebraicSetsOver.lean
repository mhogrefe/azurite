import Azurite.BasuPollackRoy.Chapter2.Section2_3.SemialgebraicSets

/-! # Basic semialgebraic sets defined over `D` (disjunctive normal form)

The over-`D` analogue of `BasicSemialgebraicSets.lean`: a *basic semialgebraic
set over `D`* is `{x | P(x) = 0 ∧ ⋀ q ∈ 𝒬, q(x) > 0}` with `P, 𝒬` over `D`
(evaluated by `aeval`). Every set semialgebraic over `D` is a finite union of
basic ones (`IsFinUnionOfBasicOver.of_isSemialgebraicSetOver`) — the disjunctive
normal form used to reduce the projection theorem (Theorem 2.76) to the
projection of a single basic cell.

The proofs mirror the absolute `BasicSemialgebraicSets.lean`, replacing `eval`
by `aeval` and `R`-coefficients by `D`-coefficients (`aeval` is a ring
homomorphism, so the sum-of-squares and boolean-closure arguments transfer
verbatim).
-/

namespace Azurite.BPR

open MvPolynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {D : Type*} [CommRing D] [Algebra D R]

/-- A basic semialgebraic subset of `R^k` defined over `D`. -/
def IsBasicSemialgebraicSetOver (D : Type*) [CommRing D] [Algebra D R]
    (V : Set (Fin k → R)) : Prop :=
  ∃ (P : MvPolynomial (Fin k) D) (Q : Finset (MvPolynomial (Fin k) D)),
    V = {x | aeval x P = 0 ∧ ∀ q ∈ Q, aeval x q > 0}

/-- Finite unions of basic semialgebraic subsets defined over `D`. -/
inductive IsFinUnionOfBasicOver (D : Type*) [CommRing D] [Algebra D R] :
    Set (Fin k → R) → Prop where
  | empty : IsFinUnionOfBasicOver D ∅
  | basic {B} : IsBasicSemialgebraicSetOver D B → IsFinUnionOfBasicOver D B
  | union {V W} : IsFinUnionOfBasicOver D V → IsFinUnionOfBasicOver D W →
      IsFinUnionOfBasicOver D (V ∪ W)

namespace IsBasicSemialgebraicSetOver

omit [IsStrictOrderedRing R] in
theorem univ : IsBasicSemialgebraicSetOver D (Set.univ : Set (Fin k → R)) :=
  ⟨0, ∅, by ext x; simp⟩

omit [IsStrictOrderedRing R] in
theorem eqZero (P : MvPolynomial (Fin k) D) :
    IsBasicSemialgebraicSetOver D ({x : Fin k → R | aeval x P = 0}) :=
  ⟨P, ∅, by ext x; simp⟩

omit [IsStrictOrderedRing R] in
theorem gtZero (P : MvPolynomial (Fin k) D) :
    IsBasicSemialgebraicSetOver D ({x : Fin k → R | aeval x P > 0}) :=
  ⟨0, {P}, by ext x; simp⟩

theorem ltZero (P : MvPolynomial (Fin k) D) :
    IsBasicSemialgebraicSetOver D ({x : Fin k → R | aeval x P < 0}) := by
  refine ⟨0, {-P}, ?_⟩; ext x; simp [map_neg]

theorem inter {V W : Set (Fin k → R)}
    (hV : IsBasicSemialgebraicSetOver D V) (hW : IsBasicSemialgebraicSetOver D W) :
    IsBasicSemialgebraicSetOver D (V ∩ W) := by
  classical
  obtain ⟨P₁, Q₁, rfl⟩ := hV; obtain ⟨P₂, Q₂, rfl⟩ := hW
  refine ⟨P₁ ^ 2 + P₂ ^ 2, Q₁ ∪ Q₂, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union, map_add, map_pow]
  constructor
  · rintro ⟨⟨hp₁, hQ₁⟩, hp₂, hQ₂⟩
    refine ⟨by rw [hp₁, hp₂]; ring, ?_⟩
    rintro q (hq | hq); exacts [hQ₁ q hq, hQ₂ q hq]
  · rintro ⟨hsum, hQ⟩
    have hP₁ : (aeval x P₁ : R) ^ 2 = 0 := by
      nlinarith [sq_nonneg (aeval x P₁ : R), sq_nonneg (aeval x P₂ : R)]
    have hP₂ : (aeval x P₂ : R) ^ 2 = 0 := by
      nlinarith [sq_nonneg (aeval x P₁ : R), sq_nonneg (aeval x P₂ : R)]
    exact ⟨⟨sq_eq_zero_iff.mp hP₁, fun q hq => hQ q (Or.inl hq)⟩,
           sq_eq_zero_iff.mp hP₂, fun q hq => hQ q (Or.inr hq)⟩

end IsBasicSemialgebraicSetOver

namespace IsFinUnionOfBasicOver

private theorem basicInter {B W : Set (Fin k → R)}
    (hB : IsBasicSemialgebraicSetOver D B) (hW : IsFinUnionOfBasicOver D W) :
    IsFinUnionOfBasicOver D (B ∩ W) := by
  induction hW with
  | empty => rw [Set.inter_empty]; exact .empty
  | basic hB' => exact .basic (hB.inter hB')
  | union _ _ ihW₁ ihW₂ => rw [Set.inter_union_distrib_left]; exact ihW₁.union ihW₂

theorem inter {V W : Set (Fin k → R)}
    (hV : IsFinUnionOfBasicOver D V) (hW : IsFinUnionOfBasicOver D W) :
    IsFinUnionOfBasicOver D (V ∩ W) := by
  induction hV with
  | empty => rw [Set.empty_inter]; exact .empty
  | basic hB => exact basicInter hB hW
  | union _ _ ihV₁ ihV₂ => rw [Set.union_inter_distrib_right]; exact ihV₁.union ihV₂

omit [IsStrictOrderedRing R] in
theorem univ : IsFinUnionOfBasicOver D (Set.univ : Set (Fin k → R)) :=
  .basic IsBasicSemialgebraicSetOver.univ

private theorem le_zero (P : MvPolynomial (Fin k) D) :
    IsFinUnionOfBasicOver D ({x : Fin k → R | aeval x P ≤ 0}) := by
  have h_lt : IsFinUnionOfBasicOver D ({x : Fin k → R | aeval x P < 0}) :=
    .basic (IsBasicSemialgebraicSetOver.ltZero P)
  have h_eq : IsFinUnionOfBasicOver D ({x : Fin k → R | aeval x P = 0}) :=
    .basic (IsBasicSemialgebraicSetOver.eqZero P)
  have h := h_lt.union h_eq
  convert h using 1
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_union]; exact le_iff_lt_or_eq

private theorem ne_zero (P : MvPolynomial (Fin k) D) :
    IsFinUnionOfBasicOver D ({x : Fin k → R | aeval x P ≠ 0}) := by
  have h_pos : IsFinUnionOfBasicOver D ({x : Fin k → R | aeval x P > 0}) :=
    .basic (IsBasicSemialgebraicSetOver.gtZero P)
  have h_neg : IsFinUnionOfBasicOver D ({x : Fin k → R | aeval x P < 0}) :=
    .basic (IsBasicSemialgebraicSetOver.ltZero P)
  have h := h_pos.union h_neg
  convert h using 1
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_union]
  exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim ne_of_gt ne_of_lt⟩

private theorem complementOfBasic (P : MvPolynomial (Fin k) D)
    (Q : Finset (MvPolynomial (Fin k) D)) :
    IsFinUnionOfBasicOver D
      ({x : Fin k → R | aeval x P = 0 ∧ ∀ q ∈ Q, aeval x q > 0}ᶜ) := by
  classical
  induction Q using Finset.induction with
  | empty =>
    have h := ne_zero (R := R) P
    convert h using 1; ext x; simp
  | @insert q' Q' _ ih =>
    have h := ih.union (le_zero (R := R) q')
    convert h using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, Finset.forall_mem_insert]
    constructor
    · intro hn
      by_cases hq' : aeval x q' > 0
      · left; rintro ⟨hP, hQ'⟩; exact hn ⟨hP, hq', hQ'⟩
      · right; exact not_lt.mp hq'
    · rintro (hn | hq')
      · rintro ⟨hP, _, hQ'⟩; exact hn ⟨hP, hQ'⟩
      · rintro ⟨_, hq, _⟩; linarith

theorem compl {V : Set (Fin k → R)} (h : IsFinUnionOfBasicOver D V) :
    IsFinUnionOfBasicOver D Vᶜ := by
  induction h with
  | empty => rw [Set.compl_empty]; exact univ
  | basic hB => obtain ⟨P, Q, rfl⟩ := hB; exact complementOfBasic P Q
  | union _ _ ihV ihW => rw [Set.compl_union]; exact ihV.inter ihW

/-- **Disjunctive normal form over `D`.** Every set semialgebraic over `D` is a
finite union of basic semialgebraic sets over `D`. -/
theorem of_isSemialgebraicSetOver {V : Set (Fin k → R)} (h : IsSemialgebraicSetOver D V) :
    IsFinUnionOfBasicOver D V := by
  induction h with
  | algebraic hAlg =>
    obtain ⟨S, rfl⟩ := hAlg
    refine .basic ⟨∑ P ∈ S, P ^ 2, ∅, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Finset.notMem_empty, false_implies, implies_true, and_true,
      map_sum, map_pow]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun P _ => sq_nonneg (aeval x P : R))]
    constructor
    · intro h P hP; rw [h P hP]; ring
    · intro h P hP; exact pow_eq_zero_iff (by norm_num) |>.mp (h P hP)
  | pos_locus P => exact .basic (IsBasicSemialgebraicSetOver.gtZero P)
  | compl _ ih => exact ih.compl
  | inter _ _ ihV ihW => exact ihV.inter ihW

end IsFinUnionOfBasicOver

end Azurite.BPR
