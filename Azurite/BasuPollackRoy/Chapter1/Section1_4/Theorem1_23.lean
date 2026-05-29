import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleQF
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_2
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization
import Azurite.BasuPollackRoy.Chapter1.Section1_1.RealizationInvariance
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Theorem1_22

/-! # BPR Section 1.4 — Theorem 1.23: Quantifier Elimination over ACF

> **Theorem 1.23** (Quantifier elimination over algebraically closed fields).
> Let `Φ(Y_1, …, Y_ℓ)` be a formula in the language of fields with free
> variables `{Y_1, …, Y_ℓ}` and coefficients in a subring `D` of the
> algebraically closed field `C`. Then there is a quantifier-free formula
> `Ψ(Y_1, …, Y_ℓ)` with coefficients in `D` which is `C`-equivalent to
> `Φ(Y_1, …, Y_ℓ)`.

**Proof outline** (BPR): By induction on quantifier count.
* The case `∀X Φ` reduces to `¬∃X ¬Φ`.
* The case `∃X Φ` with `Φ` quantifier-free uses Theorem 1.22 (the projection
  theorem): the projection of `Reali(Φ, C^{k+1})` to `C^k` is constructible,
  hence the realization of a quantifier-free formula.

**Detailed structure of the proof:**
1. **DNF normalisation** — every QF formula over `D` is `C`-equivalent to a
   disjunction of *conjFormFormula* `Ps Qs` (conjunctions of equations and
   disequations).
2. **QE step for conjFormFormula at last variable** — for lists `Ps, Qs` of
   polynomials in `D[Y_1, …, Y_{k+1}]`, the formula
   `∃ (Fin.last k), (⋀ P = 0 ∧ ⋀ Q ≠ 0)` is `C`-equivalent to the lift of
   `projBasic Ps Qs` from `Fin k` to `Fin (k+1)` via `Fin.castSucc`.
3. **Variable swap** — for arbitrary `i : Fin (k+1)`, we reduce `∃ i Φ` to
   `∃ (Fin.last k) Φ̃` where `Φ̃ = Φ.rename (Equiv.swap i (Fin.last k))`.
4. **Structural induction** — combine the pieces with `eliminateForall`
   (which rewrites `∀X Φ` as `¬∃X ¬Φ`) and handle `∃X` via 1–3.

This file establishes the foundational lemmas; the main theorem
`theorem_1_23` is built up via several helper steps marked `existsQE_*`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial Formula

variable {D : Type*} [CommRing D]
variable {C : Type*} [Field C] [Algebra D C] [IsAlgClosed C]

/-!
### Bridge lemma: `Function.update y (Fin.last k) c = Fin.snoc (y ∘ castSucc) c`

This identity bridges the formula-level `∃ (Fin.last k)` realization (which
uses `Function.update`) with Theorem 1.22's projection set (which uses
`Fin.snoc`).
-/

omit [Field C] [Algebra D C] [IsAlgClosed C] in
theorem update_last_eq_snoc_castSucc {k : ℕ}
    (y : Fin (k+1) → C) (c : C) :
    Function.update y (Fin.last k) c =
      Fin.snoc (fun j : Fin k => y j.castSucc) c := by
  ext j
  refine Fin.lastCases ?_ ?_ j
  · simp [Function.update]
  · intro j'
    have hne : j'.castSucc ≠ Fin.last k :=
      Fin.ne_of_lt (Fin.castSucc_lt_last _)
    simp [Function.update, hne]

omit [IsAlgClosed C] in
/-- Realisation of `∃ (Fin.last k), Φ` rewritten via `Fin.snoc`. -/
theorem realization_exists_last {k : ℕ}
    (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D)) :
    (Formula.exists_ (Fin.last k) Φ).realization (C := C) =
      { y : Fin (k+1) → C | ∃ c : C,
          Fin.snoc (fun j : Fin k => y j.castSucc) c
            ∈ Φ.realization (C := C) } := by
  show { y | ∃ c : C, Function.update y (Fin.last k) c ∈ Φ.realization (C := C) } = _
  ext y
  simp only [Set.mem_setOf_eq]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · rwa [update_last_eq_snoc_castSucc] at hc
  · rwa [update_last_eq_snoc_castSucc]

/-!
### Conjunctive-form formulas

The basic building block: `conjFormFormula Ps Qs` is the formula
`⋀ Pᵢ = 0 ∧ ⋀ Qⱼ ≠ 0`, the conjunction of equations and disequations
that `projBasic` operates on.
-/

omit [IsAlgClosed C] [Algebra D C] in
/-- Conjunction of `Q_i ≠ 0` atoms. -/
noncomputable def conjNeZero {σ : Type*}
    (Qs : List (MvPolynomial σ D)) : Formula σ (FieldAtom σ D) :=
  Formula.conjList (Qs.map Formula.ne_zero)

omit [IsAlgClosed C] [Algebra D C] in
/-- The conj-form formula `⋀ Pᵢ = 0 ∧ ⋀ Qⱼ ≠ 0`. -/
noncomputable def conjFormFormula {σ : Type*}
    (Ps Qs : List (MvPolynomial σ D)) : Formula σ (FieldAtom σ D) :=
  Formula.and (conjEqZero Ps) (conjNeZero Qs)

omit [IsAlgClosed C] [Algebra D C] in
theorem conjNeZero_isQF {σ : Type*}
    (Qs : List (MvPolynomial σ D)) :
    (conjNeZero (D := D) Qs).IsQuantifierFree := by
  apply Formula.conjList_isQF
  intro Φ hΦ
  rw [List.mem_map] at hΦ
  obtain ⟨Q, _, rfl⟩ := hΦ
  exact trivial

omit [IsAlgClosed C] [Algebra D C] in
theorem conjFormFormula_isQF {σ : Type*}
    (Ps Qs : List (MvPolynomial σ D)) :
    (conjFormFormula (D := D) Ps Qs).IsQuantifierFree :=
  ⟨conjEqZero_isQF Ps, conjNeZero_isQF Qs⟩

omit [IsAlgClosed C] in
theorem realization_conjNeZero {σ : Type*} [DecidableEq σ]
    (Qs : List (MvPolynomial σ D)) :
    (conjNeZero Qs).realization (C := C) =
      { y | ∀ Q ∈ Qs, MvPolynomial.aeval y Q ≠ 0 } := by
  unfold conjNeZero
  rw [Formula.realization_conjList]
  ext y
  simp only [Set.mem_setOf_eq, List.forall_mem_map]
  refine ⟨fun h Q hQ => ?_, fun h Q hQ => ?_⟩
  · have := h Q hQ
    simpa [Formula.ne_zero, realization, FieldAtom.neZero] using this
  · simp only [Formula.ne_zero, realization, FieldAtom.neZero]
    exact h Q hQ

omit [IsAlgClosed C] in
theorem realization_conjFormFormula {σ : Type*} [DecidableEq σ]
    (Ps Qs : List (MvPolynomial σ D)) :
    (conjFormFormula Ps Qs).realization (C := C) =
      { y | (∀ P ∈ Ps, MvPolynomial.aeval y P = 0) ∧
            (∀ Q ∈ Qs, MvPolynomial.aeval y Q ≠ 0) } := by
  unfold conjFormFormula
  rw [Formula.realization_and, conjEqZero_realization,
      realization_conjNeZero]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq,
    MvPolynomial.aeval_def]

/-!
### QE step: `∃ (Fin.last k), conjFormFormula Ps Qs`

Lifting `projBasic Ps Qs` from `Fin k` to `Fin (k+1)` via `Fin.castSucc`
gives a QF formula whose realization equals
`(∃ (Fin.last k), conjFormFormula Ps Qs).realization`.
-/

section ExistsLastQE
variable [IsDomain D]

/-- QE step for conj-form at the last variable: the lift of
`projBasic Ps Qs` via `Fin.castSucc` is a QF formula in `Fin (k+1)`
variables whose `C`-realisation equals
`(∃ (Fin.last k), conjFormFormula Ps Qs).realisation`. -/
theorem realization_exists_last_conjFormFormula {k : ℕ}
    (hinj : Function.Injective (algebraMap D C))
    (Ps Qs : List (MvPolynomial (Fin (k+1)) D)) :
    (Formula.exists_ (Fin.last k)
        (conjFormFormula Ps Qs)).realization (C := C) =
      ((projBasic Ps Qs).rename Fin.castSucc
          (FieldAtom.renameVars Fin.castSucc)).realization (C := C) := by
  rw [realization_exists_last,
      Formula.rename_realization Fin.castSucc (Fin.castSucc_injective k),
      realization_projBasic hinj]
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  refine ⟨fun ⟨c, hc⟩ => ?_, fun ⟨c, hc⟩ => ?_⟩
  · refine ⟨c, ?_, ?_⟩
    · intro P hP
      rw [realization_conjFormFormula] at hc
      exact hc.1 P hP
    · intro Q hQ
      rw [realization_conjFormFormula] at hc
      exact hc.2 Q hQ
  · rw [realization_conjFormFormula]
    exact ⟨c, hc.1, hc.2⟩

omit [IsAlgClosed C] [Algebra D C] in
/-- The QE step preserves `IsQuantifierFree`: the rename of `projBasic`
is QF. -/
theorem qe_last_conjFormFormula_isQF {k : ℕ}
    (Ps Qs : List (MvPolynomial (Fin (k+1)) D)) :
    ((projBasic Ps Qs).rename Fin.castSucc
        (FieldAtom.renameVars Fin.castSucc)).IsQuantifierFree :=
  Formula.rename_isQF _ _ _ (projBasic_isQF Ps Qs)

end ExistsLastQE

/-!
### DNF normalization for QF formulas

Every QF formula `Φ : Formula σ (FieldAtom σ D)` is `C`-equivalent to a finite
disjunction of `conjFormFormula Ps Qs` formulas. The function `qfDNFAux`
computes, polarity-aware, the list of pairs `(Ps, Qs)` such that the union of
`conjFormFormula Ps Qs` realizations equals either `Φ.realization` (when
`b = true`) or its complement (when `b = false`).
-/

omit [IsAlgClosed C] [Algebra D C] in
/-- Polarity-aware DNF computation. With `b = true`, returns a list of pairs
`(Ps, Qs)` whose conj-form realizations union to `Φ.realization`. With
`b = false`, the union equals the complement. -/
noncomputable def qfDNFAux {σ : Type*} (b : Bool) :
    Formula σ (FieldAtom σ D) →
    List (List (MvPolynomial σ D) × List (MvPolynomial σ D))
  | .atom a =>
      let isEq := if b then a.isEq else !a.isEq
      if isEq then [([a.poly], [])] else [([], [a.poly])]
  | .not Φ => qfDNFAux (!b) Φ
  | .and Φ₁ Φ₂ =>
      if b then
        (qfDNFAux true Φ₁).flatMap fun PQ₁ =>
          (qfDNFAux true Φ₂).map fun PQ₂ =>
            (PQ₁.1 ++ PQ₂.1, PQ₁.2 ++ PQ₂.2)
      else
        qfDNFAux false Φ₁ ++ qfDNFAux false Φ₂
  | .or Φ₁ Φ₂ =>
      if b then qfDNFAux true Φ₁ ++ qfDNFAux true Φ₂
      else
        (qfDNFAux false Φ₁).flatMap fun PQ₁ =>
          (qfDNFAux false Φ₂).map fun PQ₂ =>
            (PQ₁.1 ++ PQ₂.1, PQ₁.2 ++ PQ₂.2)
  | .implies Φ₁ Φ₂ =>
      if b then qfDNFAux false Φ₁ ++ qfDNFAux true Φ₂
      else
        (qfDNFAux true Φ₁).flatMap fun PQ₁ =>
          (qfDNFAux false Φ₂).map fun PQ₂ =>
            (PQ₁.1 ++ PQ₂.1, PQ₁.2 ++ PQ₂.2)
  | .exists_ _ Φ => qfDNFAux b Φ
  | .forall_ _ Φ => qfDNFAux b Φ

omit [IsAlgClosed C] in
/-- `conjFormFormula` distributes over list append as set intersection. -/
theorem realization_conjFormFormula_append {σ : Type*} [DecidableEq σ]
    (P₁s P₂s Q₁s Q₂s : List (MvPolynomial σ D)) :
    (conjFormFormula (P₁s ++ P₂s) (Q₁s ++ Q₂s)).realization (C := C) =
      (conjFormFormula P₁s Q₁s).realization (C := C) ∩
        (conjFormFormula P₂s Q₂s).realization (C := C) := by
  rw [realization_conjFormFormula, realization_conjFormFormula,
      realization_conjFormFormula]
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, List.mem_append]
  constructor
  · rintro ⟨hP, hQ⟩
    refine ⟨⟨fun P hP₁ => hP P (Or.inl hP₁),
            fun Q hQ₁ => hQ Q (Or.inl hQ₁)⟩,
           ⟨fun P hP₂ => hP P (Or.inr hP₂),
            fun Q hQ₂ => hQ Q (Or.inr hQ₂)⟩⟩
  · rintro ⟨⟨hP₁, hQ₁⟩, ⟨hP₂, hQ₂⟩⟩
    refine ⟨fun P hP => ?_, fun Q hQ => ?_⟩
    · rcases hP with h | h
      · exact hP₁ P h
      · exact hP₂ P h
    · rcases hQ with h | h
      · exact hQ₁ Q h
      · exact hQ₂ Q h

omit [IsAlgClosed C] in
/-- Union over a list append splits as union of two unions. -/
theorem iUnion_conjFormFormula_append {σ : Type*} [DecidableEq σ]
    (L₁ L₂ : List (List (MvPolynomial σ D) × List (MvPolynomial σ D))) :
    (⋃ PQ ∈ L₁ ++ L₂, (conjFormFormula PQ.1 PQ.2).realization (C := C)) =
      (⋃ PQ ∈ L₁, (conjFormFormula PQ.1 PQ.2).realization (C := C)) ∪
        (⋃ PQ ∈ L₂, (conjFormFormula PQ.1 PQ.2).realization (C := C)) := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨PQ, h | h, hy⟩
    · exact Or.inl ⟨PQ, h, hy⟩
    · exact Or.inr ⟨PQ, h, hy⟩
  · rintro (⟨PQ, h, hy⟩ | ⟨PQ, h, hy⟩)
    · exact ⟨PQ, Or.inl h, hy⟩
    · exact ⟨PQ, Or.inr h, hy⟩

omit [IsAlgClosed C] in
/-- The union over a flatMap is the union of unions over inner lists. -/
theorem iUnion_conjFormFormula_flatMap_map {σ : Type*} [DecidableEq σ]
    (L₁ L₂ : List (List (MvPolynomial σ D) × List (MvPolynomial σ D))) :
    (⋃ PQ ∈ L₁.flatMap fun PQ₁ =>
        L₂.map fun PQ₂ => (PQ₁.1 ++ PQ₂.1, PQ₁.2 ++ PQ₂.2),
      (conjFormFormula PQ.1 PQ.2).realization (C := C)) =
      (⋃ PQ₁ ∈ L₁, (conjFormFormula PQ₁.1 PQ₁.2).realization (C := C)) ∩
        (⋃ PQ₂ ∈ L₂, (conjFormFormula PQ₂.1 PQ₂.2).realization (C := C)) := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_inter_iff, List.mem_flatMap,
    List.mem_map]
  constructor
  · rintro ⟨PQ, ⟨PQ₁, hPQ₁, PQ₂, hPQ₂, rfl⟩, hy⟩
    rw [realization_conjFormFormula_append] at hy
    exact ⟨⟨PQ₁, hPQ₁, hy.1⟩, ⟨PQ₂, hPQ₂, hy.2⟩⟩
  · rintro ⟨⟨PQ₁, hPQ₁, hy₁⟩, ⟨PQ₂, hPQ₂, hy₂⟩⟩
    refine ⟨(PQ₁.1 ++ PQ₂.1, PQ₁.2 ++ PQ₂.2),
      ⟨PQ₁, hPQ₁, PQ₂, hPQ₂, rfl⟩, ?_⟩
    rw [realization_conjFormFormula_append]
    exact ⟨hy₁, hy₂⟩

omit [IsAlgClosed C] in
/-- Main correctness theorem for `qfDNFAux`. With `b = true`, the union of
conj-form realizations equals `Φ.realization`. With `b = false`, the union
equals its complement. -/
theorem qfDNFAux_realization {σ : Type*} [DecidableEq σ]
    (b : Bool) (Φ : Formula σ (FieldAtom σ D))
    (hQF : Φ.IsQuantifierFree) :
    (if b then Φ.realization (C := C) else (Φ.realization (C := C))ᶜ) =
      ⋃ PQ ∈ qfDNFAux b Φ, (conjFormFormula PQ.1 PQ.2).realization (C := C) := by
  induction Φ generalizing b with
  | atom a =>
    -- Goal: (if b then (atom a).realization else (atom a).realization ᶜ)
    --   = ⋃ PQ ∈ qfDNFAux b (atom a), (conjFormFormula PQ.1 PQ.2).realization
    -- The list has exactly one entry, so we reduce both sides to one
    -- conjFormFormula realization.
    have hSingle : ∀ (Ps Qs : List (MvPolynomial σ D)),
        (⋃ PQ ∈ [(Ps, Qs)], (conjFormFormula PQ.1 PQ.2).realization (C := C)) =
          (conjFormFormula Ps Qs).realization (C := C) := by
      intro Ps Qs
      simp [Set.iUnion_iUnion_eq_left]
    simp only [qfDNFAux]
    -- Split on b and a.isEq
    rcases hb : b with _ | _ <;> rcases hisEq : a.isEq with _ | _
    all_goals simp only [Bool.false_eq_true, Bool.not_false, Bool.not_true,
      if_true, if_false, hSingle]
    all_goals
      rw [realization_conjFormFormula]
      ext y
      show _ ↔ _
      simp only [Formula.realization, interpret_fieldAtom, hisEq,
        Bool.false_eq_true, if_true, if_false, Set.mem_setOf_eq, Set.mem_compl_iff,
        List.mem_singleton, List.not_mem_nil, IsEmpty.forall_iff, forall_eq,
        implies_true, and_true, true_and]
      try tauto
  | not Φ ih =>
    have hQF' : Φ.IsQuantifierFree := hQF
    simp only [qfDNFAux, Formula.realization]
    rcases b with _ | _
    · -- b = false: want (Φ.realization)ᶜᶜ = Φ.realization = ⋃ qfDNFAux true Φ
      simp only [Bool.false_eq_true, if_false, compl_compl, Bool.not_false]
      have := ih true hQF'
      simp only [if_true] at this
      exact this
    · -- b = true: want (Φ.realization)ᶜ = ⋃ qfDNFAux false Φ
      simp only [if_true, Bool.not_true]
      have := ih false hQF'
      simp only [Bool.false_eq_true, if_false] at this
      exact this
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    simp only [qfDNFAux, Formula.realization]
    rcases b with _ | _
    · -- b = false: want (Φ₁.realization ∩ Φ₂.realization)ᶜ
      --   = (Φ₁.realization)ᶜ ∪ (Φ₂.realization)ᶜ
      simp only [Bool.false_eq_true, if_false, Set.compl_inter]
      rw [iUnion_conjFormFormula_append]
      have h₁ := ih₁ false hQF₁
      have h₂ := ih₂ false hQF₂
      simp only [Bool.false_eq_true, if_false] at h₁ h₂
      rw [h₁, h₂]
    · -- b = true: want Φ₁.realization ∩ Φ₂.realization
      simp only [if_true]
      rw [iUnion_conjFormFormula_flatMap_map]
      have h₁ := ih₁ true hQF₁
      have h₂ := ih₂ true hQF₂
      simp only [if_true] at h₁ h₂
      rw [h₁, h₂]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    simp only [qfDNFAux, Formula.realization]
    rcases b with _ | _
    · -- b = false: want (Φ₁.realization ∪ Φ₂.realization)ᶜ
      --   = (Φ₁.realization)ᶜ ∩ (Φ₂.realization)ᶜ
      simp only [Bool.false_eq_true, if_false, Set.compl_union]
      rw [iUnion_conjFormFormula_flatMap_map]
      have h₁ := ih₁ false hQF₁
      have h₂ := ih₂ false hQF₂
      simp only [Bool.false_eq_true, if_false] at h₁ h₂
      rw [h₁, h₂]
    · -- b = true: want Φ₁.realization ∪ Φ₂.realization
      simp only [if_true]
      rw [iUnion_conjFormFormula_append]
      have h₁ := ih₁ true hQF₁
      have h₂ := ih₂ true hQF₂
      simp only [if_true] at h₁ h₂
      rw [h₁, h₂]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    simp only [qfDNFAux, Formula.realization]
    rcases b with _ | _
    · -- b = false: want ((Φ₁.realization)ᶜ ∪ Φ₂.realization)ᶜ
      --   = Φ₁.realization ∩ (Φ₂.realization)ᶜ
      simp only [Bool.false_eq_true, if_false, Set.compl_union, compl_compl]
      rw [iUnion_conjFormFormula_flatMap_map]
      have h₁ := ih₁ true hQF₁
      have h₂ := ih₂ false hQF₂
      simp only [if_true, Bool.false_eq_true, if_false] at h₁ h₂
      rw [h₁, h₂]
    · -- b = true: want (Φ₁.realization)ᶜ ∪ Φ₂.realization
      simp only [if_true]
      rw [iUnion_conjFormFormula_append]
      have h₁ := ih₁ false hQF₁
      have h₂ := ih₂ true hQF₂
      simp only [Bool.false_eq_true, if_false, if_true] at h₁ h₂
      rw [h₁, h₂]
  | exists_ _ _ _ => exact absurd hQF id
  | forall_ _ _ _ => exact absurd hQF id

omit [IsAlgClosed C] in
/-- The DNF specialization: any QF formula's realization equals the union of
conj-form realizations. -/
theorem qfDNF_realization {σ : Type*} [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D))
    (hQF : Φ.IsQuantifierFree) :
    Φ.realization (C := C) =
      ⋃ PQ ∈ qfDNFAux true Φ,
        (conjFormFormula PQ.1 PQ.2).realization (C := C) := by
  have := qfDNFAux_realization (D := D) (C := C) true Φ hQF
  simpa using this

/-!
### Variable swap

We reduce the existential `∃ i Φ` over an arbitrary variable `i : Fin (k+1)` to
the case `∃ (Fin.last k) Φ̃` by renaming via `Equiv.swap i (Fin.last k)`.
-/

omit [Field C] [Algebra D C] [IsAlgClosed C] in
/-- Composing `Function.update y i c` with `Equiv.swap i j` rewrites the
update from index `i` to index `j`, in the post-composition direction. -/
theorem update_comp_swap_eq {α β : Type*} [DecidableEq α]
    (y : α → β) (i j : α) (c : β) :
    Function.update y i c ∘ (Equiv.swap i j : α → α) =
      Function.update (y ∘ (Equiv.swap i j : α → α)) j c := by
  ext a
  by_cases hij : i = j
  · subst hij
    simp [Equiv.swap_self]
  · by_cases haj : a = j
    · subst haj
      -- swap i a a = i, so LHS = update y i c i = c. RHS = update _ a c a = c.
      rw [Function.comp_apply, Equiv.swap_apply_right,
        Function.update_self, Function.update_self]
    · by_cases hai : a = i
      · subst hai
        -- swap a j a = j, so LHS = update y a c j = y j (since a≠j).
        -- RHS = update (y∘swap a j) j c a = y∘swap a j a = y (swap a j a) = y j.
        rw [Function.comp_apply, Equiv.swap_apply_left,
          Function.update_of_ne hij, Function.update_of_ne (Ne.symm haj),
          Function.comp_apply, Equiv.swap_apply_left]
      · have hswap : (Equiv.swap i j : α → α) a = a :=
          Equiv.swap_apply_of_ne_of_ne hai haj
        rw [Function.comp_apply, hswap, Function.update_of_ne hai,
          Function.update_of_ne haj, Function.comp_apply, hswap]

omit [Field C] [Algebra D C] [IsAlgClosed C] in
/-- `Equiv.swap` is an involution: applied twice it is the identity. -/
theorem swap_comp_swap_eq_id {α : Type*} [DecidableEq α] (i j : α) :
    (Equiv.swap i j : α → α) ∘ (Equiv.swap i j) = id := by
  ext a; simp [Function.comp_apply, Equiv.swap_apply_self]

omit [IsAlgClosed C] in
/-- Variable swap for existential: swapping `i` and `Fin.last k` via
`Equiv.swap` gives an equivalent existential at `Fin.last k`. -/
theorem realization_exists_swap {k : ℕ} (i : Fin (k+1))
    (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D)) :
    (Formula.exists_ i Φ).realization (C := C) =
      (· ∘ (Equiv.swap i (Fin.last k))) ⁻¹'
        (Formula.exists_ (Fin.last k)
          (Φ.rename (Equiv.swap i (Fin.last k))
            (FieldAtom.renameVars (Equiv.swap i (Fin.last k))))).realization
            (C := C) := by
  set s : Fin (k+1) → Fin (k+1) :=
    ((Equiv.swap i (Fin.last k) : Equiv.Perm (Fin (k+1))) : Fin (k+1) → Fin (k+1))
  have hs_inj : Function.Injective s := (Equiv.swap i (Fin.last k)).injective
  have hs_comm : ((Equiv.swap (Fin.last k) i : Equiv.Perm (Fin (k+1))) :
      Fin (k+1) → Fin (k+1)) = s := by
    simp [s, Equiv.swap_comm]
  -- Unfold both realizations.
  show { y : Fin (k+1) → C | ∃ c : C, Function.update y i c ∈
      Φ.realization (C := C) } = _
  ext y
  -- RHS unfolds to: ∃ c, Function.update (y) (Fin.last k) c ∈ rename Φ realization (after preimage step).
  show (∃ c : C, Function.update y i c ∈ Φ.realization (C := C)) ↔
      (∃ c : C, Function.update (y ∘ s) (Fin.last k) c ∈
        (Φ.rename s (FieldAtom.renameVars s)).realization (C := C))
  rw [Formula.rename_realization s hs_inj]
  simp only [Set.mem_preimage]
  -- After unfolding rename, RHS becomes: ∃ c, (update (y∘s) (last k) c) ∘ s ∈ Φ.realization.
  -- Rewrite the composition using update_comp_swap_eq with the swap reversed.
  have key : ∀ c : C, Function.update (y ∘ s) (Fin.last k) c ∘ s =
      Function.update y i c := by
    intro c
    have h₁ : Function.update (y ∘ s) (Fin.last k) c ∘ s =
        Function.update ((y ∘ s) ∘ s) i c := by
      have := update_comp_swap_eq (y ∘ s) (Fin.last k) i c
      rw [hs_comm] at this
      exact this
    rw [h₁]
    have h₂ : (y ∘ s) ∘ s = y := by
      rw [Function.comp_assoc, swap_comp_swap_eq_id]; ext a; simp
    rw [h₂]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · rw [key c]; exact hc
  · rw [key c] at hc; exact hc

/-!
### Existential QE for arbitrary QF body

Given a QF formula `Φ` over `Fin (k+1)` variables and a variable
`i : Fin (k+1)`, we produce an equivalent QF formula `Ψ` for
`∃ i Φ`.

The construction:
1. Reduce to `∃ (Fin.last k)` via `realization_exists_swap`.
2. Apply DNF: `Φ̃.realization` is a finite union of `conjFormFormula`.
3. Distribute `∃` over the union, then apply
   `realization_exists_last_conjFormFormula` to each disjunct.
4. Take a `disjList` and rename via the swap to obtain Ψ.
-/

section ExistsQE
variable [IsDomain D]

omit [IsAlgClosed C] [IsDomain D] in
/-- `∃ x` distributes over a `disjList` of formulas. -/
theorem realization_exists_disjList {k : ℕ} (i : Fin (k+1))
    (Φs : List (Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D))) :
    (Formula.exists_ i (Formula.disjList Φs)).realization (C := C) =
      ⋃ Φ ∈ Φs, (Formula.exists_ i Φ).realization (C := C) := by
  ext y
  show (∃ c : C, Function.update y i c ∈
      (Formula.disjList Φs).realization (C := C)) ↔ _
  rw [Formula.realization_disjList]
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨c, Φ, hΦ, hc⟩
    refine ⟨Φ, hΦ, c, ?_⟩
    show Function.update y i c ∈ Φ.realization (C := C)
    exact hc
  · rintro ⟨Φ, hΦ, c, hc⟩
    refine ⟨c, Φ, hΦ, ?_⟩
    exact hc

omit [IsAlgClosed C] [IsDomain D] in
/-- Helper: the disjList of QF formulas is QF. -/
theorem disjList_isQF {σ : Type*}
    (Φs : List (Formula σ (FieldAtom σ D)))
    (hQF : ∀ Φ ∈ Φs, Φ.IsQuantifierFree) :
    (Formula.disjList Φs).IsQuantifierFree := by
  induction Φs with
  | nil => exact trivial
  | cons Φ Φs ih =>
    refine ⟨hQF Φ List.mem_cons_self, ih ?_⟩
    intro Ψ hΨ
    exact hQF Ψ (List.mem_cons_of_mem _ hΨ)

/-- Distribute `∃ (Fin.last k)` over a list of `conjFormFormula`'s, expressed as
a `disjList` of `conjFormFormula`'s. Each disjunct is QE'd to the
`rename castSucc` of a `projBasic`. -/
theorem realization_exists_last_qfDNF
    (hinj : Function.Injective (algebraMap D C)) {k : ℕ}
    (L : List (List (MvPolynomial (Fin (k+1)) D) ×
        List (MvPolynomial (Fin (k+1)) D))) :
    (Formula.exists_ (Fin.last k)
        (Formula.disjList (L.map fun PQ =>
          conjFormFormula PQ.1 PQ.2))).realization (C := C) =
      (Formula.disjList (L.map fun PQ =>
        (projBasic PQ.1 PQ.2).rename Fin.castSucc
          (FieldAtom.renameVars Fin.castSucc))).realization (C := C) := by
  rw [realization_exists_disjList]
  rw [Formula.realization_disjList]
  ext y
  simp only [Set.mem_iUnion, List.mem_map, Set.mem_setOf_eq]
  constructor
  · rintro ⟨Φ, ⟨PQ, hPQ, rfl⟩, hy⟩
    refine ⟨_, ⟨PQ, hPQ, rfl⟩, ?_⟩
    rw [← realization_exists_last_conjFormFormula hinj]
    exact hy
  · rintro ⟨Φ, ⟨PQ, hPQ, rfl⟩, hy⟩
    refine ⟨_, ⟨PQ, hPQ, rfl⟩, ?_⟩
    rw [realization_exists_last_conjFormFormula hinj]
    exact hy

omit [IsAlgClosed C] [Algebra D C] in
/-- The disjList of `(projBasic).rename castSucc` is QF. -/
theorem disjList_qe_isQF {k : ℕ}
    (L : List (List (MvPolynomial (Fin (k+1)) D) ×
        List (MvPolynomial (Fin (k+1)) D))) :
    (Formula.disjList (L.map fun PQ =>
      (projBasic PQ.1 PQ.2).rename Fin.castSucc
        (FieldAtom.renameVars Fin.castSucc))).IsQuantifierFree := by
  apply disjList_isQF
  intro Φ hΦ
  rw [List.mem_map] at hΦ
  obtain ⟨PQ, _, rfl⟩ := hΦ
  exact qe_last_conjFormFormula_isQF PQ.1 PQ.2

/-- **Existential QE for arbitrary QF body.** Given a QF formula `Φ`
and a variable `i`, there is a QF formula `Ψ` with the same realization
as `∃ i Φ`. -/
theorem existsQE
    (hinj : Function.Injective (algebraMap D C))
    {k : ℕ} (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D))
    (hQF : Φ.IsQuantifierFree) (i : Fin (k+1)) :
    ∃ Ψ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D),
      Ψ.IsQuantifierFree ∧
      (Formula.exists_ i Φ).realization (C := C) =
        Ψ.realization (C := C) := by
  set s : Fin (k+1) → Fin (k+1) :=
    ((Equiv.swap i (Fin.last k) : Equiv.Perm (Fin (k+1))) :
      Fin (k+1) → Fin (k+1))
  have hs_inj : Function.Injective s := (Equiv.swap i (Fin.last k)).injective
  -- Let Φ̃ be the renamed Φ (QF).
  set Φtilde : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D) :=
    Φ.rename s (FieldAtom.renameVars s)
  have hQF_tilde : Φtilde.IsQuantifierFree :=
    Formula.rename_isQF _ _ _ hQF
  -- DNF list for Φ̃.
  set L := qfDNFAux (D := D) true Φtilde
  -- The candidate Ψ (in Fin (k+1) → variables, but still under the s-swap):
  -- inner formula:
  set Ψ_inner : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D) :=
    Formula.disjList (L.map fun PQ =>
      (projBasic PQ.1 PQ.2).rename Fin.castSucc
        (FieldAtom.renameVars Fin.castSucc))
  -- Then rename by s to absorb the swap.
  refine ⟨Ψ_inner.rename s (FieldAtom.renameVars s), ?_, ?_⟩
  · exact Formula.rename_isQF _ _ _ (disjList_qe_isQF L)
  · -- Step 1: rewrite ∃ i Φ via swap.
    rw [realization_exists_swap (D := D) (C := C) i Φ]
    -- Now LHS = (· ∘ s) ⁻¹' (∃ Fin.last k, Φ̃).realization.
    -- Step 2: rewrite RHS via rename_realization.
    rw [Formula.rename_realization s hs_inj]
    -- Now RHS = (· ∘ s) ⁻¹' Ψ_inner.realization. Reduce to inner equality.
    congr 1
    -- Goal: (∃ Fin.last k, Φ̃).realization = Ψ_inner.realization.
    show (Formula.exists_ (Fin.last k) Φtilde).realization (C := C) =
      Ψ_inner.realization (C := C)
    -- Use DNF on Φ̃ to express it as a disjList of conjFormFormulas.
    have hDNF : Φtilde.realization (C := C) =
        (Formula.disjList (L.map fun PQ =>
          conjFormFormula PQ.1 PQ.2)).realization (C := C) := by
      rw [qfDNF_realization _ hQF_tilde, Formula.realization_disjList]
      ext y
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, List.mem_map]
      constructor
      · rintro ⟨PQ, hPQ, hy⟩
        exact ⟨_, ⟨PQ, hPQ, rfl⟩, hy⟩
      · rintro ⟨Φ, ⟨PQ, hPQ, rfl⟩, hy⟩
        exact ⟨PQ, hPQ, hy⟩
    -- Now we want to replace Φ̃ inside ∃ (last k) by the disjList.
    have hexists : (Formula.exists_ (Fin.last k) Φtilde).realization (C := C) =
        (Formula.exists_ (Fin.last k)
          (Formula.disjList (L.map fun PQ =>
            conjFormFormula PQ.1 PQ.2))).realization (C := C) := by
      show { y | ∃ c, Function.update y (Fin.last k) c ∈
          Φtilde.realization (C := C) } = _
      show _ = { y | ∃ c, Function.update y (Fin.last k) c ∈
          (Formula.disjList (L.map fun PQ =>
            conjFormFormula PQ.1 PQ.2)).realization (C := C) }
      rw [hDNF]
    rw [hexists, realization_exists_last_qfDNF hinj]

end ExistsQE

/-!
### Main theorem: Theorem 1.23

Every formula over `Fin ℓ` is `C`-equivalent to a QF formula.

The proof is by structural induction on `Φ`. The interesting cases are
`exists_` (use `existsQE`) and `forall_` (rewrite as `¬∃ ¬`, then use
`existsQE`).
-/

omit [IsAlgClosed C] in
/-- The realization of `∀ x Φ` equals the realization of `¬ ∃ x ¬ Φ`. -/
theorem realization_forall_eq_not_exists_not {k : ℕ} (x : Fin k)
    (Φ : Formula (Fin k) (FieldAtom (Fin k) D)) :
    (Formula.forall_ x Φ).realization (C := C) =
      (Formula.not (Formula.exists_ x (Formula.not Φ))).realization
        (C := C) := by
  ext y
  show (∀ c : C, Function.update y x c ∈ Φ.realization (C := C)) ↔ _
  show _ ↔ ¬ ∃ c : C, Function.update y x c ∈
    (Φ.realization (C := C))ᶜ
  simp only [Set.mem_compl_iff, not_exists, not_not]

/-- **Theorem 1.23.** Every formula over an algebraically closed field is
equivalent to a quantifier-free formula. -/
theorem theorem_1_23 [IsDomain D]
    (hinj : Function.Injective (algebraMap D C))
    {ℓ : ℕ} (Φ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D)) :
    ∃ Ψ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D),
      Ψ.IsQuantifierFree ∧
      Φ.realization (C := C) = Ψ.realization (C := C) := by
  induction Φ with
  | atom a => exact ⟨.atom a, trivial, rfl⟩
  | not Φ ih =>
    obtain ⟨Ψ, hQF, hΦ⟩ := ih
    refine ⟨Formula.not Ψ, hQF, ?_⟩
    show (Φ.realization (C := C))ᶜ = (Ψ.realization (C := C))ᶜ
    rw [hΦ]
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hQF₁, h₁⟩ := ih₁
    obtain ⟨Ψ₂, hQF₂, h₂⟩ := ih₂
    refine ⟨Formula.and Ψ₁ Ψ₂, ⟨hQF₁, hQF₂⟩, ?_⟩
    show Φ₁.realization (C := C) ∩ Φ₂.realization (C := C) =
      Ψ₁.realization (C := C) ∩ Ψ₂.realization (C := C)
    rw [h₁, h₂]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hQF₁, h₁⟩ := ih₁
    obtain ⟨Ψ₂, hQF₂, h₂⟩ := ih₂
    refine ⟨Formula.or Ψ₁ Ψ₂, ⟨hQF₁, hQF₂⟩, ?_⟩
    show Φ₁.realization (C := C) ∪ Φ₂.realization (C := C) =
      Ψ₁.realization (C := C) ∪ Ψ₂.realization (C := C)
    rw [h₁, h₂]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hQF₁, h₁⟩ := ih₁
    obtain ⟨Ψ₂, hQF₂, h₂⟩ := ih₂
    refine ⟨Formula.implies Ψ₁ Ψ₂, ⟨hQF₁, hQF₂⟩, ?_⟩
    show (Φ₁.realization (C := C))ᶜ ∪ Φ₂.realization (C := C) =
      (Ψ₁.realization (C := C))ᶜ ∪ Ψ₂.realization (C := C)
    rw [h₁, h₂]
  | exists_ i Φ ih =>
    obtain ⟨Ψ, hQF, hΦ⟩ := ih
    -- Use existsQE on the QF body.
    -- But i : Fin ℓ; existsQE needs Fin (k+1) — so cases on ℓ.
    cases ℓ with
    | zero => exact Fin.elim0 i
    | succ k =>
      obtain ⟨Ψ', hQF', hexists⟩ := existsQE (D := D) (C := C) hinj Ψ hQF i
      refine ⟨Ψ', hQF', ?_⟩
      have hΦΨ : (Formula.exists_ i Φ).realization (C := C) =
          (Formula.exists_ i Ψ).realization (C := C) := by
        show { y | ∃ c, Function.update y i c ∈ Φ.realization (C := C) } =
          { y | ∃ c, Function.update y i c ∈ Ψ.realization (C := C) }
        rw [hΦ]
      rw [hΦΨ, hexists]
  | forall_ i Φ ih =>
    obtain ⟨Ψ, hQF, hΦ⟩ := ih
    cases ℓ with
    | zero => exact Fin.elim0 i
    | succ k =>
      -- ∀ i Φ ≡ ¬ ∃ i ¬ Φ. Use ih to get QF for ¬Φ then existsQE.
      have hNotΨ : (Formula.not Ψ).IsQuantifierFree := hQF
      obtain ⟨Ψ', hQF', hexists⟩ :=
        existsQE (D := D) (C := C) hinj (Formula.not Ψ) hNotΨ i
      refine ⟨Formula.not Ψ', hQF', ?_⟩
      rw [realization_forall_eq_not_exists_not]
      show (((Formula.exists_ i (Formula.not Φ)).realization (C := C))ᶜ) =
        (Ψ'.realization (C := C))ᶜ
      congr 1
      have hnot : (Formula.not Φ).realization (C := C) =
          (Formula.not Ψ).realization (C := C) := by
        show (Φ.realization (C := C))ᶜ = (Ψ.realization (C := C))ᶜ
        rw [hΦ]
      have hexists_rewrite :
          (Formula.exists_ i (Formula.not Φ)).realization (C := C) =
          (Formula.exists_ i (Formula.not Ψ)).realization (C := C) := by
        show { y | ∃ c, Function.update y i c ∈
            (Formula.not Φ).realization (C := C) } = _
        show _ = { y | ∃ c, Function.update y i c ∈
            (Formula.not Ψ).realization (C := C) }
        rw [hnot]
      rw [hexists_rewrite, hexists]

/-!
### Corollaries 1.24 and 1.25

Two immediate consequences of Theorem 1.23.

* **Corollary 1.24** — The realisation of any formula over `C` is
  constructible. Apply Theorem 1.23 with `D := C` (the algebra map is
  the identity, hence injective), then use
  `qf_realizable_isConstructible`.

* **Corollary 1.25** — A subset of `C = C^1` defined by a formula over
  `C` is finite or cofinite. By Corollary 1.24 the set is constructible;
  Exercise 1.2 finishes.
-/

/-- **BPR Corollary 1.24.** The `C`-realisation of any formula in the
language of fields with coefficients in `C` (the algebraically closed
field itself) is constructible. -/
theorem corollary_1_24 {k : ℕ}
    (Φ : Formula (Fin k) (FieldAtom (Fin k) C)) :
    IsConstructibleSet (Φ.realization (C := C)) := by
  obtain ⟨Ψ, hΨ_qf, hΨ_real⟩ :=
    theorem_1_23 (D := C) (C := C) Function.injective_id Φ
  rw [hΨ_real]
  exact qf_realizable_isConstructible hΨ_qf

/-- **BPR Corollary 1.25.** A subset of `C` defined by a formula in the
language of fields with coefficients in `C` is finite or cofinite. -/
theorem corollary_1_25
    (Φ : Formula (Fin 1) (FieldAtom (Fin 1) C)) :
    (Φ.realization (C := C)).Finite ∨ (Φ.realization (C := C))ᶜ.Finite :=
  exercise_1_2 _ (corollary_1_24 Φ)

end Azurite.BPR
