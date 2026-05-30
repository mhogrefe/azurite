import Azurite.BasuPollackRoy.Chapter2.Section2_3.BasicSemialgebraicSets
import Azurite.BasuPollackRoy.Chapter2.Section2_3.OrderedFieldFormula
import Mathlib.Data.Sign.Defs

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

open Formula in
/-- Over-`D` variant of the QF → semialgebraic bridge. A
quantifier-free formula with `D`-coefficient atomic witnesses has
semialgebraic-over-`D` realisation. -/
theorem qfRealizable_isSemialgebraicSetOver
    {D : Type*} [CommRing D] [Algebra D R]
    {Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) D)}
    (hqf : Φ.IsQuantifierFree) :
    IsSemialgebraicSetOver D (Φ.realization (C := R)) := by
  induction Φ with
  | atom a =>
    obtain ⟨P, rel⟩ := a
    cases rel
    · exact IsSemialgebraicSetOver.eqZero (R := R) P
    · exact IsSemialgebraicSetOver.neZero (R := R) P
    · exact IsSemialgebraicSetOver.ltZero (R := R) P
    · exact IsSemialgebraicSetOver.gtZero (R := R) P
    · exact IsSemialgebraicSetOver.leZero (R := R) P
    · exact IsSemialgebraicSetOver.geZero (R := R) P
  | not _ ih => exact (ih hqf).compl
  | and _ _ ih₁ ih₂ => exact (ih₁ hqf.1).inter (ih₂ hqf.2)
  | or _ _ ih₁ ih₂ => exact (ih₁ hqf.1).union (ih₂ hqf.2)
  | implies _ _ ih₁ ih₂ =>
    exact ((ih₁ hqf.1).compl).union (ih₂ hqf.2)
  | exists_ _ _ _ => exact absurd hqf id
  | forall_ _ _ _ => exact absurd hqf id

/-- A subset of `R^k` is semialgebraic iff it is the realization of a
quantifier-free formula over ordered field atoms. -/
theorem semialgebraic_iff_qfRealizable
    (V : Set (Fin k → R)) :
    IsSemialgebraicSet V ↔
    ∃ Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R),
      Φ.IsQuantifierFree ∧ V = Φ.realization (C := R) :=
  ⟨semialgebraic_isQFRealizable V,
   fun ⟨_, hqf, hV⟩ => hV ▸ qfRealizable_isSemialgebraic hqf⟩

/-! ### Sign-condition formulas.

Sign-condition formulas package atomic sign assertions on polynomials
into QF formulas over the ordered-field-atom language. They are the
building blocks of the BPR Theorem 2.62 proof: the leaves of
`TRems(P, ∂P/∂X)` ultimately produce a list of (polynomial, sign)
pairs whose conjunction is a basic semialgebraic-over-`D` cell on `R^k`.
-/

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]

/-- For a polynomial `P` and a sign `s ∈ {0, +1, -1}`, the QF atomic
formula asserting that `aeval y P` has sign `s`. -/
noncomputable def signAtom (P : MvPolynomial σ D) (s : SignType) :
    Formula σ (OrderedFieldAtom σ D) :=
  match s with
  | .zero => eqZeroO P
  | .pos => gtZeroO P
  | .neg => ltZeroO P

theorem signAtom_isQF (P : MvPolynomial σ D) (s : SignType) :
    (signAtom P s).IsQuantifierFree := by
  cases s <;> trivial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R]

@[simp] theorem realization_signAtom [DecidableEq σ]
    (P : MvPolynomial σ D) (s : SignType) :
    (signAtom P s).realization (C := R) =
      { y | SignType.sign (MvPolynomial.aeval y P) = s } := by
  cases s
  · ext y; simp [signAtom, sign_eq_zero_iff]
  · ext y; simp [signAtom, sign_eq_neg_one_iff]
  · ext y; simp [signAtom, sign_eq_one_iff]

/-- For a list of `(polynomial, sign)` pairs, the QF formula asserting
that each polynomial has the prescribed sign at `y`. The empty list
produces the trivially-true formula `eqZeroO 0`. -/
noncomputable def signCondFormula :
    List (MvPolynomial σ D × SignType) → Formula σ (OrderedFieldAtom σ D)
  | [] => eqZeroO 0
  | (P, s) :: rest => .and (signAtom P s) (signCondFormula rest)

theorem signCondFormula_isQF
    (l : List (MvPolynomial σ D × SignType)) :
    (signCondFormula l).IsQuantifierFree := by
  induction l with
  | nil => trivial
  | cons head rest ih =>
    exact ⟨signAtom_isQF head.1 head.2, ih⟩

theorem signCondFormula_realization [DecidableEq σ]
    (l : List (MvPolynomial σ D × SignType)) :
    (signCondFormula l).realization (C := R) =
      { y | ∀ ps ∈ l, SignType.sign (MvPolynomial.aeval y ps.1) = ps.2 } := by
  induction l with
  | nil =>
    ext y; simp [signCondFormula]
  | cons head rest ih =>
    ext y
    simp only [signCondFormula, realization, Set.mem_inter_iff,
      Set.mem_setOf_eq, List.mem_cons]
    rw [realization_signAtom]
    rw [show (signCondFormula rest).realization (C := R) =
      { y | ∀ ps ∈ rest, SignType.sign (MvPolynomial.aeval y ps.1) = ps.2 }
      from ih]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hhead, hrest⟩ ps hps
      rcases hps with rfl | hps
      · exact hhead
      · exact hrest ps hps
    · intro h
      exact ⟨h head (Or.inl rfl), fun ps hps => h ps (Or.inr hps)⟩

end Formula

/-! ### Ordered-field-atom disjunction list. -/

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]

/-- Disjunction of a list of ordered-field formulas; empty list yields
the ordered-field contradiction `ltZeroO 1` (which realises to `∅`). -/
noncomputable def disjListO :
    List (Formula σ (OrderedFieldAtom σ D)) → Formula σ (OrderedFieldAtom σ D)
  | [] => ltZeroO 1
  | Φ :: Φs => .or Φ (disjListO Φs)

theorem disjListO_isQF
    (Φs : List (Formula σ (OrderedFieldAtom σ D)))
    (h : ∀ Φ ∈ Φs, Φ.IsQuantifierFree) :
    (disjListO Φs).IsQuantifierFree := by
  induction Φs with
  | nil => trivial
  | cons Φ rest ih =>
    refine ⟨h Φ List.mem_cons_self, ih ?_⟩
    intro φ hφ; exact h φ (List.mem_cons_of_mem _ hφ)

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R]

@[simp] theorem realization_disjListO [DecidableEq σ]
    (Φs : List (Formula σ (OrderedFieldAtom σ D))) :
    (disjListO Φs).realization (C := R) =
      { y | ∃ Φ ∈ Φs, y ∈ Φ.realization (C := R) } := by
  induction Φs with
  | nil =>
    ext y; simp [disjListO]
  | cons Φ Φs ih =>
    show (Φ.or (disjListO Φs)).realization (C := R) = _
    rw [show (Φ.or (disjListO Φs)).realization (C := R) =
            Φ.realization (C := R) ∪ (disjListO Φs).realization (C := R)
            from rfl, ih]
    ext y
    simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons]
    constructor
    · rintro (h | ⟨φ, hφ_mem, hφ⟩)
      · exact ⟨Φ, Or.inl rfl, h⟩
      · exact ⟨φ, Or.inr hφ_mem, hφ⟩
    · rintro ⟨φ, hφ_mem, hφ⟩
      rcases hφ_mem with rfl | hφ_mem
      · exact Or.inl hφ
      · exact Or.inr ⟨φ, hφ_mem, hφ⟩

end Formula

/-! ### FieldAtom → OrderedFieldAtom translation.

To reuse Chapter 1's leaf-formula machinery in the ordered setting we
translate `FieldAtom` formulas (equalities and disequalities only) to
`OrderedFieldAtom` formulas: `eq → .eq`, `ne → .ne`. The six atomic
relations of `OrderedFieldAtom` strictly extend the two of `FieldAtom`,
so this is a faithful embedding.
-/

/-- Translate a `FieldAtom` to an `OrderedFieldAtom`: equality maps to
`.eq`, disequality maps to `.ne`. -/
def FieldAtom.toOrderedFieldAtom {σ : Type*} {D : Type*} [CommRing D]
    (a : FieldAtom σ D) : OrderedFieldAtom σ D :=
  ⟨a.poly, if a.isEq then OrderRel.eq else OrderRel.ne⟩

namespace Formula

variable {σ α β : Type*}

/-- `mapAtom` preserves the QF property: it doesn't introduce
quantifiers. -/
theorem mapAtom_isQF (f : α → β) (Φ : Formula σ α) :
    (Φ.mapAtom f).IsQuantifierFree ↔ Φ.IsQuantifierFree := by
  induction Φ with
  | atom _ => simp [mapAtom, IsQuantifierFree]
  | not _ ih => simp [mapAtom, IsQuantifierFree, ih]
  | and _ _ ih₁ ih₂ => simp [mapAtom, IsQuantifierFree, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [mapAtom, IsQuantifierFree, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ => simp [mapAtom, IsQuantifierFree, ih₁, ih₂]
  | exists_ _ _ _ => simp [mapAtom, IsQuantifierFree]
  | forall_ _ _ _ => simp [mapAtom, IsQuantifierFree]

end Formula

/-! ### Realisation preservation under `FieldAtom → OrderedFieldAtom`. -/

/-- The realisation of a `FieldAtom` formula equals the realisation of
its `OrderedFieldAtom` translation: the two atom types agree at
equality and disequality, and the translation only re-routes between
them. -/
@[simp] theorem Formula.realization_mapAtom_toOrderedFieldAtom
    {σ : Type*} [DecidableEq σ]
    {D : Type*} [CommRing D]
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Algebra D R]
    (Φ : Formula σ (FieldAtom σ D)) :
    (Φ.mapAtom FieldAtom.toOrderedFieldAtom).realization (C := R) =
      Φ.realization (C := R) := by
  induction Φ with
  | atom a =>
    show (Formula.atom (FieldAtom.toOrderedFieldAtom a)).realization (C := R) =
          (Formula.atom a).realization (C := R)
    cases h : a.isEq
    · have h_atom_eq : FieldAtom.toOrderedFieldAtom a =
          ⟨a.poly, OrderRel.ne⟩ := by
        simp [FieldAtom.toOrderedFieldAtom, h]
      rw [h_atom_eq]
      show ({y : σ → R | MvPolynomial.aeval y a.poly ≠ 0} : Set _) =
            AtomRealization.interpret a
      show _ = (if a.isEq then _ else _)
      rw [h]; rfl
    · have h_atom_eq : FieldAtom.toOrderedFieldAtom a =
          ⟨a.poly, OrderRel.eq⟩ := by
        simp [FieldAtom.toOrderedFieldAtom, h]
      rw [h_atom_eq]
      show ({y : σ → R | MvPolynomial.aeval y a.poly = 0} : Set _) =
            AtomRealization.interpret a
      show _ = (if a.isEq then _ else _)
      rw [h]; rfl
  | not Φ ih =>
    show ((Φ.mapAtom _).not).realization (C := R) = _
    simp only [Formula.realization_not, ih]
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    show ((Φ₁.mapAtom _).and (Φ₂.mapAtom _)).realization (C := R) = _
    simp only [Formula.realization_and, ih₁, ih₂]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    show ((Φ₁.mapAtom _).or (Φ₂.mapAtom _)).realization (C := R) = _
    simp only [Formula.realization_or, ih₁, ih₂]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    change (Φ₁.mapAtom _).realizationᶜ ∪ (Φ₂.mapAtom _).realization =
           Φ₁.realizationᶜ ∪ Φ₂.realization
    rw [ih₁, ih₂]
  | exists_ x Φ ih =>
    change {y : σ → R | ∃ c : R, Function.update y x c ∈
              (Φ.mapAtom _).realization} = _
    ext y
    simp only [Set.mem_setOf_eq, ih]
    rfl
  | forall_ x Φ ih =>
    change {y : σ → R | ∀ c : R, Function.update y x c ∈
              (Φ.mapAtom _).realization} = _
    ext y
    simp only [Set.mem_setOf_eq, ih]
    rfl

/-- A sign-condition realisation over `D` is semialgebraic over `D`. -/
theorem isSemialgebraicSetOver_signCondLocus
    {D : Type*} [CommRing D] [Algebra D R]
    (l : List (MvPolynomial (Fin k) D × SignType)) :
    IsSemialgebraicSetOver D
      ({ y : Fin k → R |
          ∀ ps ∈ l, SignType.sign (MvPolynomial.aeval y ps.1) = ps.2 }) := by
  rw [← Formula.signCondFormula_realization l]
  exact qfRealizable_isSemialgebraicSetOver
    (Formula.signCondFormula_isQF l)

end Azurite.BPR
