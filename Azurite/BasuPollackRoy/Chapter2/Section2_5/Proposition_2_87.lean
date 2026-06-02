import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_82
import Azurite.BasuPollackRoy.Chapter2.Section2_3.SemialgebraicQF

/-! # BPR §2.5.3 — Extension of semialgebraic sets; Proposition 2.87

Let `R ⊆ R'` be real closed fields. The **extension** `Ext(S, R')` of a semialgebraic
set `S ⊆ Rᵏ` is the subset of `R'ᵏ` defined by the *same* quantifier-free formula that
defines `S`. The point of Proposition 2.87 is that this is **well defined**: it depends
only on the set `S`, not on the chosen formula. This is an easy consequence of the
Tarski–Seidenberg transfer principle (Theorem 2.80): if two quantifier-free formulas
`Φ₁, Φ₂` (coefficients in `R`) have the same realization over `R`, then the sentence
`∀x ((Φ₁ ⟺ Φ₂))` is true over `R`, hence over `R'` (Theorem 2.80), so `Φ₁` and `Φ₂` have
the same realization over `R'` as well.

We model `S` as `IsSemialgebraicSet S` (`S : Set (Fin k → R)`); `Ext S hS` picks a
defining quantifier-free formula via `semialgebraic_isQFRealizable` and realizes it over
`R'`. The well-definedness theorem `ext_well_defined` shows the choice does not matter,
and `ext_eq` packages it as a usable rewriting rule. From these, `Ext` preserves the
boolean operations (`ext_inter`, `ext_union`, `ext_compl`) and is monotone (`ext_mono`).
-/

open MvPolynomial

namespace Azurite.BPR

namespace Formula

/-! ### Universal closure over all coordinates of `Fin k`

The key gadget: universally closing a formula `Ψ` over *all* of `Fin k` gives a sentence
whose truth is `Ψ.realization = univ`. Applied to `(Φ₁ ⟹ Φ₂) ∧ (Φ₂ ⟹ Φ₁)`, this turns
"`Φ₁` and `Φ₂` have the same realization" into the truth of a sentence. -/

/-- The free variables of a universal closure over a list: `Φ.freeVars` minus the list. -/
theorem freeVars_forallList {σ α : Type*} [AtomVars α σ] [DecidableEq σ]
    (L : List σ) (Φ : Formula σ α) :
    (Formula.forallList L Φ).freeVars = Φ.freeVars \ L.toFinset := by
  induction L with
  | nil => simp [Formula.forallList]
  | cons x rest ih =>
    show (Formula.forall_ x (Formula.forallList rest Φ)).freeVars = _
    show (Formula.forallList rest Φ).freeVars \ {x} = _
    rw [ih, List.toFinset_cons]
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
    tauto

/-- Universally closing over all of `Fin k` yields a sentence. -/
theorem isSentence_forallList_finRange {k : ℕ} {α : Type*} [AtomVars α (Fin k)]
    (Φ : Formula (Fin k) α) :
    Formula.isSentence (Formula.forallList (List.finRange k) Φ) := by
  rw [Formula.isSentence, freeVars_forallList]
  have huniv : (List.finRange k).toFinset = (Finset.univ : Finset (Fin k)) := by
    ext i; simp
  rw [huniv]
  exact Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)

/-- The realization of the universal closure over all coordinates is `univ` exactly when
the inner realization is `univ`. -/
theorem realization_forallList_finRange_univ_iff {k : ℕ} {α : Type*} {C : Type*}
    [AtomRealization α (Fin k) C] (Φ : Formula (Fin k) α) :
    (Formula.forallList (List.finRange k) Φ).realization (C := C) = Set.univ ↔
      Φ.realization (C := C) = Set.univ := by
  rw [Formula.realization_forallList, Set.eq_univ_iff_forall, Set.eq_univ_iff_forall]
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h v; exact h v v (fun s hs => absurd (List.mem_finRange s) hs)
  · intro h _ v _; exact h v

/-- The biconditional `(Φ₁ ⟹ Φ₂) ∧ (Φ₂ ⟹ Φ₁)` has realization `univ` exactly when `Φ₁`
and `Φ₂` have the same realization. -/
theorem and_implies_realization_univ_iff {k : ℕ} {α : Type*} {C : Type*}
    [AtomRealization α (Fin k) C] (Φ₁ Φ₂ : Formula (Fin k) α) :
    ((Φ₁.implies Φ₂).and (Φ₂.implies Φ₁)).realization (C := C) = Set.univ ↔
      Φ₁.realization (C := C) = Φ₂.realization (C := C) := by
  simp only [Formula.realization]
  rw [Set.eq_univ_iff_forall, Set.ext_iff]
  refine forall_congr' fun y => ?_
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
  tauto

/-- The universal closure of `(Φ₁ ⟹ Φ₂) ∧ (Φ₂ ⟹ Φ₁)` is true (over `C`) exactly when
`Φ₁` and `Φ₂` realize the same set over `C`. -/
theorem closure_isTrue_iff_eq {k : ℕ} {α : Type*} {C : Type*}
    [AtomRealization α (Fin k) C] (Φ₁ Φ₂ : Formula (Fin k) α) :
    (Formula.forallList (List.finRange k)
        ((Φ₁.implies Φ₂).and (Φ₂.implies Φ₁))).IsTrue (C := C) ↔
      Φ₁.realization (C := C) = Φ₂.realization (C := C) := by
  unfold Formula.IsTrue
  rw [realization_forallList_finRange_univ_iff, and_implies_realization_univ_iff]

end Formula

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

/-- **Well-definedness of the extension (the heart of Proposition 2.87).** If two formulas
(coefficients in `R`) realize the same set over `R`, they realize the same set over `R'`.
Proof: the sentence `∀x ((Φ₁ ⟹ Φ₂) ∧ (Φ₂ ⟹ Φ₁))` is true over `R`, hence over `R'` by the
Tarski–Seidenberg transfer principle (Theorem 2.80). -/
theorem ext_well_defined {k : ℕ}
    (Φ₁ Φ₂ : Formula (Fin k) (OrderedFieldAtom (Fin k) R))
    (h : Φ₁.realization (C := R) = Φ₂.realization (C := R)) :
    Φ₁.realization (C := R') = Φ₂.realization (C := R') := by
  have hsent : Formula.isSentence (Formula.forallList (List.finRange k)
      ((Φ₁.implies Φ₂).and (Φ₂.implies Φ₁))) :=
    Formula.isSentence_forallList_finRange _
  have h80 := theorem_2_80 (R := R) (R' := R') (Formula.forallList (List.finRange k)
      ((Φ₁.implies Φ₂).and (Φ₂.implies Φ₁))) hsent
  rw [Formula.closure_isTrue_iff_eq (C := R), Formula.closure_isTrue_iff_eq (C := R')] at h80
  exact h80.mp h

/-- **`Ext(S, R')`**, the extension of a semialgebraic set `S ⊆ Rᵏ` to `R'`: the realization
over `R'` of a quantifier-free formula (with coefficients in `R`) defining `S`. -/
noncomputable def extension {k : ℕ} (S : Set (Fin k → R)) (hS : IsSemialgebraicSet S) :
    Set (Fin k → R') :=
  (semialgebraic_isQFRealizable S hS).choose.realization (C := R')

/-- **Characterization of `Ext` (well-definedness, usable form).** For *any* quantifier-free
formula `Φ` (coefficients in `R`) defining `S`, `Ext S` is the realization of `Φ` over `R'`.
This is exactly the statement that `Ext` does not depend on the chosen formula. -/
theorem ext_eq {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)} (hΦ : S = Φ.realization (C := R)) :
    extension (R' := R') S hS = Φ.realization (C := R') := by
  show (semialgebraic_isQFRealizable S hS).choose.realization (C := R') = Φ.realization (C := R')
  exact ext_well_defined _ Φ
    ((semialgebraic_isQFRealizable S hS).choose_spec.2.symm.trans hΦ)

/-- **`Ext(S, R') ∩ Rᵏ = S`** (pointwise). A point of `Rᵏ`, embedded into `R'ᵏ` via
`algebraMap R R'`, lies in `Ext S` iff it already lies in `S`. This is the transfer of
quantifier-free realizations along the order-preserving embedding `R ↪ R'`
(`qf_realization_transfer`): restricting the extension back to `Rᵏ` recovers `S`. -/
theorem mem_ext_algebraMap {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    (y : Fin k → R) :
    (algebraMap R R' ∘ y) ∈ extension (R' := R') S hS ↔ y ∈ S := by
  obtain ⟨Φ, hqf, hSeq⟩ := semialgebraic_isQFRealizable S hS
  rw [ext_eq hS hSeq, ← qf_realization_transfer Φ hqf y, ← hSeq]

/-- **`Ext(S, R') ∩ Rᵏ = S`** (as a preimage). Pulling `Ext S` back along the embedding
`Rᵏ ↪ R'ᵏ` recovers `S`. Note this does *not* characterize `Ext S`: other semialgebraic
subsets of `R'ᵏ` can have the same intersection with `Rᵏ` (e.g. for `S = [0,4]` over the
real algebraic numbers, `[0, π) ∪ (π, 4]` also meets `Rᵏ` in `S`). -/
theorem ext_preimage_algebraMap {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    (fun y : Fin k → R => algebraMap R R' ∘ y) ⁻¹' extension (R' := R') S hS = S := by
  ext y; exact mem_ext_algebraMap hS y

/-- The formula `X₀ ≥ 0 ∧ 4 − X₀ ≥ 0` (coefficients in `F`) realizes the interval `[0,4]`
over any ordered extension field `C'`. -/
theorem mem_interval_formula {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {C' : Type*} [Field C'] [LinearOrder C'] [IsStrictOrderedRing C'] [Algebra F C']
    (y : Fin 1 → C') :
    y ∈ ((Formula.atom (⟨MvPolynomial.X 0, OrderRel.ge⟩ : OrderedFieldAtom (Fin 1) F)).and
        (Formula.atom ⟨MvPolynomial.C 4 - MvPolynomial.X 0, OrderRel.ge⟩)).realization (C := C')
      ↔ (0 ≤ y 0 ∧ y 0 ≤ 4) := by
  simp only [Formula.realization, AtomRealization.interpret, Set.mem_inter_iff,
    Set.mem_setOf_eq, MvPolynomial.aeval_X, map_sub, map_ofNat, ge_iff_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-- **Non-uniqueness of the extension (BPR's remark following Proposition 2.87).** The
identity `Ext(S, R') ∩ Rᵏ = S` does *not* characterize `Ext(S, R')`. Concretely, for
`S = [0,4]` and any `t ∈ R'` outside the image of `R` with `0 < t < 4`, the punctured
interval `[0,4] ∖ {t}` is a *different* semialgebraic subset of `R'` with the *same* trace
`S` on `R` (the embedded `Rᵏ`). (BPR's instance: `R = R_alg`, `R' = R`, `t = π`.) -/
theorem ext_not_unique (t : R') (ht : ∀ y : R, algebraMap R R' y ≠ t)
    (ht0 : 0 < t) (ht4 : t < 4) :
    ∃ (S : Set (Fin 1 → R)) (hS : IsSemialgebraicSet S) (T' : Set (Fin 1 → R')),
      IsSemialgebraicSet T' ∧
      (fun y : Fin 1 → R => algebraMap R R' ∘ y) ⁻¹' T' = S ∧
      T' ≠ extension (R' := R') S hS := by
  classical
  -- the formula `X₀ ≥ 0 ∧ 4 − X₀ ≥ 0` defining `[0,4]`.
  set Φ : Formula (Fin 1) (OrderedFieldAtom (Fin 1) R) :=
    (Formula.atom ⟨MvPolynomial.X 0, OrderRel.ge⟩).and
      (Formula.atom ⟨MvPolynomial.C 4 - MvPolynomial.X 0, OrderRel.ge⟩) with hΦdef
  have hqf : Φ.IsQuantifierFree := ⟨trivial, trivial⟩
  set S : Set (Fin 1 → R) := Φ.realization (C := R) with hSdef
  have hS : IsSemialgebraicSet S := qfRealizable_isSemialgebraic hqf
  have hExt : extension (R' := R') S hS = Φ.realization (C := R') := ext_eq hS hSdef
  have hExtSemialg : IsSemialgebraicSet (extension (R' := R') S hS) := by
    rw [hExt]
    exact IsSemialgebraicSet.of_definedOver (D := R) (qfRealizable_isSemialgebraicSetOver hqf)
  -- the witness: the punctured interval `[0,4] ∖ {t}`.
  set T' : Set (Fin 1 → R') := extension (R' := R') S hS ∩ {y | y 0 ≠ t} with hTdef
  have hzero : IsSemialgebraicSet {y : Fin 1 → R' | y 0 = t} := by
    have heq : {y : Fin 1 → R' | y 0 = t}
        = {y | MvPolynomial.eval y (MvPolynomial.X 0 - MvPolynomial.C t) = 0} := by
      ext y; simp [sub_eq_zero]
    rw [heq]; exact IsSemialgebraicSet.eqZero _
  have hT' : IsSemialgebraicSet T' := by
    refine hExtSemialg.inter ?_
    have heq : {y : Fin 1 → R' | y 0 ≠ t} = {y : Fin 1 → R' | y 0 = t}ᶜ := by ext y; simp
    rw [heq]; exact hzero.compl
  refine ⟨S, hS, T', hT', ?_, ?_⟩
  · -- the trace of `T'` on `R` is `S`
    rw [hTdef, Set.preimage_inter, ext_preimage_algebraMap hS]
    have huniv : (fun y : Fin 1 → R => algebraMap R R' ∘ y) ⁻¹' {y : Fin 1 → R' | y 0 ≠ t}
        = Set.univ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Function.comp_apply, Set.mem_univ, iff_true]
      exact ht (y 0)
    rw [huniv, Set.inter_univ]
  · -- `T'` differs from `Ext S`: the point `t` lies in `Ext S = [0,4]` but not in `T'`
    have hp_ext : (fun _ => t) ∈ extension (R' := R') S hS := by
      rw [hExt, hΦdef]; exact (mem_interval_formula _).mpr ⟨ht0.le, ht4.le⟩
    have hp_not : (fun _ => t) ∉ T' := by
      rw [hTdef]; rintro ⟨_, h2⟩; exact h2 rfl
    exact fun h => hp_not (by rw [h]; exact hp_ext)

/-- `Ext` depends only on the underlying set (not on the semialgebraicity proof). -/
theorem ext_congr {k : ℕ} {S S' : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) (hS' : IsSemialgebraicSet S') (h : S = S') :
    extension (R' := R') S hS = extension (R' := R') S' hS' := by
  obtain ⟨Φ, _, hSeq⟩ := semialgebraic_isQFRealizable S hS
  rw [ext_eq hS hSeq, ext_eq hS' (h ▸ hSeq)]

/-- **`Ext` preserves intersection.** -/
theorem ext_inter {k : ℕ} {S T : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) :
    extension (R' := R') (S ∩ T) (hS.inter hT) = extension (R' := R') S hS ∩ extension (R' := R') T hT := by
  obtain ⟨ΦS, _, hSeq⟩ := semialgebraic_isQFRealizable S hS
  obtain ⟨ΦT, _, hTeq⟩ := semialgebraic_isQFRealizable T hT
  rw [ext_eq hS hSeq, ext_eq hT hTeq,
      ext_eq (hS.inter hT) (Φ := ΦS.and ΦT) (by rw [hSeq, hTeq]; rfl)]
  rfl

/-- **`Ext` preserves union.** -/
theorem ext_union {k : ℕ} {S T : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) :
    extension (R' := R') (S ∪ T) (hS.union hT) = extension (R' := R') S hS ∪ extension (R' := R') T hT := by
  obtain ⟨ΦS, _, hSeq⟩ := semialgebraic_isQFRealizable S hS
  obtain ⟨ΦT, _, hTeq⟩ := semialgebraic_isQFRealizable T hT
  rw [ext_eq hS hSeq, ext_eq hT hTeq,
      ext_eq (hS.union hT) (Φ := ΦS.or ΦT) (by rw [hSeq, hTeq]; rfl)]
  rfl

/-- **`Ext` preserves complementation.** -/
theorem ext_compl {k : ℕ} {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    extension (R' := R') Sᶜ hS.compl = (extension (R' := R') S hS)ᶜ := by
  obtain ⟨ΦS, _, hSeq⟩ := semialgebraic_isQFRealizable S hS
  rw [ext_eq hS hSeq, ext_eq hS.compl (Φ := ΦS.not) (by rw [hSeq]; rfl)]
  rfl

/-- **`Ext` is monotone.** -/
theorem ext_mono {k : ℕ} {S T : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) (hsub : S ⊆ T) :
    extension (R' := R') S hS ⊆ extension (R' := R') T hT := by
  have hI : extension (R' := R') S hS = extension (R' := R') S hS ∩ extension (R' := R') T hT := by
    rw [← ext_inter hS hT]
    exact ext_congr hS (hS.inter hT) (Set.inter_eq_left.mpr hsub).symm
  intro x hx
  rw [hI] at hx
  exact hx.2

/-- **BPR Proposition 2.87.** The extension `Ext(·, R')` of semialgebraic subsets of `Rᵏ`
is well defined (depends only on the set, `ext_well_defined`), preserves the boolean
operations (intersection, union, complementation), and is monotone. -/
theorem proposition_2_87 {k : ℕ} {S T : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) :
    extension (R' := R') (S ∩ T) (hS.inter hT) = extension (R' := R') S hS ∩ extension (R' := R') T hT ∧
    extension (R' := R') (S ∪ T) (hS.union hT) = extension (R' := R') S hS ∪ extension (R' := R') T hT ∧
    extension (R' := R') Sᶜ hS.compl = (extension (R' := R') S hS)ᶜ ∧
    (S ⊆ T → extension (R' := R') S hS ⊆ extension (R' := R') T hT) :=
  ⟨ext_inter hS hT, ext_union hS hT, ext_compl hS, fun h => ext_mono hS hT h⟩

end Azurite.BPR
