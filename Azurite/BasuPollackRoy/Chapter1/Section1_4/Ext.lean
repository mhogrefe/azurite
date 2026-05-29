import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleQF
import Azurite.BasuPollackRoy.Chapter1.Section1_4.SentencePreservation
import Azurite.BasuPollackRoy.Chapter1.Section1_4.Theorem1_26

/-! # BPR Section 1.4 — Extension of constructible sets

> **Definition (after Theorem 1.26).** Let `C` denote an algebraically closed
> field and `C'` an algebraically closed field containing `C`. Given a
> constructible set `S ⊂ C^k`, the **extension** of `S` to `C'`, denoted
> `Ext(S, C')`, is the constructible subset of `C'^k` defined by a
> quantifier-free formula that defines `S`.

The challenge is **well-definedness**: two different quantifier-free formulas
`Ψ₁, Ψ₂` both defining `S` in `C` must give the same set in `C'`. By the
Lefschetz principle, the sentence `∀y, Ψ₁(y) ↔ Ψ₂(y)` is `C`-true (both define
`S`), so `C'`-true, so `Ψ₁` and `Ψ₂` agree in `C'` too.

This file:

* extends `qf_finZero_realization_transfer` to `Fin ℓ` sentences
  (`qf_sentence_realization_transfer`);
* defines `Ext S` via `Classical.choose` on the QF realisation;
* proves `Ext_isConstructible`;
* provides a building-block `rename_freeVars` lemma.

The full well-definedness theorem `Ext_eq_realization` requires a sentence
preservation result for `theorem_1_23_two_fields` (that the QF formula
produced by the two-field QE preserves the empty-free-variable property);
this is left for future work because it requires tracking polynomial
variables through the `projBasic` pipeline (`splitLast`, `posgcd`, `TRems`,
`leafFormula`).
-/

namespace Azurite.BPR

open MvPolynomial Polynomial Formula

/-!
### Generalized Lefschetz transfer for `Fin ℓ` sentences

We extend `qf_finZero_realization_transfer` from `Fin 0` to arbitrary `Fin ℓ`,
provided the formula has empty free-variable set (so the realization does not
depend on the choice of assignment).
-/

section SentenceTransfer

variable {C C' : Type*} [Field C] [Field C'] [Algebra C C']

/-- For a QF formula `Ψ` with `freeVars Ψ = ∅`, every atom in `Ψ` has a
polynomial with empty `vars`. -/
theorem qf_sentence_atom_vars_empty
    {ℓ : ℕ} {Ψ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) C)}
    (hQF : Ψ.IsQuantifierFree) (hSent : Ψ.freeVars = ∅) :
    ∀ a, Ψ = .atom a → a.poly.vars = ∅ := by
  induction Ψ with
  | atom a =>
    intro a' ha; cases ha
    have : a.vars = ∅ := hSent
    exact this
  | not _ _ => intro a' ha; cases ha
  | and _ _ _ _ => intro a' ha; cases ha
  | or _ _ _ _ => intro a' ha; cases ha
  | implies _ _ _ _ => intro a' ha; cases ha
  | exists_ _ _ _ => exact absurd hQF id
  | forall_ _ _ _ => exact absurd hQF id

/-- For `P ∈ MvPolynomial (Fin ℓ) D` with `P.vars = ∅` and any algebra
`D → K`, evaluation of `P` at any assignment `y : Fin ℓ → K` factors through
the constant coefficient: it equals `algebraMap D K (constantCoeff P)`. -/
theorem aeval_of_vars_empty
    {D K : Type*} [CommSemiring D] [CommSemiring K] [Algebra D K]
    {ℓ : ℕ} (P : MvPolynomial (Fin ℓ) D) (hP : P.vars = ∅) (y : Fin ℓ → K) :
    (MvPolynomial.aeval y) P = algebraMap D K (MvPolynomial.constantCoeff P) := by
  apply MvPolynomial.aeval_eq_constantCoeff_of_vars
  intro i hi
  rw [hP] at hi
  exact absurd hi (Finset.notMem_empty _)

/-- A QF formula `Ψ` over `Fin ℓ` with `freeVars Ψ = ∅` has the same truth
value (in the sense of `realization = Set.univ`) over `C` and `C'`, whenever
`algebraMap C C'` is injective. This is the `Fin ℓ` generalization of
`qf_finZero_realization_transfer`. -/
theorem qf_sentence_realization_transfer
    {ℓ : ℕ}
    (Ψ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) C))
    (hQF : Ψ.IsQuantifierFree) (hSent : Ψ.freeVars = ∅) :
    Ψ.realization (C := C) = Set.univ ↔
    Ψ.realization (C := C') = Set.univ := by
  have hAlgInj : Function.Injective (algebraMap C C') :=
    RingHom.injective (algebraMap C C')
  -- For a formula with `freeVars = ∅`, realization is constant; we test at
  -- the zero assignment.
  let y0C : Fin ℓ → C := fun _ => 0
  let y0C' : Fin ℓ → C' := fun _ => 0
  have key_C : Ψ.realization (C := C) = Set.univ ↔
      y0C ∈ Ψ.realization (C := C) := by
    constructor
    · intro h; rw [h]; trivial
    · intro h
      ext y
      simp only [Set.mem_univ, iff_true]
      exact (realization_eq_of_agree_on_freeVars Ψ y0C y
        (fun x hx => by rw [hSent] at hx; exact absurd hx (Finset.notMem_empty _))).mp h
  have key_C' : Ψ.realization (C := C') = Set.univ ↔
      y0C' ∈ Ψ.realization (C := C') := by
    constructor
    · intro h; rw [h]; trivial
    · intro h
      ext y
      simp only [Set.mem_univ, iff_true]
      exact (realization_eq_of_agree_on_freeVars Ψ y0C' y
        (fun x hx => by rw [hSent] at hx; exact absurd hx (Finset.notMem_empty _))).mp h
  rw [key_C, key_C']
  -- Now reduce to a membership statement; induct on Ψ.
  clear key_C key_C'
  induction Ψ with
  | atom a =>
    have hav : a.poly.vars = ∅ := hSent
    have hC : (MvPolynomial.aeval y0C) a.poly =
        algebraMap C C (MvPolynomial.constantCoeff a.poly) :=
      aeval_of_vars_empty a.poly hav y0C
    have hC' : (MvPolynomial.aeval y0C') a.poly =
        algebraMap C C' (MvPolynomial.constantCoeff a.poly) :=
      aeval_of_vars_empty a.poly hav y0C'
    have hC_iff : (MvPolynomial.aeval y0C) a.poly = 0 ↔
        MvPolynomial.constantCoeff a.poly = 0 := by
      rw [hC]; exact ⟨id, id⟩
    have hC'_iff : (MvPolynomial.aeval y0C') a.poly = 0 ↔
        MvPolynomial.constantCoeff a.poly = 0 := by
      rw [hC']
      exact ⟨fun h => hAlgInj (by rw [h, map_zero]),
        fun h => by rw [h, map_zero]⟩
    rcases hb : a.isEq with _ | _
    · simp only [Formula.realization, Formula.interpret_fieldAtom, hb,
        Bool.false_eq_true, if_false, Set.mem_setOf_eq]
      exact not_congr hC_iff |>.trans (not_congr hC'_iff).symm
    · simp only [Formula.realization, Formula.interpret_fieldAtom, hb,
        if_true, Set.mem_setOf_eq]
      rw [hC_iff, hC'_iff]
  | not Φ ih =>
    have hQF' : Φ.IsQuantifierFree := hQF
    have hSent' : Φ.freeVars = ∅ := hSent
    have hΦ : y0C ∈ Φ.realization (C := C) ↔
              y0C' ∈ Φ.realization (C := C') := ih hQF' hSent'
    show y0C ∈ (Φ.realization (C := C))ᶜ ↔
         y0C' ∈ (Φ.realization (C := C'))ᶜ
    simp only [Set.mem_compl_iff]
    exact not_congr hΦ
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have hS : Φ₁.freeVars ∪ Φ₂.freeVars = ∅ := hSent
    have hSent₁ : Φ₁.freeVars = ∅ := by
      have := Finset.union_eq_empty.mp hS; exact this.1
    have hSent₂ : Φ₂.freeVars = ∅ := by
      have := Finset.union_eq_empty.mp hS; exact this.2
    have h1 := ih₁ hQF₁ hSent₁
    have h2 := ih₂ hQF₂ hSent₂
    show y0C ∈ (Φ₁.realization (C := C) ∩ Φ₂.realization (C := C)) ↔
         y0C' ∈ (Φ₁.realization (C := C') ∩ Φ₂.realization (C := C'))
    simp only [Set.mem_inter_iff]
    exact and_congr h1 h2
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have hS : Φ₁.freeVars ∪ Φ₂.freeVars = ∅ := hSent
    have hSent₁ : Φ₁.freeVars = ∅ := by
      have := Finset.union_eq_empty.mp hS; exact this.1
    have hSent₂ : Φ₂.freeVars = ∅ := by
      have := Finset.union_eq_empty.mp hS; exact this.2
    have h1 := ih₁ hQF₁ hSent₁
    have h2 := ih₂ hQF₂ hSent₂
    show y0C ∈ (Φ₁.realization (C := C) ∪ Φ₂.realization (C := C)) ↔
         y0C' ∈ (Φ₁.realization (C := C') ∪ Φ₂.realization (C := C'))
    simp only [Set.mem_union]
    exact or_congr h1 h2
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have hS : Φ₁.freeVars ∪ Φ₂.freeVars = ∅ := hSent
    have hSent₁ : Φ₁.freeVars = ∅ := by
      have := Finset.union_eq_empty.mp hS; exact this.1
    have hSent₂ : Φ₂.freeVars = ∅ := by
      have := Finset.union_eq_empty.mp hS; exact this.2
    have h1 := ih₁ hQF₁ hSent₁
    have h2 := ih₂ hQF₂ hSent₂
    show y0C ∈ ((Φ₁.realization (C := C))ᶜ ∪ Φ₂.realization (C := C)) ↔
         y0C' ∈ ((Φ₁.realization (C := C'))ᶜ ∪ Φ₂.realization (C := C'))
    simp only [Set.mem_union, Set.mem_compl_iff]
    exact or_congr (not_congr h1) h2
  | exists_ _ _ _ => exact absurd hQF id
  | forall_ _ _ _ => exact absurd hQF id

end SentenceTransfer

/-!
### Definition of `Ext` and well-definedness

We define `Ext S` using `Classical.choose` on the QF formula representation of
`S`, then show it equals the realization over `C'` of any QF formula defining
`S` over `C`.
-/

section ExtDefinition

variable {C C' : Type*} [Field C] [IsAlgClosed C]
variable [Field C'] [IsAlgClosed C'] [Algebra C C']

/-- BPR's extension of a constructible set to an algebraically closed
extension field. -/
noncomputable def Ext {k : ℕ} (S : Set (Fin k → C))
    (hS : IsConstructibleSet S) : Set (Fin k → C') :=
  (constructible_isQFRealizable S hS).choose.realization (C := C')

end ExtDefinition

/-!
### Constructibility of `Ext`

Since `Ext S hS` is defined as the realization of a QF formula over `C'`, it
is automatically constructible by `qf_realizable_isConstructible`.
-/

section ExtConstructible

variable {C C' : Type*} [Field C] [IsAlgClosed C]
variable [Field C'] [IsAlgClosed C'] [Algebra C C']

open Formula in
/-- A QF formula over `Fin k` with `D`-coefficients has constructible
realization in any field `K` with an algebra structure over `D`. This is a
generalisation of `qf_realizable_isConstructible` from `Φ : Formula _ D`
realised over `D` itself to realisation over a `D`-algebra `K`. -/
theorem qf_realizable_isConstructible_algebra
    {D K : Type*} [CommRing D] [Field K] [IsAlgClosed K] [Algebra D K]
    {k : ℕ}
    {Φ : Formula (Fin k) (FieldAtom (Fin k) D)} (hqf : Φ.IsQuantifierFree) :
    IsConstructibleSet (Φ.realization (C := K)) := by
  induction Φ with
  | atom a =>
    by_cases h : a.isEq = true
    · exact .algebraic ⟨{MvPolynomial.map (algebraMap D K) a.poly}, by
        ext y; simp [Zer, realization, h, MvPolynomial.aeval_def,
          MvPolynomial.eval_map]⟩
    · have : (atom a).realization (C := K) =
          ({y | MvPolynomial.eval y
            (MvPolynomial.map (algebraMap D K) a.poly) = 0} : Set (Fin k → K))ᶜ := by
        ext y
        simp [realization, h, Set.mem_compl_iff, Set.mem_setOf_eq,
          MvPolynomial.aeval_def, MvPolynomial.eval_map]
      rw [this]
      exact .compl (.algebraic
        ⟨{MvPolynomial.map (algebraMap D K) a.poly}, by ext y; simp [Zer]⟩)
  | not Φ ih => exact .compl (ih hqf)
  | and Φ₁ Φ₂ ih₁ ih₂ => exact .inter (ih₁ hqf.1) (ih₂ hqf.2)
  | or Φ₁ Φ₂ ih₁ ih₂ => exact (ih₁ hqf.1).union (ih₂ hqf.2)
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    exact (IsConstructibleSet.compl (ih₁ hqf.1)).union (ih₂ hqf.2)
  | exists_ x Φ _ => exact absurd hqf id
  | forall_ x Φ _ => exact absurd hqf id

omit [IsAlgClosed C] in
/-- `Ext S hS` is a constructible subset of `C'^k`. -/
theorem Ext_isConstructible {k : ℕ} {S : Set (Fin k → C)}
    (hS : IsConstructibleSet S) :
    IsConstructibleSet (Ext (C' := C') S hS) := by
  unfold Ext
  exact qf_realizable_isConstructible_algebra
    (constructible_isQFRealizable S hS).choose_spec.1

end ExtConstructible

/-!
### Free-variable tracking through formula renaming

We prove `rename_freeVars`: the free variables of a renamed formula are
contained in the image of the original free variables. This is a building
block for further `freeVars`-tracking lemmas.
-/

section FreeVarsTracking

variable {D : Type*} [CommRing D]

theorem rename_freeVars [DecidableEq σ] [DecidableEq τ]
    (f : σ → τ) (Φ : Formula σ (FieldAtom σ D)) :
    (Φ.rename f (FieldAtom.renameVars f)).freeVars ⊆
      Φ.freeVars.image f := by
  induction Φ with
  | atom a =>
    simp only [Formula.rename, freeVars, FieldAtom.renameVars]
    exact MvPolynomial.vars_rename f a.poly
  | not _ ih =>
    simp only [Formula.rename, freeVars]
    exact ih
  | and _ _ ih₁ ih₂ =>
    simp only [Formula.rename, freeVars, Finset.image_union]
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ (ih₁ h)
    · exact Finset.mem_union_right _ (ih₂ h)
  | or _ _ ih₁ ih₂ =>
    simp only [Formula.rename, freeVars, Finset.image_union]
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ (ih₁ h)
    · exact Finset.mem_union_right _ (ih₂ h)
  | implies _ _ ih₁ ih₂ =>
    simp only [Formula.rename, freeVars, Finset.image_union]
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ (ih₁ h)
    · exact Finset.mem_union_right _ (ih₂ h)
  | exists_ x _ ih =>
    simp only [Formula.rename, freeVars]
    intro y hy
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hy
    obtain ⟨hy_in, hy_ne⟩ := hy
    have := ih hy_in
    rw [Finset.mem_image] at this
    obtain ⟨z, hz_in, hz_eq⟩ := this
    rw [Finset.mem_image]
    refine ⟨z, ?_, hz_eq⟩
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨hz_in, ?_⟩
    intro h
    apply hy_ne
    rw [← hz_eq, h]
  | forall_ x _ ih =>
    simp only [Formula.rename, freeVars]
    intro y hy
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hy
    obtain ⟨hy_in, hy_ne⟩ := hy
    have := ih hy_in
    rw [Finset.mem_image] at this
    obtain ⟨z, hz_in, hz_eq⟩ := this
    rw [Finset.mem_image]
    refine ⟨z, ?_, hz_eq⟩
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨hz_in, ?_⟩
    intro h
    apply hy_ne
    rw [← hz_eq, h]

end FreeVarsTracking

/-! ### Well-definedness of `Ext` -/

section ExtEqRealization

variable {C C' : Type*} [Field C] [IsAlgClosed C]
variable [Field C'] [IsAlgClosed C'] [Algebra C C']

/-- Wrap a formula with `forall_` quantifiers over an explicit list of
indices. Reading: `wrapForall [x₁,...,xₙ] Φ = ∀ x₁...∀ xₙ Φ`. -/
noncomputable def wrapForall {σ : Type*} {D : Type*} [CommRing D]
    (xs : List σ) (Φ : Formula σ (FieldAtom σ D)) :
    Formula σ (FieldAtom σ D) :=
  xs.foldr Formula.forall_ Φ

theorem wrapForall_freeVars [DecidableEq σ] {D : Type*} [CommRing D]
    (xs : List σ) (Φ : Formula σ (FieldAtom σ D)) :
    (wrapForall xs Φ).freeVars =
      Φ.freeVars \ xs.toFinset := by
  classical
  induction xs with
  | nil => simp [wrapForall, List.toFinset_nil, Finset.sdiff_empty]
  | cons x rest ih =>
    show (Formula.forall_ x (wrapForall rest Φ)).freeVars = _
    show (wrapForall rest Φ).freeVars \ {x} = _
    rw [ih]
    simp [List.toFinset_cons]
    rw [Finset.sdiff_insert]
    ext y
    simp [Finset.mem_sdiff, Finset.mem_erase]
    tauto

omit [IsAlgClosed C] in
theorem wrapForall_realization_univ_iff
    {D : Type*} [CommRing D] [Algebra D C]
    {ℓ : ℕ} (xs : List (Fin ℓ))
    (Φ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D)) :
    (wrapForall xs Φ).realization (C := C) = Set.univ ↔
    Φ.realization (C := C) = Set.univ := by
  induction xs with
  | nil => simp [wrapForall]
  | cons x rest ih =>
    show (Formula.forall_ x (wrapForall rest Φ)).realization (C := C) = Set.univ ↔ _
    show { y | ∀ c, Function.update y x c ∈
        (wrapForall rest Φ).realization (C := C) } = Set.univ ↔ _
    constructor
    · intro h
      rw [← ih]
      ext y
      simp only [Set.mem_univ, iff_true]
      have hy : y ∈ { y | ∀ c, Function.update y x c ∈
          (wrapForall rest Φ).realization (C := C) } := by
        rw [h]; trivial
      have := hy (y x)
      rwa [Function.update_eq_self] at this
    · intro h
      ext y
      simp only [Set.mem_univ, iff_true, Set.mem_setOf_eq]
      intro c
      have : Function.update y x c ∈ (wrapForall rest Φ).realization (C := C) := by
        rw [ih.mpr h]; trivial
      exact this

/-- **Well-definedness of `Ext`.** Any QF formula `Ψ` that defines `S`
over `C` produces the same set over `C'` as `Ext S hS`. -/
theorem Ext_eq_realization
    {k : ℕ} {S : Set (Fin k → C)} (hS : IsConstructibleSet S)
    {Ψ : Formula (Fin k) (FieldAtom (Fin k) C)}
    (hQF : Ψ.IsQuantifierFree)
    (hΨ : Ψ.realization (C := C) = S) :
    Ψ.realization (C := C') = Ext S hS := by
  classical
  -- Step 1: Get Ψ₀ from the constructibility witness.
  set Ψ₀ := (constructible_isQFRealizable S hS).choose with Ψ₀_def
  have hΨ₀_QF : Ψ₀.IsQuantifierFree :=
    (constructible_isQFRealizable S hS).choose_spec.1
  have hΨ₀_eq : S = Ψ₀.realization (C := C) :=
    (constructible_isQFRealizable S hS).choose_spec.2
  -- Step 2: Ξ = (Ψ ↔ Ψ₀) realized as ∧ of two implies.
  set Ξ : Formula (Fin k) (FieldAtom (Fin k) C) :=
    (Ψ.implies Ψ₀).and (Ψ₀.implies Ψ) with Ξ_def
  have hΞ_QF : Ξ.IsQuantifierFree := ⟨⟨hQF, hΨ₀_QF⟩, hΨ₀_QF, hQF⟩
  have hΞ_C : Ξ.realization (C := C) = Set.univ := by
    rw [Ξ_def]
    show ((Ψ.realization (C := C))ᶜ ∪ Ψ₀.realization (C := C)) ∩
        ((Ψ₀.realization (C := C))ᶜ ∪ Ψ.realization (C := C)) = Set.univ
    rw [hΨ, ← hΨ₀_eq]
    ext y; simp
  -- Step 3: wrapForall to form a sentence.
  set xs : List (Fin k) := (Finset.univ : Finset (Fin k)).toList with xs_def
  set Φ_sent : Formula (Fin k) (FieldAtom (Fin k) C) := wrapForall xs Ξ
    with Φ_sent_def
  have hΦ_sent_freeVars : Φ_sent.freeVars = ∅ := by
    rw [Φ_sent_def, wrapForall_freeVars]
    have : xs.toFinset = Finset.univ := by
      rw [xs_def]; simp
    rw [this]
    exact Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)
  have hinjCC : Function.Injective (algebraMap C C) := Function.injective_id
  have hinjCC' : Function.Injective (algebraMap C C') :=
    RingHom.injective (algebraMap C C')
  obtain ⟨Ψ_qe, hΨ_qe_QF, hΨ_qe_sent, hΨ_qe_C, hΨ_qe_C'⟩ :=
    theorem_1_23_two_fields_preserves_sentence
      (D := C) (C := C) (C' := C') hinjCC hinjCC' Φ_sent hΦ_sent_freeVars
  have hΦ_sent_C : Φ_sent.realization (C := C) = Set.univ :=
    (wrapForall_realization_univ_iff xs Ξ).mpr hΞ_C
  have hΨ_qe_C_univ : Ψ_qe.realization (C := C) = Set.univ := by
    rw [← hΨ_qe_C]; exact hΦ_sent_C
  have hΨ_qe_C'_univ : Ψ_qe.realization (C := C') = Set.univ :=
    (qf_sentence_realization_transfer (C := C) (C' := C') Ψ_qe
      hΨ_qe_QF hΨ_qe_sent).mp hΨ_qe_C_univ
  have hΦ_sent_C' : Φ_sent.realization (C := C') = Set.univ := by
    rw [hΨ_qe_C']; exact hΨ_qe_C'_univ
  have hΞ_C' : Ξ.realization (C := C') = Set.univ :=
    (wrapForall_realization_univ_iff xs Ξ).mp hΦ_sent_C'
  have hΨ_Ψ₀_C' : Ψ.realization (C := C') = Ψ₀.realization (C := C') := by
    have hΞ_eq : ((Ψ.realization (C := C'))ᶜ ∪ Ψ₀.realization (C := C')) ∩
        ((Ψ₀.realization (C := C'))ᶜ ∪ Ψ.realization (C := C')) = Set.univ := hΞ_C'
    have h1 : (Ψ.realization (C := C'))ᶜ ∪ Ψ₀.realization (C := C') = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      have := (Set.eq_univ_iff_forall.mp hΞ_eq) y
      exact this.1
    have h2 : (Ψ₀.realization (C := C'))ᶜ ∪ Ψ.realization (C := C') = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      have := (Set.eq_univ_iff_forall.mp hΞ_eq) y
      exact this.2
    apply Set.Subset.antisymm <;> intro y hy
    · have := (Set.eq_univ_iff_forall.mp h1) y
      rw [Set.mem_union, Set.mem_compl_iff] at this
      tauto
    · have := (Set.eq_univ_iff_forall.mp h2) y
      rw [Set.mem_union, Set.mem_compl_iff] at this
      tauto
  show Ψ.realization (C := C') = Ψ₀.realization (C := C')
  exact hΨ_Ψ₀_C'

end ExtEqRealization

/-!
### Note on well-definedness `Ext_eq_realization`

The well-definedness of `Ext`, i.e., the theorem
```
theorem Ext_eq_realization {C C' : Type*} [Field C] [IsAlgClosed C]
    [Field C'] [IsAlgClosed C'] [Algebra C C']
    {k : ℕ} {S : Set (Fin k → C)} (hS : IsConstructibleSet S)
    {Ψ : Formula (Fin k) (FieldAtom (Fin k) C)}
    (hQF : Ψ.IsQuantifierFree)
    (hΨ : Ψ.realization (C := C) = S) :
    Ψ.realization (C := C') = Ext S hS
```
follows from the chain:
1. Set `Ψ₀ := (constructible_isQFRealizable S hS).choose`. Then
   `Ψ.realization C = S = Ψ₀.realization C`.
2. Set `Ξ := (Ψ.implies Ψ₀).and (Ψ₀.implies Ψ)`, QF over `Fin k`. By 1,
   `Ξ.realization C = univ`.
3. Set `Φ_sent := wrapForall Ξ`, a sentence (`freeVars = ∅`) over `Fin k`.
   Then `Φ_sent.realization C = univ ↔ Ξ.realization C = univ` (since
   wrapping universal quantifiers over a sentence-body preserves the
   `univ`/`∅` value).
4. Apply `theorem_1_23_two_fields` to `Φ_sent`, obtaining QF `Ψ_qe` with
   `Φ_sent.realization C = Ψ_qe.realization C` and
   `Φ_sent.realization C' = Ψ_qe.realization C'`.
5. From `Φ_sent.realization C = univ`, conclude `Ψ_qe.realization C = univ`.
6. **Sentence preservation through `theorem_1_23_two_fields`:** show that
   `Ψ_qe.freeVars = ∅` (i.e., the QF formula produced by the two-field QE
   preserves the empty-free-variable property).
7. By `qf_sentence_realization_transfer` applied to `Ψ_qe`:
   `Ψ_qe.realization C' = univ`.
8. Hence `Φ_sent.realization C' = univ`, so `Ξ.realization C' = univ`, so
   `Ψ.realization C' = Ψ₀.realization C' = Ext S hS`.

Step (6) is the technical sticking point. It requires showing that the QE
algorithm in `existsQE_two_fields` does not introduce new free variables.
Concretely:
```
existsQE_two_fields_freeVars
    (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D))
    (hQF : Φ.IsQuantifierFree) (i : Fin (k+1)) :
    (existsQE_two_fields _ _ Φ hQF i).choose.freeVars ⊆ Φ.freeVars.erase i
```
This in turn requires tracking polynomial vars through `splitLast`,
`posgcd`, `TRems`, `leafFormula`, and `degNeqFormula` — substantial work
because each operation produces polynomials derived from the inputs.
-/

end Azurite.BPR
