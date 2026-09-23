import Azurite.BasuPollackRoy.Chapter1.Section1_1.Sentences
import Azurite.BasuPollackRoy.Chapter1.Section1_4.SentencePreservation
import Azurite.BasuPollackRoy.Chapter1.Section1_4.Theorem1_23
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod

/-! # BPR Section 1.4 — Theorem 1.26: Lefschetz principle

> **Theorem 1.26** (Lefschetz principle).
> Let `C ⊂ C'` be an inclusion of algebraically closed fields. If `Φ` is a
> sentence in the language of fields with coefficients in `C`, then `Φ` is
> true in `C` if and only if it is true in `C'`.

**Proof outline** (BPR). By Theorem 1.23, there is a quantifier-free formula
`Ψ` that is `C`-equivalent to `Φ`. The proof of Theorem 1.22 (and hence of
Theorem 1.23) is *uniform* in the algebraically closed field: the SAME `Ψ` is
also `C'`-equivalent to `Φ`. Because `Φ` is a sentence over `Fin 0`, the only
assignment to evaluate at is `Fin.elim0`. Injectivity of `algebraMap C C'`
(a ring map from a field is injective) lets atoms `c = 0`/`c ≠ 0` transfer
between the fields.

The key technical input is a **two-field** version of Theorem 1.23, which
exhibits the same `Ψ` working over two fields simultaneously.
-/

namespace Azurite.BPR

open _root_.Azurite.BPR.MvPolynomial Polynomial Formula

variable {D : Type*} [CommRing D]

/-!
### Two-field existential QE

The constructions `qfDNFAux`, `projBasic`, and the swap-based reduction are
all *deterministic*: they produce the same candidate formula `Ψ` regardless
of which algebraically closed field we evaluate over. The correctness proofs
depend on `hinj : Function.Injective (algebraMap D C)`, but we can simply
apply them twice (once per field) to obtain a uniform witness.
-/

section TwoFieldExistsQE

variable {C C' : Type*} [Field C] [Field C'] [IsAlgClosed C] [IsAlgClosed C']
variable [Algebra D C] [Algebra D C']
variable [IsDomain D]

/-- **Two-field existential QE.** Given a QF formula `Φ` and a variable `i`,
there is a *single* QF formula `Ψ` whose realisation agrees with that of
`∃ i Φ` over BOTH `C` and `C'`. -/
theorem existsQE_two_fields
    (hinj : Function.Injective (algebraMap D C))
    (hinj' : Function.Injective (algebraMap D C'))
    {k : ℕ} (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D))
    (hQF : Φ.IsQuantifierFree) (i : Fin (k+1)) :
    ∃ Ψ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D),
      Ψ.IsQuantifierFree ∧
      (Formula.exists_ i Φ).realization (C := C) =
        Ψ.realization (C := C) ∧
      (Formula.exists_ i Φ).realization (C := C') =
        Ψ.realization (C := C') := by
  set s : Fin (k+1) → Fin (k+1) :=
    ((Equiv.swap i (Fin.last k) : Equiv.Perm (Fin (k+1))) :
      Fin (k+1) → Fin (k+1))
  have hs_inj : Function.Injective s := (Equiv.swap i (Fin.last k)).injective
  set Φtilde : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D) :=
    Φ.rename s (FieldAtom.renameVars s)
  have hQF_tilde : Φtilde.IsQuantifierFree :=
    Formula.rename_isQF _ _ _ hQF
  set L := qfDNFAux (D := D) true Φtilde
  set Ψ_inner : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D) :=
    Formula.disjList (L.map fun PQ =>
      (projBasic PQ.1 PQ.2).rename Fin.castSucc
        (FieldAtom.renameVars Fin.castSucc))
  refine ⟨Ψ_inner.rename s (FieldAtom.renameVars s), ?_, ?_, ?_⟩
  · exact Formula.rename_isQF _ _ _ (disjList_qe_isQF L)
  · rw [realization_exists_swap (D := D) (C := C) i Φ]
    rw [Formula.rename_realization s hs_inj]
    congr 1
    show (Formula.exists_ (Fin.last k) Φtilde).realization (C := C) =
      Ψ_inner.realization (C := C)
    have hDNF : Φtilde.realization (C := C) =
        (Formula.disjList (L.map fun PQ =>
          conjFormFormula PQ.1 PQ.2)).realization (C := C) := by
      rw [qfDNF_realization _ hQF_tilde, Formula.realization_disjList]
      ext y
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, List.mem_map]
      constructor
      · rintro ⟨PQ, hPQ, hy⟩
        exact ⟨_, ⟨PQ, hPQ, rfl⟩, hy⟩
      · rintro ⟨Φ, ⟨PQ, hPQ, rfl⟩, hy⟩
        exact ⟨PQ, hPQ, hy⟩
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
  · rw [realization_exists_swap (D := D) (C := C') i Φ]
    rw [Formula.rename_realization s hs_inj]
    congr 1
    show (Formula.exists_ (Fin.last k) Φtilde).realization (C := C') =
      Ψ_inner.realization (C := C')
    have hDNF : Φtilde.realization (C := C') =
        (Formula.disjList (L.map fun PQ =>
          conjFormFormula PQ.1 PQ.2)).realization (C := C') := by
      rw [qfDNF_realization _ hQF_tilde, Formula.realization_disjList]
      ext y
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, List.mem_map]
      constructor
      · rintro ⟨PQ, hPQ, hy⟩
        exact ⟨_, ⟨PQ, hPQ, rfl⟩, hy⟩
      · rintro ⟨Φ, ⟨PQ, hPQ, rfl⟩, hy⟩
        exact ⟨PQ, hPQ, hy⟩
    have hexists : (Formula.exists_ (Fin.last k) Φtilde).realization (C := C') =
        (Formula.exists_ (Fin.last k)
          (Formula.disjList (L.map fun PQ =>
            conjFormFormula PQ.1 PQ.2))).realization (C := C') := by
      show { y | ∃ c, Function.update y (Fin.last k) c ∈
          Φtilde.realization (C := C') } = _
      show _ = { y | ∃ c, Function.update y (Fin.last k) c ∈
          (Formula.disjList (L.map fun PQ =>
            conjFormFormula PQ.1 PQ.2)).realization (C := C') }
      rw [hDNF]
    rw [hexists, realization_exists_last_qfDNF hinj']

/-- **Two-field existential QE preserves sentence property.** Slightly
more general: if `Φ.freeVars ⊆ {i}`, then `existsQE_two_fields` produces
a sentence (the quantified variable is eliminated, so any remaining
free variable would be `i`, but since we quantify over `i`, the result
has `freeVars = ∅`). Special case `Φ.freeVars = ∅` gives the sentence
preservation. -/
theorem existsQE_two_fields_preserves_sentence
    (hinj : Function.Injective (algebraMap D C))
    (hinj' : Function.Injective (algebraMap D C'))
    {k : ℕ} (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D))
    (hQF : Φ.IsQuantifierFree) (i : Fin (k+1))
    (hSent : Φ.freeVars ⊆ {i}) :
    ∃ Ψ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D),
      Ψ.IsQuantifierFree ∧
      Ψ.freeVars = ∅ ∧
      (Formula.exists_ i Φ).realization (C := C) =
        Ψ.realization (C := C) ∧
      (Formula.exists_ i Φ).realization (C := C') =
        Ψ.realization (C := C') := by
  classical
  set s : Fin (k+1) → Fin (k+1) :=
    ((Equiv.swap i (Fin.last k) : Equiv.Perm (Fin (k+1))) :
      Fin (k+1) → Fin (k+1))
  have hs_inj : Function.Injective s := (Equiv.swap i (Fin.last k)).injective
  set Φtilde : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D) :=
    Φ.rename s (FieldAtom.renameVars s)
  have hQF_tilde : Φtilde.IsQuantifierFree :=
    Formula.rename_isQF _ _ _ hQF
  -- Φtilde.freeVars ⊆ image s {i} = {s i} = {last k}.
  have hSent_tilde : Φtilde.freeVars ⊆ {Fin.last k} := by
    have hsub : Φtilde.freeVars ⊆ Φ.freeVars.image s :=
      Formula.rename_freeVars_subset s Φ
    intro x hx
    have hximg := hsub hx
    rw [Finset.mem_image] at hximg
    obtain ⟨y, hy_mem, hxy⟩ := hximg
    have hy_i : y = i := Finset.mem_singleton.mp (hSent hy_mem)
    subst hy_i
    rw [Finset.mem_singleton]
    have hsi : s y = Fin.last k := by
      show (Equiv.swap y (Fin.last k)) y = Fin.last k
      simp [Equiv.swap_apply_left]
    rw [← hxy, hsi]
  set L := qfDNFAux (D := D) true Φtilde
  -- All polys in L have vars ⊆ Φtilde.freeVars ⊆ {last k}.
  have hL_vars : ∀ PQ ∈ L,
      (∀ P ∈ PQ.1, P.vars ⊆ {Fin.last k}) ∧
        (∀ Q ∈ PQ.2, Q.vars ⊆ {Fin.last k}) := by
    intro PQ hPQ
    have ⟨hP, hQ⟩ := qfDNFAux_polys_vars_subset true hQF_tilde PQ hPQ
    exact ⟨fun P hP_mem => (hP P hP_mem).trans hSent_tilde,
           fun Q hQ_mem => (hQ Q hQ_mem).trans hSent_tilde⟩
  set Ψ_inner : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D) :=
    Formula.disjList (L.map fun PQ =>
      (projBasic PQ.1 PQ.2).rename Fin.castSucc
        (FieldAtom.renameVars Fin.castSucc))
  have hΨ_inner_freeVars : Ψ_inner.freeVars = ∅ := by
    apply Formula.disjList_freeVars_empty
    intro Φ hΦ
    rw [List.mem_map] at hΦ
    obtain ⟨PQ, hPQ_mem, rfl⟩ := hΦ
    have ⟨hP_vars, hQ_vars⟩ := hL_vars PQ hPQ_mem
    apply Formula.rename_freeVars_empty
    exact projBasic_freeVars_empty_of_vars_subset_last hP_vars hQ_vars
  refine ⟨Ψ_inner.rename s (FieldAtom.renameVars s), ?_, ?_, ?_, ?_⟩
  · exact Formula.rename_isQF _ _ _ (disjList_qe_isQF L)
  · exact Formula.rename_freeVars_empty s hΨ_inner_freeVars
  · rw [realization_exists_swap (D := D) (C := C) i Φ]
    rw [Formula.rename_realization s hs_inj]
    congr 1
    show (Formula.exists_ (Fin.last k) Φtilde).realization (C := C) =
      Ψ_inner.realization (C := C)
    have hDNF : Φtilde.realization (C := C) =
        (Formula.disjList (L.map fun PQ =>
          conjFormFormula PQ.1 PQ.2)).realization (C := C) := by
      rw [qfDNF_realization _ hQF_tilde, Formula.realization_disjList]
      ext y
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, List.mem_map]
      constructor
      · rintro ⟨PQ, hPQ, hy⟩
        exact ⟨_, ⟨PQ, hPQ, rfl⟩, hy⟩
      · rintro ⟨Φ, ⟨PQ, hPQ, rfl⟩, hy⟩
        exact ⟨PQ, hPQ, hy⟩
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
  · rw [realization_exists_swap (D := D) (C := C') i Φ]
    rw [Formula.rename_realization s hs_inj]
    congr 1
    show (Formula.exists_ (Fin.last k) Φtilde).realization (C := C') =
      Ψ_inner.realization (C := C')
    have hDNF : Φtilde.realization (C := C') =
        (Formula.disjList (L.map fun PQ =>
          conjFormFormula PQ.1 PQ.2)).realization (C := C') := by
      rw [qfDNF_realization _ hQF_tilde, Formula.realization_disjList]
      ext y
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, List.mem_map]
      constructor
      · rintro ⟨PQ, hPQ, hy⟩
        exact ⟨_, ⟨PQ, hPQ, rfl⟩, hy⟩
      · rintro ⟨Φ, ⟨PQ, hPQ, rfl⟩, hy⟩
        exact ⟨PQ, hPQ, hy⟩
    have hexists : (Formula.exists_ (Fin.last k) Φtilde).realization (C := C') =
        (Formula.exists_ (Fin.last k)
          (Formula.disjList (L.map fun PQ =>
            conjFormFormula PQ.1 PQ.2))).realization (C := C') := by
      show { y | ∃ c, Function.update y (Fin.last k) c ∈
          Φtilde.realization (C := C') } = _
      show _ = { y | ∃ c, Function.update y (Fin.last k) c ∈
          (Formula.disjList (L.map fun PQ =>
            conjFormFormula PQ.1 PQ.2)).realization (C := C') }
      rw [hDNF]
    rw [hexists, realization_exists_last_qfDNF hinj']

/-- **Two-field existential QE preserves freeVars ⊆ T.** A relative
version of `existsQE_two_fields_preserves_sentence`: given any
`T : Finset (Fin (k+1))` and a QF formula `Φ` with
`Φ.freeVars ⊆ insert i T`, the QE output `Ψ` has `Ψ.freeVars ⊆ T`.
The sentence case is `T = ∅`. -/
theorem existsQE_two_fields_preserves_sentence_relative
    (hinj : Function.Injective (algebraMap D C))
    (hinj' : Function.Injective (algebraMap D C'))
    {k : ℕ} (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D))
    (hQF : Φ.IsQuantifierFree) (i : Fin (k+1))
    (T : Finset (Fin (k+1)))
    (hFv : Φ.freeVars ⊆ insert i T) :
    ∃ Ψ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D),
      Ψ.IsQuantifierFree ∧
      Ψ.freeVars ⊆ T ∧
      (Formula.exists_ i Φ).realization (C := C) =
        Ψ.realization (C := C) ∧
      (Formula.exists_ i Φ).realization (C := C') =
        Ψ.realization (C := C') := by
  classical
  set s : Fin (k+1) → Fin (k+1) :=
    ((Equiv.swap i (Fin.last k) : Equiv.Perm (Fin (k+1))) :
      Fin (k+1) → Fin (k+1))
  have hs_inj : Function.Injective s := (Equiv.swap i (Fin.last k)).injective
  have hs_invol : ∀ x, s (s x) = x := by
    intro x
    show (Equiv.swap i (Fin.last k)) ((Equiv.swap i (Fin.last k)) x) = x
    rw [Equiv.swap_apply_self]
  set Φtilde : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D) :=
    Φ.rename s (FieldAtom.renameVars s)
  have hQF_tilde : Φtilde.IsQuantifierFree :=
    Formula.rename_isQF _ _ _ hQF
  -- T' : Finset (Fin k) = preimage of (image s T) under castSucc.
  -- Captures the part of `image s T` that's not `last k`.
  set T' : Finset (Fin k) :=
    (T.image s).preimage Fin.castSucc (Fin.castSucc_injective k).injOn
    with T'_def
  -- Φtilde.freeVars ⊆ insert (last k) (T.image s)
  have hFvtilde : Φtilde.freeVars ⊆ insert (Fin.last k) (T.image s) := by
    have hsub : Φtilde.freeVars ⊆ Φ.freeVars.image s :=
      Formula.rename_freeVars_subset s Φ
    intro x hx
    have hximg := hsub hx
    rw [Finset.mem_image] at hximg
    obtain ⟨y, hy_mem, hxy⟩ := hximg
    have hy_iT : y ∈ insert i T := hFv hy_mem
    rw [Finset.mem_insert] at hy_iT
    rcases hy_iT with rfl | hyT
    · -- y = i ⇒ s y = last k.
      rw [Finset.mem_insert]
      left
      rw [← hxy]
      show (Equiv.swap y (Fin.last k)) y = Fin.last k
      simp [Equiv.swap_apply_left]
    · -- y ∈ T ⇒ s y ∈ T.image s.
      rw [Finset.mem_insert]
      right
      rw [← hxy]
      exact Finset.mem_image.mpr ⟨y, hyT, rfl⟩
  -- Every polynomial in qfDNFAux has vars ⊆ Φtilde.freeVars.
  -- Combined with hFvtilde, vars ⊆ insert (last k) (T.image s).
  -- And T.image s ⊆ insert (last k) (T'.image castSucc).
  have h_imageS_sub : T.image s ⊆ insert (Fin.last k) (T'.image Fin.castSucc) := by
    intro x hx
    by_cases hxl : x = Fin.last k
    · subst hxl; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      -- x ≠ last k means x = castSucc j for some j.
      obtain ⟨j, rfl⟩ :=
        (Fin.eq_castSucc_or_eq_last x).resolve_right hxl
      rw [Finset.mem_image]
      refine ⟨j, ?_, rfl⟩
      rw [T'_def]
      rw [Finset.mem_preimage]
      exact hx
  have hL_vars : ∀ PQ ∈ qfDNFAux (D := D) true Φtilde,
      (∀ P ∈ PQ.1, P.vars ⊆ insert (Fin.last k) (T'.image Fin.castSucc)) ∧
        (∀ Q ∈ PQ.2, Q.vars ⊆ insert (Fin.last k) (T'.image Fin.castSucc)) := by
    intro PQ hPQ
    have ⟨hP, hQ⟩ := qfDNFAux_polys_vars_subset true hQF_tilde PQ hPQ
    have hsub : Φtilde.freeVars ⊆ insert (Fin.last k) (T'.image Fin.castSucc) := by
      intro x hx
      have := hFvtilde hx
      rw [Finset.mem_insert] at this
      rcases this with rfl | hxs
      · exact Finset.mem_insert_self _ _
      · exact h_imageS_sub hxs
    exact ⟨fun P hP_mem => (hP P hP_mem).trans hsub,
           fun Q hQ_mem => (hQ Q hQ_mem).trans hsub⟩
  set L := qfDNFAux (D := D) true Φtilde
  set Ψ_inner : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) D) :=
    Formula.disjList (L.map fun PQ =>
      (projBasic PQ.1 PQ.2).rename Fin.castSucc
        (FieldAtom.renameVars Fin.castSucc))
  have hΨ_inner_freeVars : Ψ_inner.freeVars ⊆ T'.image Fin.castSucc := by
    apply Formula.disjList_freeVars_subset
    intro Φ hΦ
    rw [List.mem_map] at hΦ
    obtain ⟨PQ, hPQ_mem, rfl⟩ := hΦ
    have ⟨hP_vars, hQ_vars⟩ := hL_vars PQ hPQ_mem
    have hpb_sub : (projBasic PQ.1 PQ.2).freeVars ⊆ T' :=
      projBasic_freeVars_subset hP_vars hQ_vars
    -- Now rename via castSucc.
    have hren_sub :
        (((projBasic PQ.1 PQ.2).rename Fin.castSucc
            (FieldAtom.renameVars Fin.castSucc)).freeVars) ⊆
          (projBasic PQ.1 PQ.2).freeVars.image Fin.castSucc :=
      Formula.rename_freeVars_subset _ _
    intro x hx
    have hx' := hren_sub hx
    rw [Finset.mem_image] at hx'
    obtain ⟨y, hy_mem, hxy⟩ := hx'
    have hyT' : y ∈ T' := hpb_sub hy_mem
    rw [Finset.mem_image]
    exact ⟨y, hyT', hxy⟩
  -- And image s (T'.image castSucc) ⊆ T.
  have h_swap_back :
      (Ψ_inner.rename s (FieldAtom.renameVars s)).freeVars ⊆ T := by
    intro x hx
    have hsub : (Ψ_inner.rename s (FieldAtom.renameVars s)).freeVars ⊆
        Ψ_inner.freeVars.image s :=
      Formula.rename_freeVars_subset s Ψ_inner
    have hx_img := hsub hx
    rw [Finset.mem_image] at hx_img
    obtain ⟨y, hy_mem, hxy⟩ := hx_img
    -- y ∈ Ψ_inner.freeVars ⊆ T'.image castSucc
    have hy_T'img := hΨ_inner_freeVars hy_mem
    rw [Finset.mem_image] at hy_T'img
    obtain ⟨z, hz_T', hz_eq⟩ := hy_T'img
    -- castSucc z = y; want s y ∈ T.
    -- T' is preimage of image s T under castSucc, so castSucc z ∈ image s T.
    rw [T'_def, Finset.mem_preimage] at hz_T'
    -- castSucc z ∈ image s T
    rw [hz_eq] at hz_T'
    rw [Finset.mem_image] at hz_T'
    obtain ⟨w, hw_T, hw_eq⟩ := hz_T'
    -- w ∈ T, s w = y. So s y = s (s w) = w.
    have : s y = w := by rw [← hw_eq, hs_invol]
    rw [← hxy, this]
    exact hw_T
  refine ⟨Ψ_inner.rename s (FieldAtom.renameVars s), ?_, h_swap_back, ?_, ?_⟩
  · exact Formula.rename_isQF _ _ _ (disjList_qe_isQF L)
  · rw [realization_exists_swap (D := D) (C := C) i Φ]
    rw [Formula.rename_realization s hs_inj]
    congr 1
    show (Formula.exists_ (Fin.last k) Φtilde).realization (C := C) =
      Ψ_inner.realization (C := C)
    have hDNF : Φtilde.realization (C := C) =
        (Formula.disjList (L.map fun PQ =>
          conjFormFormula PQ.1 PQ.2)).realization (C := C) := by
      rw [qfDNF_realization _ hQF_tilde, Formula.realization_disjList]
      ext y
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, List.mem_map]
      constructor
      · rintro ⟨PQ, hPQ, hy⟩
        exact ⟨_, ⟨PQ, hPQ, rfl⟩, hy⟩
      · rintro ⟨Φ, ⟨PQ, hPQ, rfl⟩, hy⟩
        exact ⟨PQ, hPQ, hy⟩
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
  · rw [realization_exists_swap (D := D) (C := C') i Φ]
    rw [Formula.rename_realization s hs_inj]
    congr 1
    show (Formula.exists_ (Fin.last k) Φtilde).realization (C := C') =
      Ψ_inner.realization (C := C')
    have hDNF : Φtilde.realization (C := C') =
        (Formula.disjList (L.map fun PQ =>
          conjFormFormula PQ.1 PQ.2)).realization (C := C') := by
      rw [qfDNF_realization _ hQF_tilde, Formula.realization_disjList]
      ext y
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, List.mem_map]
      constructor
      · rintro ⟨PQ, hPQ, hy⟩
        exact ⟨_, ⟨PQ, hPQ, rfl⟩, hy⟩
      · rintro ⟨Φ, ⟨PQ, hPQ, rfl⟩, hy⟩
        exact ⟨PQ, hPQ, hy⟩
    have hexists : (Formula.exists_ (Fin.last k) Φtilde).realization (C := C') =
        (Formula.exists_ (Fin.last k)
          (Formula.disjList (L.map fun PQ =>
            conjFormFormula PQ.1 PQ.2))).realization (C := C') := by
      show { y | ∃ c, Function.update y (Fin.last k) c ∈
          Φtilde.realization (C := C') } = _
      show _ = { y | ∃ c, Function.update y (Fin.last k) c ∈
          (Formula.disjList (L.map fun PQ =>
            conjFormFormula PQ.1 PQ.2)).realization (C := C') }
      rw [hDNF]
    rw [hexists, realization_exists_last_qfDNF hinj']

end TwoFieldExistsQE

/-!
### Two-field Theorem 1.23
-/

section TwoFieldsTheorem123

variable {C C' : Type*} [Field C] [Field C'] [IsAlgClosed C] [IsAlgClosed C']
variable [Algebra D C] [Algebra D C']

/-- **Two-field Theorem 1.23.** For any formula `Φ` over `D`, there is a
single QF formula `Ψ` whose realisation agrees with that of `Φ` over BOTH
algebraically closed fields `C` and `C'` simultaneously. -/
theorem theorem_1_23_two_fields [IsDomain D]
    (hinj : Function.Injective (algebraMap D C))
    (hinj' : Function.Injective (algebraMap D C'))
    {ℓ : ℕ} (Φ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D)) :
    ∃ Ψ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D),
      Ψ.IsQuantifierFree ∧
      Φ.realization (C := C) = Ψ.realization (C := C) ∧
      Φ.realization (C := C') = Ψ.realization (C := C') := by
  induction Φ with
  | atom a => exact ⟨.atom a, trivial, rfl, rfl⟩
  | not Φ ih =>
    obtain ⟨Ψ, hQF, hΦ, hΦ'⟩ := ih
    refine ⟨Formula.not Ψ, hQF, ?_, ?_⟩
    · show (Φ.realization (C := C))ᶜ = (Ψ.realization (C := C))ᶜ
      rw [hΦ]
    · show (Φ.realization (C := C'))ᶜ = (Ψ.realization (C := C'))ᶜ
      rw [hΦ']
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hQF₁, h₁, h₁'⟩ := ih₁
    obtain ⟨Ψ₂, hQF₂, h₂, h₂'⟩ := ih₂
    refine ⟨Formula.and Ψ₁ Ψ₂, ⟨hQF₁, hQF₂⟩, ?_, ?_⟩
    · show Φ₁.realization (C := C) ∩ Φ₂.realization (C := C) =
        Ψ₁.realization (C := C) ∩ Ψ₂.realization (C := C)
      rw [h₁, h₂]
    · show Φ₁.realization (C := C') ∩ Φ₂.realization (C := C') =
        Ψ₁.realization (C := C') ∩ Ψ₂.realization (C := C')
      rw [h₁', h₂']
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hQF₁, h₁, h₁'⟩ := ih₁
    obtain ⟨Ψ₂, hQF₂, h₂, h₂'⟩ := ih₂
    refine ⟨Formula.or Ψ₁ Ψ₂, ⟨hQF₁, hQF₂⟩, ?_, ?_⟩
    · show Φ₁.realization (C := C) ∪ Φ₂.realization (C := C) =
        Ψ₁.realization (C := C) ∪ Ψ₂.realization (C := C)
      rw [h₁, h₂]
    · show Φ₁.realization (C := C') ∪ Φ₂.realization (C := C') =
        Ψ₁.realization (C := C') ∪ Ψ₂.realization (C := C')
      rw [h₁', h₂']
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hQF₁, h₁, h₁'⟩ := ih₁
    obtain ⟨Ψ₂, hQF₂, h₂, h₂'⟩ := ih₂
    refine ⟨Formula.implies Ψ₁ Ψ₂, ⟨hQF₁, hQF₂⟩, ?_, ?_⟩
    · show (Φ₁.realization (C := C))ᶜ ∪ Φ₂.realization (C := C) =
        (Ψ₁.realization (C := C))ᶜ ∪ Ψ₂.realization (C := C)
      rw [h₁, h₂]
    · show (Φ₁.realization (C := C'))ᶜ ∪ Φ₂.realization (C := C') =
        (Ψ₁.realization (C := C'))ᶜ ∪ Ψ₂.realization (C := C')
      rw [h₁', h₂']
  | exists_ i Φ ih =>
    obtain ⟨Ψ, hQF, hΦ, hΦ'⟩ := ih
    cases ℓ with
    | zero => exact Fin.elim0 i
    | succ k =>
      obtain ⟨Ψ', hQF', hC, hC'⟩ :=
        existsQE_two_fields (D := D) (C := C) (C' := C') hinj hinj' Ψ hQF i
      refine ⟨Ψ', hQF', ?_, ?_⟩
      · have hΦΨ : (Formula.exists_ i Φ).realization (C := C) =
            (Formula.exists_ i Ψ).realization (C := C) := by
          show { y | ∃ c, Function.update y i c ∈ Φ.realization (C := C) } =
            { y | ∃ c, Function.update y i c ∈ Ψ.realization (C := C) }
          rw [hΦ]
        rw [hΦΨ, hC]
      · have hΦΨ : (Formula.exists_ i Φ).realization (C := C') =
            (Formula.exists_ i Ψ).realization (C := C') := by
          show { y | ∃ c, Function.update y i c ∈ Φ.realization (C := C') } =
            { y | ∃ c, Function.update y i c ∈ Ψ.realization (C := C') }
          rw [hΦ']
        rw [hΦΨ, hC']
  | forall_ i Φ ih =>
    obtain ⟨Ψ, hQF, hΦ, hΦ'⟩ := ih
    cases ℓ with
    | zero => exact Fin.elim0 i
    | succ k =>
      have hNotΨ : (Formula.not Ψ).IsQuantifierFree := hQF
      obtain ⟨Ψ', hQF', hC, hC'⟩ :=
        existsQE_two_fields (D := D) (C := C) (C' := C') hinj hinj'
          (Formula.not Ψ) hNotΨ i
      refine ⟨Formula.not Ψ', hQF', ?_, ?_⟩
      · rw [realization_forall_eq_not_exists_not]
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
        rw [hexists_rewrite, hC]
      · rw [realization_forall_eq_not_exists_not]
        show (((Formula.exists_ i (Formula.not Φ)).realization (C := C'))ᶜ) =
          (Ψ'.realization (C := C'))ᶜ
        congr 1
        have hnot : (Formula.not Φ).realization (C := C') =
            (Formula.not Ψ).realization (C := C') := by
          show (Φ.realization (C := C'))ᶜ = (Ψ.realization (C := C'))ᶜ
          rw [hΦ']
        have hexists_rewrite :
            (Formula.exists_ i (Formula.not Φ)).realization (C := C') =
            (Formula.exists_ i (Formula.not Ψ)).realization (C := C') := by
          show { y | ∃ c, Function.update y i c ∈
              (Formula.not Φ).realization (C := C') } = _
          show _ = { y | ∃ c, Function.update y i c ∈
              (Formula.not Ψ).realization (C := C') }
          rw [hnot]
        rw [hexists_rewrite, hC']

/-- **Two-field Theorem 1.23 with `freeVars ⊆ S` tracking.** Stronger
recursive statement: for any set `S` containing `Φ.freeVars`, produce a
QF formula `Ψ` realization-equivalent over both `C` and `C'`, with
`Ψ.freeVars ⊆ S`. The sentence case is `S = ∅`.

The proof carries `Ψ.freeVars ⊆ S` through structural induction.
For `exists_ i Φ` over an arbitrary index `i`, we apply IH to `Φ` with
`S ∪ {i}` as the bound, obtaining `Ψ` with `Ψ.freeVars ⊆ S ∪ {i}`. Then
the strengthened `existsQE_two_fields_preserves_sentence_relative`
eliminates `i` (under the hypothesis `Ψ.freeVars ⊆ S ∪ {i}`, the QE
output has freeVars ⊆ S). -/
theorem theorem_1_23_two_fields_preserves_sentence [IsDomain D]
    (hinj : Function.Injective (algebraMap D C))
    (hinj' : Function.Injective (algebraMap D C'))
    {ℓ : ℕ} (Φ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D))
    (hSent : Φ.freeVars = ∅) :
    ∃ Ψ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D),
      Ψ.IsQuantifierFree ∧
      Ψ.freeVars = ∅ ∧
      Φ.realization (C := C) = Ψ.realization (C := C) ∧
      Φ.realization (C := C') = Ψ.realization (C := C') := by
  -- We use the un-strengthened theorem_1_23_two_fields to get Ψ. The
  -- key fact is that for the sentence case, applying realization
  -- transfer turns `Φ.realization C = univ` into `Ψ.realization C = univ`,
  -- but we need `Ψ.freeVars = ∅` to use sentence transfer.
  -- Instead, we use the strengthened existsQE_two_fields_preserves_sentence
  -- inductively. This requires an inductive statement carrying
  -- `Ψ.freeVars ⊆ S` for varying S, which we obtain by setting up the
  -- induction over Φ generalizing over S.
  --
  -- For now, prove the sentence-only version (S = ∅) by mimicking
  -- theorem_1_23_two_fields's induction.
  classical
  -- General statement: for any Φ, ∃ Ψ with Ψ.freeVars ⊆ Φ.freeVars and
  -- realization match. We then specialize with hSent to get Ψ.freeVars = ∅.
  suffices h : ∀ {ℓ : ℕ} (Φ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D))
      (S : Finset (Fin ℓ)), Φ.freeVars ⊆ S →
      ∃ Ψ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D),
        Ψ.IsQuantifierFree ∧
        Ψ.freeVars ⊆ S ∧
        Φ.realization (C := C) = Ψ.realization (C := C) ∧
        Φ.realization (C := C') = Ψ.realization (C := C') by
    obtain ⟨Ψ, hQF, hfv, hC, hC'⟩ := h Φ ∅ (hSent ▸ Finset.Subset.refl _)
    exact ⟨Ψ, hQF, Finset.subset_empty.mp hfv, hC, hC'⟩
  clear hSent
  intro ℓ Φ
  induction Φ with
  | atom a =>
    intro S hS
    exact ⟨.atom a, trivial, hS, rfl, rfl⟩
  | not Φ ih =>
    intro S hS
    have hSubΦ : Φ.freeVars ⊆ S := hS
    obtain ⟨Ψ, hQF, hfv, hΦ, hΦ'⟩ := ih S hSubΦ
    refine ⟨Formula.not Ψ, hQF, hfv, ?_, ?_⟩
    · show (Φ.realization (C := C))ᶜ = (Ψ.realization (C := C))ᶜ
      rw [hΦ]
    · show (Φ.realization (C := C'))ᶜ = (Ψ.realization (C := C'))ᶜ
      rw [hΦ']
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    intro S hS
    have hSub₁ : Φ₁.freeVars ⊆ S := (Finset.union_subset_iff.mp hS).1
    have hSub₂ : Φ₂.freeVars ⊆ S := (Finset.union_subset_iff.mp hS).2
    obtain ⟨Ψ₁, hQF₁, hfv₁, h₁, h₁'⟩ := ih₁ S hSub₁
    obtain ⟨Ψ₂, hQF₂, hfv₂, h₂, h₂'⟩ := ih₂ S hSub₂
    refine ⟨Formula.and Ψ₁ Ψ₂, ⟨hQF₁, hQF₂⟩,
      Finset.union_subset hfv₁ hfv₂, ?_, ?_⟩
    · show Φ₁.realization (C := C) ∩ Φ₂.realization (C := C) =
        Ψ₁.realization (C := C) ∩ Ψ₂.realization (C := C)
      rw [h₁, h₂]
    · show Φ₁.realization (C := C') ∩ Φ₂.realization (C := C') =
        Ψ₁.realization (C := C') ∩ Ψ₂.realization (C := C')
      rw [h₁', h₂']
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    intro S hS
    have hSub₁ : Φ₁.freeVars ⊆ S := (Finset.union_subset_iff.mp hS).1
    have hSub₂ : Φ₂.freeVars ⊆ S := (Finset.union_subset_iff.mp hS).2
    obtain ⟨Ψ₁, hQF₁, hfv₁, h₁, h₁'⟩ := ih₁ S hSub₁
    obtain ⟨Ψ₂, hQF₂, hfv₂, h₂, h₂'⟩ := ih₂ S hSub₂
    refine ⟨Formula.or Ψ₁ Ψ₂, ⟨hQF₁, hQF₂⟩,
      Finset.union_subset hfv₁ hfv₂, ?_, ?_⟩
    · show Φ₁.realization (C := C) ∪ Φ₂.realization (C := C) =
        Ψ₁.realization (C := C) ∪ Ψ₂.realization (C := C)
      rw [h₁, h₂]
    · show Φ₁.realization (C := C') ∪ Φ₂.realization (C := C') =
        Ψ₁.realization (C := C') ∪ Ψ₂.realization (C := C')
      rw [h₁', h₂']
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    intro S hS
    have hSub₁ : Φ₁.freeVars ⊆ S := (Finset.union_subset_iff.mp hS).1
    have hSub₂ : Φ₂.freeVars ⊆ S := (Finset.union_subset_iff.mp hS).2
    obtain ⟨Ψ₁, hQF₁, hfv₁, h₁, h₁'⟩ := ih₁ S hSub₁
    obtain ⟨Ψ₂, hQF₂, hfv₂, h₂, h₂'⟩ := ih₂ S hSub₂
    refine ⟨Formula.implies Ψ₁ Ψ₂, ⟨hQF₁, hQF₂⟩,
      Finset.union_subset hfv₁ hfv₂, ?_, ?_⟩
    · show (Φ₁.realization (C := C))ᶜ ∪ Φ₂.realization (C := C) =
        (Ψ₁.realization (C := C))ᶜ ∪ Ψ₂.realization (C := C)
      rw [h₁, h₂]
    · show (Φ₁.realization (C := C'))ᶜ ∪ Φ₂.realization (C := C') =
        (Ψ₁.realization (C := C'))ᶜ ∪ Ψ₂.realization (C := C')
      rw [h₁', h₂']
  | exists_ i Φ ih =>
    intro S hS
    cases ℓ with
    | zero => exact Fin.elim0 i
    | succ k =>
      -- Φ.freeVars ⊆ S ∪ {i}, so apply IH with S' = S ∪ {i}.
      have hSub : Φ.freeVars ⊆ insert i S := by
        intro x hx
        by_cases hxi : x = i
        · subst hxi; exact Finset.mem_insert_self _ _
        · apply Finset.mem_insert_of_mem
          apply hS
          rw [Formula.freeVars]
          rw [Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨hx, hxi⟩
      obtain ⟨Ψ, hQF, hfv, hΦ, hΦ'⟩ := ih (insert i S) hSub
      obtain ⟨Ψ', hQF', hΨ'fv, hC, hC'⟩ :=
        existsQE_two_fields_preserves_sentence_relative
          (D := D) (C := C) (C' := C')
          hinj hinj' Ψ hQF i S hfv
      refine ⟨Ψ', hQF', hΨ'fv, ?_, ?_⟩
      · have hΦΨ : (Formula.exists_ i Φ).realization (C := C) =
            (Formula.exists_ i Ψ).realization (C := C) := by
          show { y | ∃ c, Function.update y i c ∈ Φ.realization (C := C) } =
            { y | ∃ c, Function.update y i c ∈ Ψ.realization (C := C) }
          rw [hΦ]
        rw [hΦΨ, hC]
      · have hΦΨ : (Formula.exists_ i Φ).realization (C := C') =
            (Formula.exists_ i Ψ).realization (C := C') := by
          show { y | ∃ c, Function.update y i c ∈ Φ.realization (C := C') } =
            { y | ∃ c, Function.update y i c ∈ Ψ.realization (C := C') }
          rw [hΦ']
        rw [hΦΨ, hC']
  | forall_ i Φ ih =>
    intro S hS
    cases ℓ with
    | zero => exact Fin.elim0 i
    | succ k =>
      -- Same pattern as exists_, applied to ¬Φ.
      have hSub : Φ.freeVars ⊆ insert i S := by
        intro x hx
        by_cases hxi : x = i
        · subst hxi; exact Finset.mem_insert_self _ _
        · apply Finset.mem_insert_of_mem
          apply hS
          rw [Formula.freeVars]
          rw [Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨hx, hxi⟩
      obtain ⟨Ψ, hQF, hfv, hΦ, hΦ'⟩ := ih (insert i S) hSub
      have hNotΨ : (Formula.not Ψ).IsQuantifierFree := hQF
      have hNotΨfv : (Formula.not Ψ).freeVars ⊆ insert i S := hfv
      obtain ⟨Ψ', hQF', hΨ'fv, hC, hC'⟩ :=
        existsQE_two_fields_preserves_sentence_relative
          (D := D) (C := C) (C' := C')
          hinj hinj' (Formula.not Ψ) hNotΨ i S hNotΨfv
      refine ⟨Formula.not Ψ', hQF', hΨ'fv, ?_, ?_⟩
      · rw [realization_forall_eq_not_exists_not]
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
        rw [hexists_rewrite, hC]
      · rw [realization_forall_eq_not_exists_not]
        show (((Formula.exists_ i (Formula.not Φ)).realization (C := C'))ᶜ) =
          (Ψ'.realization (C := C'))ᶜ
        congr 1
        have hnot : (Formula.not Φ).realization (C := C') =
            (Formula.not Ψ).realization (C := C') := by
          show (Φ.realization (C := C'))ᶜ = (Ψ.realization (C := C'))ᶜ
          rw [hΦ']
        have hexists_rewrite :
            (Formula.exists_ i (Formula.not Φ)).realization (C := C') =
            (Formula.exists_ i (Formula.not Ψ)).realization (C := C') := by
          show { y | ∃ c, Function.update y i c ∈
              (Formula.not Φ).realization (C := C') } = _
          show _ = { y | ∃ c, Function.update y i c ∈
              (Formula.not Ψ).realization (C := C') }
          rw [hnot]
        rw [hexists_rewrite, hC']

end TwoFieldsTheorem123

/-!
### Sentence transfer over `Fin 0`

A QF formula over `Fin 0` is automatically a sentence. We work directly with
the unique assignment `Fin.elim0`: `S = Set.univ ↔ Fin.elim0 ∈ S`. The
realisation of an atom `P = 0` at `Fin.elim0` is `aeval Fin.elim0 P = 0`,
which transfers via the algebra map `C → C'` when that map is injective.
-/

section Sentence

/-- For any set `S ⊆ Fin 0 → C`, `S = Set.univ ↔ Fin.elim0 ∈ S`. -/
theorem set_finZero_eq_univ_iff {C : Type*} (S : Set (Fin 0 → C)) :
    S = Set.univ ↔ Fin.elim0 ∈ S := by
  constructor
  · intro h; rw [h]; trivial
  · intro h
    ext y
    simp only [Set.mem_univ, iff_true]
    have hy : y = Fin.elim0 := by funext i; exact Fin.elim0 i
    rw [hy]; exact h

/-- For `P ∈ MvPolynomial (Fin 0) D` and any algebra `D → C → C'`, evaluation
of `P` at `Fin.elim0 : Fin 0 → C'` factors through evaluation at
`Fin.elim0 : Fin 0 → C` via the algebra map `C → C'`. -/
theorem aeval_finZero_algebraMap
    {C C' : Type*} [Field C] [Field C'] [Algebra D C] [Algebra D C']
    [Algebra C C'] [IsScalarTower D C C']
    (P : MvPolynomial (Fin 0) D) :
    MvPolynomial.aeval (Fin.elim0 : Fin 0 → C') P =
      (algebraMap C C') (MvPolynomial.aeval (Fin.elim0 : Fin 0 → C) P) := by
  -- Note: aeval (Fin.elim0 : Fin 0 → C') is the unique D-AlgHom that sends
  -- X i to (Fin.elim0 i). Similarly, (algebraMap C C').comp (aeval Fin.elim0)
  -- is a D-AlgHom that sends X i to (algebraMap C C') (Fin.elim0 i) = elim0 i.
  -- So they coincide.
  have := MvPolynomial.aeval_unique
    ((Algebra.ofId C C').restrictScalars D |>.comp
      (MvPolynomial.aeval (Fin.elim0 : Fin 0 → C)))
  have key : ((Algebra.ofId C C').restrictScalars D |>.comp
      (MvPolynomial.aeval (Fin.elim0 : Fin 0 → C))) =
      MvPolynomial.aeval (Fin.elim0 : Fin 0 → C') := by
    apply MvPolynomial.algHom_ext
    intro i; exact Fin.elim0 i
  have h1 : (MvPolynomial.aeval (Fin.elim0 : Fin 0 → C') : MvPolynomial (Fin 0) D →ₐ[D] C') P =
      (((Algebra.ofId C C').restrictScalars D).comp
        (MvPolynomial.aeval (Fin.elim0 : Fin 0 → C))) P := by rw [key]
  simp only [AlgHom.coe_comp, Function.comp_apply,
    AlgHom.coe_restrictScalars', Algebra.ofId_apply] at h1
  exact h1

/-- An atom `Formula.atom a` over `Fin 0` with `D = C` has the same
realisation over `C` and `C'`, modulo the algebra-map transfer. -/
theorem qf_finZero_atom_transfer
    {C C' : Type*} [Field C] [Field C'] [Algebra C C']
    (a : FieldAtom (Fin 0) C)
    (hAlgInj : Function.Injective (algebraMap C C')) :
    (Formula.atom a).realization (C := C) = Set.univ ↔
    (Formula.atom a).realization (C := C') = Set.univ := by
  -- Show both sides via `set_finZero_eq_univ_iff` applied to the realisation.
  rw [set_finZero_eq_univ_iff, set_finZero_eq_univ_iff]
  have hbridge : MvPolynomial.aeval (Fin.elim0 : Fin 0 → C') a.poly =
      (algebraMap C C') (MvPolynomial.aeval (Fin.elim0 : Fin 0 → C) a.poly) :=
    aeval_finZero_algebraMap (D := C) (C := C) (C' := C') a.poly
  rcases hb : a.isEq with _ | _
  · -- a.isEq = false: atom is "≠ 0".
    simp only [Formula.realization, Formula.interpret_fieldAtom, hb,
      Bool.false_eq_true, ite_false, Set.mem_ofPred_eq]
    rw [hbridge]
    constructor
    · intro h heq
      apply h
      have : (algebraMap C C') (MvPolynomial.aeval Fin.elim0 a.poly) =
             (algebraMap C C') 0 := by rw [heq, map_zero]
      exact hAlgInj this
    · intro h heq
      apply h
      rw [heq, map_zero]
  · -- a.isEq = true: atom is "= 0".
    simp only [Formula.realization, Formula.interpret_fieldAtom, hb, ite_true,
      Set.mem_ofPred_eq]
    rw [hbridge]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      have : (algebraMap C C') (MvPolynomial.aeval Fin.elim0 a.poly) =
             (algebraMap C C') 0 := by rw [h, map_zero]
      exact hAlgInj this

end Sentence

/-!
### Theorem 1.26 (Lefschetz principle)
-/

section MainTheorem

variable {C C' : Type*} [Field C] [Field C'] [IsAlgClosed C] [IsAlgClosed C']

omit [IsAlgClosed C] [IsAlgClosed C'] in
/-- A QF formula `Ψ : Formula (Fin 0) (FieldAtom (Fin 0) C)` has the same
truth value over `C` and `C'` (in the sense of `realization = Set.univ`)
whenever `algebraMap C C'` is injective. We prove this by induction on `Ψ`,
working entirely with the singleton assignment `Fin.elim0`. -/
theorem qf_finZero_realization_transfer [Algebra C C']
    (Ψ : Formula (Fin 0) (FieldAtom (Fin 0) C))
    (hQF : Ψ.IsQuantifierFree) :
    Ψ.realization (C := C) = Set.univ ↔
    Ψ.realization (C := C') = Set.univ := by
  have hAlgInj : Function.Injective (algebraMap C C') :=
    RingHom.injective (algebraMap C C')
  induction Ψ with
  | atom a => exact qf_finZero_atom_transfer a hAlgInj
  | not Φ ih =>
    have hQF' : Φ.IsQuantifierFree := hQF
    -- (Φ.realization)ᶜ = univ iff Φ.realization = ∅ iff Fin.elim0 ∉ Φ.realization.
    have hC_iff : (Φ.realization (C := C))ᶜ = Set.univ ↔
                  Fin.elim0 ∉ Φ.realization (C := C) := by
      rw [set_finZero_eq_univ_iff]
      simp
    have hC'_iff : (Φ.realization (C := C'))ᶜ = Set.univ ↔
                   Fin.elim0 ∉ Φ.realization (C := C') := by
      rw [set_finZero_eq_univ_iff]
      simp
    have hΦ : Fin.elim0 ∈ Φ.realization (C := C) ↔
              Fin.elim0 ∈ Φ.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih hQF'
    show (Φ.realization (C := C))ᶜ = Set.univ ↔
         (Φ.realization (C := C'))ᶜ = Set.univ
    rw [hC_iff, hC'_iff, not_iff_not]
    exact hΦ
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have h1 : Fin.elim0 ∈ Φ₁.realization (C := C) ↔
              Fin.elim0 ∈ Φ₁.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₁ hQF₁
    have h2 : Fin.elim0 ∈ Φ₂.realization (C := C) ↔
              Fin.elim0 ∈ Φ₂.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₂ hQF₂
    show Φ₁.realization (C := C) ∩ Φ₂.realization (C := C) = Set.univ ↔
         Φ₁.realization (C := C') ∩ Φ₂.realization (C := C') = Set.univ
    rw [set_finZero_eq_univ_iff, set_finZero_eq_univ_iff]
    simp only [Set.mem_inter_iff]
    exact and_congr h1 h2
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have h1 : Fin.elim0 ∈ Φ₁.realization (C := C) ↔
              Fin.elim0 ∈ Φ₁.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₁ hQF₁
    have h2 : Fin.elim0 ∈ Φ₂.realization (C := C) ↔
              Fin.elim0 ∈ Φ₂.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₂ hQF₂
    show Φ₁.realization (C := C) ∪ Φ₂.realization (C := C) = Set.univ ↔
         Φ₁.realization (C := C') ∪ Φ₂.realization (C := C') = Set.univ
    rw [set_finZero_eq_univ_iff, set_finZero_eq_univ_iff]
    simp only [Set.mem_union]
    exact or_congr h1 h2
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have h1 : Fin.elim0 ∈ Φ₁.realization (C := C) ↔
              Fin.elim0 ∈ Φ₁.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₁ hQF₁
    have h2 : Fin.elim0 ∈ Φ₂.realization (C := C) ↔
              Fin.elim0 ∈ Φ₂.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₂ hQF₂
    show (Φ₁.realization (C := C))ᶜ ∪ Φ₂.realization (C := C) = Set.univ ↔
         (Φ₁.realization (C := C'))ᶜ ∪ Φ₂.realization (C := C') = Set.univ
    rw [set_finZero_eq_univ_iff, set_finZero_eq_univ_iff]
    simp only [Set.mem_union, Set.mem_compl_iff]
    exact or_congr (not_congr h1) h2
  | exists_ _ _ _ => exact absurd hQF id
  | forall_ _ _ _ => exact absurd hQF id

/-- **BPR Theorem 1.26 (Lefschetz principle).** A sentence in the language
of fields with coefficients in the algebraically closed field `C` is true in
`C` if and only if it is true in any algebraically closed extension `C'`. -/
theorem theorem_1_26 [Algebra C C']
    (Φ : Formula (Fin 0) (FieldAtom (Fin 0) C)) :
    Φ.realization (C := C) = Set.univ ↔ Φ.realization (C := C') = Set.univ := by
  have hinjC : Function.Injective (algebraMap C C) := Function.injective_id
  have hinjC' : Function.Injective (algebraMap C C') :=
    RingHom.injective (algebraMap C C')
  obtain ⟨Ψ, hQF, hΨC, hΨC'⟩ :=
    theorem_1_23_two_fields (D := C) (C := C) (C' := C') hinjC hinjC' Φ
  rw [hΨC, hΨC']
  exact qf_finZero_realization_transfer Ψ hQF

end MainTheorem

/-!
### Strong Lefschetz: two algebraically closed fields of the same characteristic

We generalize `theorem_1_26` to the case where `C` and `C'` are *not* assumed
to be related by an inclusion `Algebra C C'`. Instead, we use the
"two parallel rails" pattern of `theorem_1_23_two_fields`: a common
coefficient domain `D` with injective algebra maps into both `C` and `C'`.

For sentences over `Fin 0`, polynomials in `MvPolynomial (Fin 0) D` are
constants — `aeval Fin.elim0 P = algebraMap D K (constantCoeff P)`. So the
atoms `P = 0` and `P ≠ 0` reduce to the *same* condition on `constantCoeff P`
in both fields (using injectivity on each side).
-/

section StrongLefschetz

/-- For any algebra `D → K`, evaluation of a `MvPolynomial (Fin 0) D` at
`Fin.elim0 : Fin 0 → K` factors through the constant coefficient: it equals
`algebraMap D K (constantCoeff P)`. -/
theorem aeval_finZero_eq_algebraMap_constantCoeff
    {D K : Type*} [CommSemiring D] [CommSemiring K] [Algebra D K]
    (P : MvPolynomial (Fin 0) D) :
    (MvPolynomial.aeval (Fin.elim0 : Fin 0 → K)) P =
      algebraMap D K (MvPolynomial.constantCoeff P) := by
  apply MvPolynomial.aeval_eq_constantCoeff_of_vars
  intro i _
  exact Fin.elim0 i

/-- **Generalized QF transfer.** A QF formula `Ψ` over `Fin 0` with
coefficients in a common domain `D` has the same truth value over any two
fields `C` and `C'` admitting injective algebra maps from `D`. -/
theorem qf_finZero_realization_transfer_general
    {D C C' : Type*} [CommRing D] [Field C] [Field C']
    [Algebra D C] [Algebra D C']
    (hinj_C : Function.Injective (algebraMap D C))
    (hinj_C' : Function.Injective (algebraMap D C'))
    {Ψ : Formula (Fin 0) (FieldAtom (Fin 0) D)}
    (hQF : Ψ.IsQuantifierFree) :
    Ψ.realization (C := C) = Set.univ ↔
    Ψ.realization (C := C') = Set.univ := by
  induction Ψ with
  | atom a =>
    rw [set_finZero_eq_univ_iff, set_finZero_eq_univ_iff]
    have hC : MvPolynomial.aeval (Fin.elim0 : Fin 0 → C) a.poly =
        algebraMap D C (MvPolynomial.constantCoeff a.poly) :=
      aeval_finZero_eq_algebraMap_constantCoeff (D := D) (K := C) a.poly
    have hC' : MvPolynomial.aeval (Fin.elim0 : Fin 0 → C') a.poly =
        algebraMap D C' (MvPolynomial.constantCoeff a.poly) :=
      aeval_finZero_eq_algebraMap_constantCoeff (D := D) (K := C') a.poly
    -- Both atoms `P = 0` and `P ≠ 0` reduce to the same condition on
    -- `constantCoeff a.poly` via injectivity of `algebraMap D ·`.
    have hC_iff : MvPolynomial.aeval (Fin.elim0 : Fin 0 → C) a.poly = 0 ↔
        MvPolynomial.constantCoeff a.poly = 0 := by
      rw [hC]
      exact ⟨fun h => hinj_C (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
    have hC'_iff : MvPolynomial.aeval (Fin.elim0 : Fin 0 → C') a.poly = 0 ↔
        MvPolynomial.constantCoeff a.poly = 0 := by
      rw [hC']
      exact ⟨fun h => hinj_C' (by rw [h, map_zero]),
        fun h => by rw [h, map_zero]⟩
    rcases hb : a.isEq with _ | _
    · -- atom is "≠ 0"
      simp only [Formula.realization, Formula.interpret_fieldAtom, hb,
        Bool.false_eq_true, ite_false, Set.mem_ofPred_eq]
      exact not_congr hC_iff |>.trans (not_congr hC'_iff).symm
    · -- atom is "= 0"
      simp only [Formula.realization, Formula.interpret_fieldAtom, hb,
        ite_true, Set.mem_ofPred_eq]
      rw [hC_iff, hC'_iff]
  | not Φ ih =>
    have hQF' : Φ.IsQuantifierFree := hQF
    have hC_iff : (Φ.realization (C := C))ᶜ = Set.univ ↔
                  Fin.elim0 ∉ Φ.realization (C := C) := by
      rw [set_finZero_eq_univ_iff]; simp
    have hC'_iff : (Φ.realization (C := C'))ᶜ = Set.univ ↔
                   Fin.elim0 ∉ Φ.realization (C := C') := by
      rw [set_finZero_eq_univ_iff]; simp
    have hΦ : Fin.elim0 ∈ Φ.realization (C := C) ↔
              Fin.elim0 ∈ Φ.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih hQF'
    show (Φ.realization (C := C))ᶜ = Set.univ ↔
         (Φ.realization (C := C'))ᶜ = Set.univ
    rw [hC_iff, hC'_iff, not_iff_not]
    exact hΦ
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have h1 : Fin.elim0 ∈ Φ₁.realization (C := C) ↔
              Fin.elim0 ∈ Φ₁.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₁ hQF₁
    have h2 : Fin.elim0 ∈ Φ₂.realization (C := C) ↔
              Fin.elim0 ∈ Φ₂.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₂ hQF₂
    show Φ₁.realization (C := C) ∩ Φ₂.realization (C := C) = Set.univ ↔
         Φ₁.realization (C := C') ∩ Φ₂.realization (C := C') = Set.univ
    rw [set_finZero_eq_univ_iff, set_finZero_eq_univ_iff]
    simp only [Set.mem_inter_iff]
    exact and_congr h1 h2
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have h1 : Fin.elim0 ∈ Φ₁.realization (C := C) ↔
              Fin.elim0 ∈ Φ₁.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₁ hQF₁
    have h2 : Fin.elim0 ∈ Φ₂.realization (C := C) ↔
              Fin.elim0 ∈ Φ₂.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₂ hQF₂
    show Φ₁.realization (C := C) ∪ Φ₂.realization (C := C) = Set.univ ↔
         Φ₁.realization (C := C') ∪ Φ₂.realization (C := C') = Set.univ
    rw [set_finZero_eq_univ_iff, set_finZero_eq_univ_iff]
    simp only [Set.mem_union]
    exact or_congr h1 h2
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have h1 : Fin.elim0 ∈ Φ₁.realization (C := C) ↔
              Fin.elim0 ∈ Φ₁.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₁ hQF₁
    have h2 : Fin.elim0 ∈ Φ₂.realization (C := C) ↔
              Fin.elim0 ∈ Φ₂.realization (C := C') := by
      rw [← set_finZero_eq_univ_iff, ← set_finZero_eq_univ_iff]
      exact ih₂ hQF₂
    show (Φ₁.realization (C := C))ᶜ ∪ Φ₂.realization (C := C) = Set.univ ↔
         (Φ₁.realization (C := C'))ᶜ ∪ Φ₂.realization (C := C') = Set.univ
    rw [set_finZero_eq_univ_iff, set_finZero_eq_univ_iff]
    simp only [Set.mem_union, Set.mem_compl_iff]
    exact or_congr (not_congr h1) h2
  | exists_ _ _ _ => exact absurd hQF id
  | forall_ _ _ _ => exact absurd hQF id

/-- **BPR Theorem 1.26 (strong Lefschetz form).** Two algebraically
closed fields admitting injective ring homomorphisms from a common
integral domain `D` agree on sentences with coefficients in `D`. -/
theorem theorem_1_26_general
    {D C C' : Type*} [CommRing D] [IsDomain D]
    [Field C] [Field C'] [IsAlgClosed C] [IsAlgClosed C']
    [Algebra D C] [Algebra D C']
    (hinj_C : Function.Injective (algebraMap D C))
    (hinj_C' : Function.Injective (algebraMap D C'))
    {Φ : Formula (Fin 0) (FieldAtom (Fin 0) D)} :
    Φ.realization (C := C) = Set.univ ↔
    Φ.realization (C := C') = Set.univ := by
  obtain ⟨Ψ, hQF, hΨC, hΨC'⟩ :=
    theorem_1_23_two_fields (D := D) (C := C) (C' := C') hinj_C hinj_C' Φ
  rw [hΨC, hΨC']
  exact qf_finZero_realization_transfer_general hinj_C hinj_C' hQF

/-- Two algebraically closed fields of the same prime characteristic
agree on sentences with `ZMod p` coefficients. -/
theorem theorem_1_26_same_charP
    (p : ℕ) [hp : Fact p.Prime]
    {C C' : Type*} [Field C] [Field C'] [IsAlgClosed C] [IsAlgClosed C']
    [CharP C p] [CharP C' p]
    {Φ : Formula (Fin 0) (FieldAtom (Fin 0) (ZMod p))} :
    letI : Algebra (ZMod p) C := ZMod.algebra C p
    letI : Algebra (ZMod p) C' := ZMod.algebra C' p
    Φ.realization (C := C) = Set.univ ↔
    Φ.realization (C := C') = Set.univ := by
  let : Algebra (ZMod p) C := ZMod.algebra C p
  let : Algebra (ZMod p) C' := ZMod.algebra C' p
  have hinj_C : Function.Injective (algebraMap (ZMod p) C) :=
    ZMod.castHom_injective C
  have hinj_C' : Function.Injective (algebraMap (ZMod p) C') :=
    ZMod.castHom_injective C'
  exact theorem_1_26_general (D := ZMod p) (C := C) (C' := C')
    hinj_C hinj_C' (Φ := Φ)

/-- Two algebraically closed fields of characteristic 0 agree on
sentences with `ℚ` coefficients. -/
theorem theorem_1_26_same_charZero
    {C C' : Type*} [Field C] [Field C'] [IsAlgClosed C] [IsAlgClosed C']
    [CharZero C] [CharZero C']
    {Φ : Formula (Fin 0) (FieldAtom (Fin 0) ℚ)} :
    Φ.realization (C := C) = Set.univ ↔
    Φ.realization (C := C') = Set.univ := by
  have hinj_C : Function.Injective (algebraMap ℚ C) :=
    RingHom.injective _
  have hinj_C' : Function.Injective (algebraMap ℚ C') :=
    RingHom.injective _
  exact theorem_1_26_general (D := ℚ) (C := C) (C' := C')
    hinj_C hinj_C' (Φ := Φ)

end StrongLefschetz

end Azurite.BPR
