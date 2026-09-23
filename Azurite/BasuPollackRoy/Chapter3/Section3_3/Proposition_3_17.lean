/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_16
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Theorem_2_77
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Theorem_2_80
import Azurite.BasuPollackRoy.Chapter2.Section2_3.OrderedSentences

/-! # BPR §3.3 — Proposition 3.17: truth of an `R[ε]`-sentence in `R⟨ε⟩`

A sentence `Φ` in the language of ordered fields with coefficients in `R[ε]` is true in
`R⟨ε⟩` (the germ field, `ε ↦ idGerm`) iff there is `t₀ > 0` such that `Φ′(t)` (substitute `t` for
`ε`) is true in `R` for every `t ∈ (0, t₀)`.

The proof internalizes the coefficient `ε` as a fresh variable (`reifyFormula`): `Φ` over
`R[ε] = Polynomial R` becomes a formula `Φ̂` over `R` with one extra variable (coordinate `0`) for
`ε`. The substitution principle `reify_realization` shows that evaluating `Φ̂` at a point `v` with
`v 0 = c` is the same as realizing `Φ` with `ε ↦ c`. Quantifier elimination (Theorem 2.77) makes
`Φ̂` quantifier-free, and Proposition 3.16's `realization_bridge` (with the single germ `idGerm` for
`ε`) finishes. -/

namespace Azurite.BPR

open MvPolynomial Formula

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Internalize `ε` as the variable `X 0` and shift the old variables `X i ↦ X i.succ`: a polynomial
in `R[ε][X₁,…,X_k]` becomes one in `R[X₀,…,X_k]`. -/
noncomputable def reifyPoly (P : MvPolynomial (Fin k) (Polynomial R)) :
    MvPolynomial (Fin (k + 1)) R :=
  MvPolynomial.eval₂Hom
    (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin (k + 1)) R)).toRingHom
    (fun i => MvPolynomial.X i.succ) P

variable {C : Type*} [Field C] [LinearOrder C] [IsStrictOrderedRing C] [Algebra R C]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder C] [IsStrictOrderedRing C] in
/-- **Key polynomial identity.** Evaluating the reified polynomial at `v` equals evaluating the
original at `v ∘ succ` with the coefficient `ε ↦ v 0`. -/
theorem reifyPoly_aeval (P : MvPolynomial (Fin k) (Polynomial R)) (v : Fin (k + 1) → C) :
    MvPolynomial.aeval v (reifyPoly P)
      = MvPolynomial.aeval (v ∘ Fin.succ) (P.map (Polynomial.aeval (v 0)).toRingHom) := by
  have key : (MvPolynomial.aeval v).toRingHom.comp
        (MvPolynomial.eval₂Hom
          (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin (k + 1)) R)).toRingHom
          (fun i => MvPolynomial.X i.succ))
      = (MvPolynomial.aeval (R := C) (v ∘ Fin.succ)).toRingHom.comp
          (MvPolynomial.map (σ := Fin k)
            ((Polynomial.aeval (v 0)).toRingHom : Polynomial R →+* C)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C]
      rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X, Algebra.algebraMap_self_apply]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_X, Function.comp_apply]
  rw [reifyPoly]
  exact DFunLike.congr_fun key P

/-- The atom-level coefficient substitution `ε ↦ c`: map each polynomial's `R[ε]`-coefficients to `C`
by evaluating `ε ↦ c`. -/
noncomputable def substAtom (c : C) :
    OrderedFieldAtom (Fin k) (Polynomial R) → OrderedFieldAtom (Fin k) C :=
  fun a => ⟨a.poly.map (Polynomial.aeval c).toRingHom, a.rel⟩

/-- **The reification** of a formula over `R[ε]` (variables `Fin k`) as a formula over `R`
(variables `Fin (k+1)`, coordinate `0` standing for `ε`). -/
noncomputable def reifyFormula :
    Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R)) →
      Formula (Fin (k + 1)) (OrderedFieldAtom (Fin (k + 1)) R)
  | .atom ⟨P, rel⟩ => .atom ⟨reifyPoly P, rel⟩
  | .not Φ => .not (reifyFormula Φ)
  | .and Φ₁ Φ₂ => .and (reifyFormula Φ₁) (reifyFormula Φ₂)
  | .or Φ₁ Φ₂ => .or (reifyFormula Φ₁) (reifyFormula Φ₂)
  | .implies Φ₁ Φ₂ => .implies (reifyFormula Φ₁) (reifyFormula Φ₂)
  | .exists_ i Φ => .exists_ i.succ (reifyFormula Φ)
  | .forall_ i Φ => .forall_ i.succ (reifyFormula Φ)

omit [Field C] [LinearOrder C] [IsStrictOrderedRing C] in
theorem update_comp_succ (v : Fin (k + 1) → C) (i : Fin k) (c : C) :
    (Function.update v i.succ c) ∘ Fin.succ = Function.update (v ∘ Fin.succ) i c := by
  funext j
  rcases eq_or_ne j i with h | h
  · subst h; simp
  · rw [Function.comp_apply, Function.update_of_ne ((Fin.succ_injective k).ne h),
      Function.update_of_ne h, Function.comp_apply]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **Substitution principle.** A point `v` satisfies `reifyFormula Φ` over `C` iff `v ∘ succ`
satisfies `Φ` with `ε ↦ v 0`. -/
theorem reify_realization (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R)))
    (v : Fin (k + 1) → C) :
    v ∈ (reifyFormula Φ).realization (C := C)
      ↔ (v ∘ Fin.succ) ∈ (Φ.mapAtom (substAtom (v 0))).realization (C := C) := by
  induction Φ generalizing v with
  | atom a =>
    obtain ⟨P, rel⟩ := a
    show v ∈ AtomRealization.interpret (⟨reifyPoly P, rel⟩ : OrderedFieldAtom (Fin (k + 1)) R)
      ↔ (v ∘ Fin.succ) ∈ AtomRealization.interpret (substAtom (v 0) ⟨P, rel⟩)
    rw [substAtom]
    cases rel <;>
      simp only [AtomRealization.interpret, Set.mem_ofPred_eq, reifyPoly_aeval]
  | not Φ ih =>
    show v ∈ ((reifyFormula Φ).realization)ᶜ ↔ _
    rw [Set.mem_compl_iff, ih]
    rfl
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    show v ∈ (reifyFormula Φ₁).realization ∩ (reifyFormula Φ₂).realization ↔ _
    rw [Set.mem_inter_iff, ih₁, ih₂]
    rfl
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    show v ∈ (reifyFormula Φ₁).realization ∪ (reifyFormula Φ₂).realization ↔ _
    rw [Set.mem_union, ih₁, ih₂]
    rfl
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    show v ∈ ((reifyFormula Φ₁).realization)ᶜ ∪ (reifyFormula Φ₂).realization ↔ _
    rw [Set.mem_union, Set.mem_compl_iff, ih₁, ih₂]
    rfl
  | exists_ i Φ ih =>
    have hkey : ∀ c : C, Function.update v i.succ c ∈ (reifyFormula Φ).realization
        ↔ Function.update (v ∘ Fin.succ) i c ∈ (Φ.mapAtom (substAtom (v 0))).realization := by
      intro c
      rw [ih, show (Function.update v i.succ c) 0 = v 0 from
        Function.update_of_ne (Fin.succ_ne_zero i).symm _ _, update_comp_succ v i c]
    show (∃ c, Function.update v i.succ c ∈ (reifyFormula Φ).realization)
      ↔ (∃ c, Function.update (v ∘ Fin.succ) i c ∈ (Φ.mapAtom (substAtom (v 0))).realization)
    exact exists_congr hkey
  | forall_ i Φ ih =>
    have hkey : ∀ c : C, Function.update v i.succ c ∈ (reifyFormula Φ).realization
        ↔ Function.update (v ∘ Fin.succ) i c ∈ (Φ.mapAtom (substAtom (v 0))).realization := by
      intro c
      rw [ih, show (Function.update v i.succ c) 0 = v 0 from
        Function.update_of_ne (Fin.succ_ne_zero i).symm _ _, update_comp_succ v i c]
    show (∀ c, Function.update v i.succ c ∈ (reifyFormula Φ).realization)
      ↔ (∀ c, Function.update (v ∘ Fin.succ) i c ∈ (Φ.mapAtom (substAtom (v 0))).realization)
    exact forall_congr' hkey

/-! ### Sentence preservation and the connection lemmas -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder C] [IsStrictOrderedRing C] in
/-- The coefficient substitution `ε ↦ c` can only shrink the free variables. -/
theorem freeVars_mapAtom_substAtom (c : C)
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R))) :
    (Φ.mapAtom (substAtom c)).freeVars ⊆ Φ.freeVars := by
  induction Φ with
  | atom a =>
    obtain ⟨P, rel⟩ := a
    simp only [Formula.mapAtom, substAtom, Formula.freeVars, AtomVars.vars_orderedFieldAtom,
      OrderedFieldAtom.vars]
    exact MvPolynomial.vars_map _ _
  | not _ ih => simpa only [Formula.mapAtom, Formula.freeVars] using ih
  | and _ _ ih₁ ih₂ =>
    simp only [Formula.mapAtom, Formula.freeVars]; exact Finset.union_subset_union ih₁ ih₂
  | or _ _ ih₁ ih₂ =>
    simp only [Formula.mapAtom, Formula.freeVars]; exact Finset.union_subset_union ih₁ ih₂
  | implies _ _ ih₁ ih₂ =>
    simp only [Formula.mapAtom, Formula.freeVars]; exact Finset.union_subset_union ih₁ ih₂
  | exists_ x _ ih =>
    simp only [Formula.mapAtom, Formula.freeVars]; exact Finset.sdiff_subset_sdiff ih subset_rfl
  | forall_ x _ ih =>
    simp only [Formula.mapAtom, Formula.freeVars]; exact Finset.sdiff_subset_sdiff ih subset_rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] [LinearOrder C] [IsStrictOrderedRing C] in
theorem isSentence_mapAtom_substAtom (c : C)
    {Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R))} (hΦ : Formula.isSentence Φ) :
    Formula.isSentence (Φ.mapAtom (substAtom c)) :=
  Finset.subset_empty.mp (hΦ ▸ freeVars_mapAtom_substAtom c Φ)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- For a sentence, a point lies in the substituted realization iff `Φ′(c)` is true. -/
theorem mem_realization_iff_isTrue
    {Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R))} (hΦ : Formula.isSentence Φ)
    (c : C) (w : Fin k → C) :
    w ∈ (Φ.mapAtom (substAtom c)).realization (C := C)
      ↔ (Φ.mapAtom (substAtom c)).IsTrue (C := C) := by
  constructor
  · intro h
    exact (Formula.isTrue_iff_nonempty_of_isSentence _ (isSentence_mapAtom_substAtom c hΦ)).mpr ⟨w, h⟩
  · intro h; rw [Formula.IsTrue] at h; rw [h]; trivial

/-- `ε ↦ idGerm`: the algebra making `R⟨ε⟩ = SemialgGerm R` an `R[ε]`-algebra with `ε` the germ of
the identity. -/
noncomputable instance instAlgebraPolynomialSemialgGerm :
    Algebra (Polynomial R) (SemialgGerm R) := (Polynomial.aeval (idGerm : SemialgGerm R)).toAlgebra

/-- **Germ connection.** A point `v` with `v 0 = ε` satisfies `reifyFormula Φ` over `R⟨ε⟩` iff the
sentence `Φ` is true in `R⟨ε⟩`. -/
theorem reify_germ_iff (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R)))
    (hΦ : Formula.isSentence Φ) (v : Fin (k + 1) → SemialgGerm R) (hv : v 0 = idGerm) :
    v ∈ (reifyFormula Φ).realization (C := SemialgGerm R)
      ↔ Φ.IsTrue (C := SemialgGerm R) := by
  rw [reify_realization, hv,
    show Φ.mapAtom (substAtom (idGerm : SemialgGerm R)) = Φ.mapCoeffO (D' := SemialgGerm R) from rfl,
    realization_mapCoeffO]
  constructor
  · intro h; exact (Formula.isTrue_iff_nonempty_of_isSentence _ hΦ).mpr ⟨_, h⟩
  · intro h; rw [Formula.IsTrue] at h; rw [h]; trivial

omit [IsRealClosed R] in
/-- **Real connection.** A point `v` with `v 0 = t` satisfies `reifyFormula Φ` over `R` iff `Φ′(t)`
is true in `R`. -/
theorem reify_R_iff (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R)))
    (hΦ : Formula.isSentence Φ) (v : Fin (k + 1) → R) (t : R) (hv : v 0 = t) :
    v ∈ (reifyFormula Φ).realization (C := R) ↔ (Φ.mapAtom (substAtom t)).IsTrue (C := R) := by
  rw [reify_realization, hv]
  exact mem_realization_iff_isTrue hΦ t _

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem EvNhd_congr {P Q : R → Prop} (h : ∀ s, P s ↔ Q s) : EvNhd P ↔ EvNhd Q :=
  ⟨fun hp => hp.mono fun s => (h s).mp, fun hq => hq.mono fun s => (h s).mpr⟩

/-! ### Proposition 3.17 -/

/-- **BPR Proposition 3.17.** Let `Φ` be a sentence in the language of ordered fields with
coefficients in `R[ε]`, and let `Φ′(t)` be obtained by substituting `t ∈ R` for `ε`. Then `Φ` is true
in `R⟨ε⟩` (the germ field, `ε ↦ idGerm`) iff there is `t₀ > 0` with `Φ′(t)` true for every
`t ∈ (0, t₀)`. -/
theorem proposition_3_17 (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) (Polynomial R)))
    (hΦ : Formula.isSentence Φ) :
    Φ.IsTrue (C := SemialgGerm R)
      ↔ ∃ t₀ : R, 0 < t₀ ∧ ∀ t : R, 0 < t → t < t₀ → (Φ.mapAtom (substAtom t)).IsTrue (C := R) := by
  have : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  obtain ⟨Ψ, hΨqf, hΨR⟩ := theorem_2_77 (D := R) (R := R) Function.injective_id (reifyFormula Φ)
  have hΨgerm : (reifyFormula Φ).realization (C := SemialgGerm R)
      = Ψ.realization (C := SemialgGerm R) :=
    ext_well_defined (reifyFormula Φ) Ψ hΨR
  have key := realization_bridge (1 : R) one_pos (fun _ : Fin (k + 1) => idSub (1 : R)) Ψ hΨqf
  rw [show (fun i : Fin (k + 1) =>
        germHom (1 : R) one_pos ((fun _ => idSub (1 : R)) i)) = fun _ => idGerm from by
      funext i; exact germHom_idSub 1 one_pos,
    ← hΨgerm, reify_germ_iff Φ hΦ (fun _ => idGerm) rfl] at key
  rw [key]
  refine EvNhd_congr fun s => ?_
  rw [← hΨR]
  exact reify_R_iff Φ hΦ _ s rfl

end Azurite.BPR
