/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization

/-!
# Variable renaming and realization invariance

Lemmas relating `realization` to variable renaming and to updates of the
assignment outside the formula's free variables.

* `rename_realization` -- the realization of a renamed formula is the
  preimage of the original realization along the renaming.
* `aeval_update_of_not_mem_vars` -- evaluating a polynomial at an updated
  assignment agrees with the unupdated assignment when the updated
  variable doesn't appear in the polynomial.
* `realization_invariant_update` -- updating the assignment at a variable
  not in the free-variable set leaves the realization invariant.
* `exists_and_equiv` and `forall_and_equiv` -- the quantifier-and-conjunction
  distribution laws when the conjoined formula doesn't depend on the bound
  variable.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]
variable {C : Type*} [Field C] [Algebra D C]

theorem rename_realization [DecidableEq σ] [DecidableEq τ]
    (f : σ → τ) (hf : Function.Injective f)
    (Φ : Formula σ (FieldAtom σ D)) :
    (Φ.rename f (FieldAtom.renameVars f)).realization (C := C) =
      (· ∘ f) ⁻¹' Φ.realization := by
  induction Φ with
  | atom a =>
    ext y; cases a with | mk P b =>
    cases b <;> simp [rename, FieldAtom.renameVars,
      realization, aeval_rename]
  | not _ ih =>
    simp [rename, realization, ih, Set.preimage_compl]
  | and _ _ ih₁ ih₂ =>
    simp [rename, realization, ih₁, ih₂,
      Set.preimage_inter]
  | or _ _ ih₁ ih₂ =>
    simp [rename, realization, ih₁, ih₂,
      Set.preimage_union]
  | implies _ _ ih₁ ih₂ =>
    simp [rename, realization, ih₁, ih₂,
      Set.preimage_union, Set.preimage_compl]
  | exists_ x _ ih =>
    ext y
    simp only [rename, realization, Set.mem_ofPred_eq,
      Set.mem_preimage, ih]
    constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, ?_⟩ <;>
    · convert hc using 1; ext i
      simp [Function.update, hf.eq_iff]
  | forall_ x _ ih =>
    ext y
    simp only [rename, realization, Set.mem_ofPred_eq,
      Set.mem_preimage, ih]
    constructor <;> intro hc <;> intro c <;>
    · have := hc c; convert this using 1; ext i
      simp [Function.update, hf.eq_iff]

theorem aeval_update_of_not_mem_vars
    [DecidableEq σ] (P : MvPolynomial σ D)
    (y : σ → C) (x : σ) (c : C) (hx : x ∉ P.vars) :
    aeval (Function.update y x c) P = aeval y P := by
  simp only [MvPolynomial.aeval_def]
  apply MvPolynomial.eval₂_congr
  intro i ci hi hci
  have : i ≠ x := by
    intro h; apply hx; subst h
    rw [MvPolynomial.mem_vars_iff_mem_support]
    exact ⟨ci, P.mem_support_iff.mpr hci, hi⟩
  simp [this]

theorem realization_invariant_update [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (x : σ) (hx : x ∉ Φ.freeVars)
    (y : σ → C) (c : C) :
    y ∈ Φ.realization (C := C) ↔
    Function.update y x c ∈ Φ.realization := by
  induction Φ generalizing y with
  | atom a =>
    simp only [realization, freeVars, AtomVars.vars_fieldAtom,
      FieldAtom.vars, interpret_fieldAtom] at *
    split <;> simp only [Set.mem_ofPred_eq] <;>
    rw [aeval_update_of_not_mem_vars a.poly y x c hx]
  | not _ ih =>
    simp only [realization, Set.mem_compl_iff, freeVars] at *
    rw [ih hx]
  | and _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_inter_iff, freeVars,
      Finset.mem_union, not_or] at *
    rw [ih₁ hx.1, ih₂ hx.2]
  | or _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_union, freeVars,
      Finset.mem_union, not_or] at *
    rw [ih₁ hx.1, ih₂ hx.2]
  | implies _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_union, Set.mem_compl_iff, freeVars,
      Finset.mem_union, not_or] at *
    rw [ih₁ hx.1, ih₂ hx.2]
  | exists_ z _ ih =>
    simp only [realization, Set.mem_ofPred_eq, freeVars,
      Finset.mem_sdiff, Finset.mem_singleton] at *
    push Not at hx
    constructor <;> rintro ⟨d, hd⟩ <;> refine ⟨d, ?_⟩
    · by_cases hxz : x = z
      · subst hxz; rwa [Function.update_idem]
      · rw [Function.update_comm hxz]
        rwa [← ih (fun hmem => absurd (hx hmem) hxz)]
    · by_cases hxz : x = z
      · subst hxz; rwa [Function.update_idem] at hd
      · rw [Function.update_comm hxz] at hd
        rwa [ih (fun hmem => absurd (hx hmem) hxz)]
  | forall_ z _ ih =>
    simp only [realization, Set.mem_ofPred_eq, freeVars,
      Finset.mem_sdiff, Finset.mem_singleton] at *
    push Not at hx
    constructor
    · intro hd d
      by_cases hxz : x = z
      · subst hxz; rw [Function.update_idem]; exact hd d
      · rw [Function.update_comm hxz]
        exact (ih (fun hmem => absurd (hx hmem) hxz) _).mp (hd d)
    · intro hd d
      by_cases hxz : x = z
      · subst hxz
        have := hd d; rw [Function.update_idem] at this; exact this
      · have := hd d; rw [Function.update_comm hxz] at this
        exact (ih (fun hmem => absurd (hx hmem) hxz) _).mpr this

/-- (∃x, A) ∧ B ≡ ∃x, (A ∧ B) when x ∉ freeVars B. -/
theorem exists_and_equiv [DecidableEq σ]
    (A B : Formula σ (FieldAtom σ D)) (x : σ) (hx : x ∉ B.freeVars) :
    (Formula.exists_ x A).realization (C := C) ∩ B.realization =
    (Formula.exists_ x (Formula.and A B)).realization := by
  ext y
  simp only [realization, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨c, hc⟩, hB⟩
    exact ⟨c, hc,
      (realization_invariant_update B x hx y c).mp hB⟩
  · rintro ⟨c, hA, hB⟩
    exact ⟨⟨c, hA⟩,
      (realization_invariant_update B x hx y c).mpr hB⟩

/-- (∀x, A) ∧ B ≡ ∀x, (A ∧ B) when x ∉ freeVars B. -/
theorem forall_and_equiv [DecidableEq σ]
    (A B : Formula σ (FieldAtom σ D)) (x : σ) (hx : x ∉ B.freeVars) :
    (Formula.forall_ x A).realization (C := C) ∩
      B.realization =
    (Formula.forall_ x (Formula.and A B)).realization := by
  ext y
  simp only [realization, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hA, hB⟩ c
    exact ⟨hA c,
      (realization_invariant_update B x hx y c).mp hB⟩
  · intro h
    exact ⟨fun c => (h c).1,
      by have := (h (y x)).2
         rw [Function.update_eq_self] at this; exact this⟩

end Formula

end Azurite.BPR
