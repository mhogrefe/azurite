/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.StratumB

/-! # BPR Theorem 2.77: Quantifier Elimination over Real Closed Fields

**Theorem 2.77.** Let `Φ(Y)` be a formula in the language of ordered fields with
coefficients in an ordered ring `D` contained in the real closed field `R`. Then
there is a quantifier-free formula `Ψ(Y)` with coefficients in `D` such that for
every `y ∈ Rᵏ`, `Φ(y)` holds iff `Ψ(y)` holds.

## Proof outline

We work with the inductive `Formula (Fin k) (OrderedFieldAtom (Fin k) D)` type
(`exists_`/`forall_` quantify over coordinates of `Fin k → R`). The key fact
(`formula_realization_isSemialgebraicSetOver`) is that the realization of **every**
formula is semialgebraic over `D`, proved by structural induction:

* atoms are the six sign/zero loci, each semialgebraic over `D`;
* `not`/`and`/`or`/`implies` use closure of semialgebraic-over-`D` sets under
  complement/intersection/union;
* `exists_ x Φ` projects out coordinate `x` — this is the content of **Theorem 2.76**:
  `IsSemialgebraicSetOver.exists_update` shows the cylindrical projection
  `{y | ∃ c, update y x c ∈ V}` is semialgebraic over `D` (swap `x` to the last
  coordinate, then `theorem_2_76` and the pullback lemma `IsSemialgebraicSetOver.comap`);
* `forall_ x Φ ≡ ¬ ∃ x, ¬ Φ`, reducing to the existential case.

Then `semialgebraic_isQFRealizableOver` turns the realization back into a
quantifier-free formula over `D` (`theorem_2_77`).
-/

open _root_.Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {D : Type*} [CommRing D] [IsDomain D] [Algebra D R]

omit [IsStrictOrderedRing R] [IsRealClosed R] [IsDomain D] in
/-- **Pullback along a variable reindexing.** If `W` is semialgebraic over `D`, so is
its preimage `{y | y ∘ g ∈ W}` under the coordinate map `g : Fin a → Fin b` — push each
witness polynomial through `MvPolynomial.rename g`. -/
theorem IsSemialgebraicSetOver.comap {a b : ℕ} (g : Fin a → Fin b)
    {W : Set (Fin a → R)} (hW : IsSemialgebraicSetOver D W) :
    IsSemialgebraicSetOver D {y : Fin b → R | y ∘ g ∈ W} := by
  classical
  induction hW with
  | algebraic h =>
    obtain ⟨ps, rfl⟩ := h
    refine .algebraic ⟨ps.image (MvPolynomial.rename g), ?_⟩
    ext y; simp only [Set.mem_ofPred_eq, Finset.mem_image]
    constructor
    · rintro hy Q ⟨P, hP, rfl⟩
      rw [MvPolynomial.aeval_rename]; exact hy P hP
    · intro hy P hP
      have := hy (MvPolynomial.rename g P) ⟨P, hP, rfl⟩
      rwa [MvPolynomial.aeval_rename] at this
  | pos_locus P =>
    have heq : {y : Fin b → R | y ∘ g ∈ {z | MvPolynomial.aeval z P > 0}}
        = {y : Fin b → R | MvPolynomial.aeval y (MvPolynomial.rename g P) > 0} := by
      ext y; simp only [Set.mem_ofPred_eq, MvPolynomial.aeval_rename]
    rw [heq]; exact .pos_locus _
  | compl _ ih => exact ih.compl
  | inter _ _ ih1 ih2 => exact ih1.inter ih2

/-- **Cylindrical projection preserves semialgebraicity (Theorem 2.76 in formula form).**
If `V` is semialgebraic over `D`, so is `{y | ∃ c, Function.update y x c ∈ V}` — the
realization of `∃ X_x, V`. Swap `x` to the last coordinate, then the projection is
`theorem_2_76` and the surrounding reindexings are `comap`. -/
theorem IsSemialgebraicSetOver.exists_update {k : ℕ}
    (hinj : Function.Injective (algebraMap D R)) (x : Fin k)
    {V : Set (Fin k → R)} (hV : IsSemialgebraicSetOver D V) :
    IsSemialgebraicSetOver D {y : Fin k → R | ∃ c : R, Function.update y x c ∈ V} := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by have := x.pos; omega⟩
  classical
  set e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap x (Fin.last m) with he
  have hupd : ∀ (w : Fin (m + 1) → R) (d : R),
      Function.update w (Fin.last m) d = Fin.snoc (Fin.init w) d := by
    intro w d; funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Function.update_self, Fin.snoc_last]
    · rw [Function.update_of_ne (Fin.castSucc_ne_last j), Fin.snoc_castSucc]; rfl
  have key : ∀ (y : Fin (m + 1) → R) (c : R),
      (Fin.snoc ((y ∘ ⇑e) ∘ Fin.castSucc) c) ∘ ⇑e = Function.update y x c := by
    intro y c
    have h1 : (y ∘ ⇑e) ∘ Fin.castSucc = Fin.init (y ∘ ⇑e) := rfl
    rw [h1, ← hupd (y ∘ ⇑e) c, Function.update_comp_equiv]
    have h2 : (y ∘ ⇑e) ∘ ⇑e = y := by funext i; simp [he, Equiv.swap_apply_self]
    have h3 : e.symm (Fin.last m) = x := by simp [he, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [h2, h3]
  have hFin := IsSemialgebraicSetOver.comap (⇑e)
    (IsSemialgebraicSetOver.comap (Fin.castSucc) (theorem_2_76 hinj
      (IsSemialgebraicSetOver.comap (⇑e) hV)))
  convert hFin using 1
  ext y
  simp only [Set.mem_ofPred_eq, Fin.init_image_eq_setOf_exists_snoc]
  exact exists_congr (fun c => by rw [key y c])

/-- **The realization of every formula is semialgebraic over `D`.** The substantive
half of quantifier elimination: by structural induction, atoms are sign/zero loci,
the boolean connectives use closure under complement/intersection/union, and the
quantifiers use `exists_update` (Theorem 2.76) — universally via `∀ = ¬∃¬`. -/
theorem formula_realization_isSemialgebraicSetOver {k : ℕ}
    (hinj : Function.Injective (algebraMap D R))
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) D)) :
    IsSemialgebraicSetOver D (Φ.realization (C := R)) := by
  induction Φ with
  | atom a =>
    obtain ⟨P, rel⟩ := a
    cases rel
    · exact IsSemialgebraicSetOver.eqZero P
    · exact IsSemialgebraicSetOver.neZero P
    · exact IsSemialgebraicSetOver.ltZero P
    · exact IsSemialgebraicSetOver.gtZero P
    · exact IsSemialgebraicSetOver.leZero P
    · exact IsSemialgebraicSetOver.geZero P
  | not Φ ih => exact ih.compl
  | and Φ₁ Φ₂ ih1 ih2 => exact ih1.inter ih2
  | or Φ₁ Φ₂ ih1 ih2 => exact ih1.union ih2
  | implies Φ₁ Φ₂ ih1 ih2 => exact ih1.compl.union ih2
  | exists_ x Φ ih => exact IsSemialgebraicSetOver.exists_update hinj x ih
  | forall_ x Φ ih =>
    have h := (IsSemialgebraicSetOver.exists_update hinj x ih.compl).compl
    convert h using 1
    ext y
    simp only [Formula.realization, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_not]

/-- **BPR Theorem 2.77 (Quantifier Elimination over Real Closed Fields).** Every
formula `Φ(Y)` in the language of ordered fields with coefficients in `D ⊆ R` (a real
closed field) is equivalent — same realization over `R` — to a quantifier-free formula
`Ψ(Y)` with coefficients in `D`.

The realization of `Φ` is semialgebraic over `D`
(`formula_realization_isSemialgebraicSetOver`), and every semialgebraic-over-`D` set is
the realization of a quantifier-free formula over `D`
(`semialgebraic_isQFRealizableOver`). -/
theorem theorem_2_77 {k : ℕ} (hinj : Function.Injective (algebraMap D R))
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) D)) :
    ∃ Ψ : Formula (Fin k) (OrderedFieldAtom (Fin k) D),
      Ψ.IsQuantifierFree ∧ Φ.realization (C := R) = Ψ.realization (C := R) :=
  semialgebraic_isQFRealizableOver _ (formula_realization_isSemialgebraicSetOver hinj Φ)

/-- **BPR Corollary 2.78.** For a formula `Φ(Y)` in the language of ordered fields with
coefficients in `D ⊆ R`, the set `{y ∈ Rᵏ | Φ(y)}` is semialgebraic.

Immediate from `formula_realization_isSemialgebraicSetOver` (the realization is
semialgebraic *over `D`*) and `IsSemialgebraicSet.of_definedOver` (sets defined over a
subring are semialgebraic). -/
theorem corollary_2_78 {k : ℕ} (hinj : Function.Injective (algebraMap D R))
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) D)) :
    IsSemialgebraicSet (Φ.realization (C := R)) :=
  IsSemialgebraicSet.of_definedOver (formula_realization_isSemialgebraicSetOver hinj Φ)

end Azurite.BPR
