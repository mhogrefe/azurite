/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_1.Continuity
import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_84
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Exercise_2_17
import Azurite.BasuPollackRoy.Chapter2.Section2_5.PNormIsSemialgebraic

/-! # BPR §3.1 — semialgebraic homeomorphisms

A *semialgebraic homeomorphism* from a semialgebraic set `S` to a semialgebraic set `T` is a
semialgebraic bijection `f : S → T` that is continuous and whose inverse is continuous. We bundle `f`
together with its inverse `g` as data (BPR only requires `f` itself to be semialgebraic; the inverse
need only be continuous).

Besides the definition, we record the basic closure facts — the Cartesian product of semialgebraic
sets is semialgebraic, the identity is a semialgebraic homeomorphism, the inverse of a semialgebraic
bijection is semialgebraic, and semialgebraic homeomorphisms are closed under inverse and composition.
These are exactly the data making semialgebraic sets into a *groupoid* (see
`SemialgebraicGroupoid.lean`). -/

namespace Azurite.BPR

open MvPolynomial

variable {k ℓ m : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR definition (semialgebraic homeomorphism).** A *semialgebraic homeomorphism* from a
semialgebraic set `S ⊆ R^k` to a semialgebraic set `T ⊆ R^ℓ` is a semialgebraic bijection
`f : S → T` that is continuous and whose inverse `g : T → S` is continuous. -/
structure IsSemialgebraicHomeomorphism (S : Set (Fin k → R)) (T : Set (Fin ℓ → R))
    (f : (Fin k → R) → (Fin ℓ → R)) (g : (Fin ℓ → R) → (Fin k → R)) : Prop where
  /-- `f` is a semialgebraic function. -/
  isSemialgebraicFunction : IsSemialgebraicFunction S f
  /-- `f` is a bijection from `S` onto `T`. -/
  bijOn : Set.BijOn f S T
  /-- `f` is continuous on `S`. -/
  continuousOn : ContinuousOn f S
  /-- `g` is the two-sided inverse of `f` on `S` and `T`. -/
  invOn : Set.InvOn g f S T
  /-- the inverse `g` is continuous on `T`. -/
  continuousOn_inv : ContinuousOn g T

/-! ### The Cartesian product of semialgebraic sets -/

/-- The **Cartesian product** of `S ⊆ R^k` and `T ⊆ R^ℓ`, as a subset of `R^{k+ℓ}`: the points
whose first `k` coordinates lie in `S` and whose last `ℓ` coordinates lie in `T`. -/
def setProd (S : Set (Fin k → R)) (T : Set (Fin ℓ → R)) : Set (Fin (k + ℓ) → R) :=
  {z | (z ∘ Fin.castAdd ℓ) ∈ S ∧ (z ∘ Fin.natAdd k) ∈ T}

omit [IsRealClosed R] in
/-- **The Cartesian product of two semialgebraic sets is semialgebraic** (it is the intersection of
the two coordinate-block cylinders). -/
theorem IsSemialgebraicSet.prod {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) :
    IsSemialgebraicSet (setProd S T) :=
  (IsSemialgebraicSet.comap (Fin.castAdd ℓ) hS).inter (IsSemialgebraicSet.comap (Fin.natAdd k) hT)

/-! ### The identity is a semialgebraic function -/

omit [IsRealClosed R] in
/-- **The identity is a semialgebraic function** on any semialgebraic domain: its graph is the
intersection of the domain cylinder with the diagonal `{z | z∘natAdd = z∘castAdd}`. -/
theorem isSemialgebraicFunction_id {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicFunction S (id : (Fin k → R) → (Fin k → R)) := by
  show IsSemialgebraicSet (funGraph S id)
  have hdiag : IsSemialgebraicSet {z : Fin (k + k) → R | z ∘ Fin.natAdd k = z ∘ Fin.castAdd k} := by
    have he : {z : Fin (k + k) → R | z ∘ Fin.natAdd k = z ∘ Fin.castAdd k}
        = ⋂ i ∈ (Finset.univ : Finset (Fin k)),
            {z : Fin (k + k) → R | eval z (X (Fin.natAdd k i) - X (Fin.castAdd k i)) = 0} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_univ, forall_true_left,
        map_sub, eval_X, sub_eq_zero, funext_iff, Function.comp_apply]
    rw [he]
    exact IsSemialgebraicSet.iInter_finset _ (fun i _ => IsSemialgebraicSet.eqZero _)
  have hgraph : funGraph S id
      = {z : Fin (k + k) → R | z ∘ Fin.castAdd k ∈ S} ∩
          {z : Fin (k + k) → R | z ∘ Fin.natAdd k = z ∘ Fin.castAdd k} := by
    ext z; simp only [mem_funGraph, id_eq, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hgraph]
  exact (IsSemialgebraicSet.comap (Fin.castAdd k) hS).inter hdiag

/-! ### The inverse of a semialgebraic bijection is semialgebraic

The graph of the inverse `g` is the block-swap (`blockSwap`) transpose of the graph of `f`. This
graph-transpose relation is the bridge between "`g` is the inverse of `f`" and "`g`'s graph is
semialgebraic"; both directions are recorded, since they are also what makes `Ext` preserve
homeomorphisms (Exercise 3.2). -/

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **The graph of the inverse is the transpose of the graph of `f`.** If `f : S → T` is a
semialgebraic bijection with two-sided inverse `g`, then `funGraph T g` is the `blockSwap`
reindexing of `funGraph S f`. -/
theorem funGraph_inverse_eq {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin k → R)}
    (hbij : Set.BijOn f S T) (hinv : Set.InvOn g f S T) :
    funGraph T g = {v : Fin (ℓ + k) → R | v ∘ blockSwap k ℓ ∈ funGraph S f} := by
  have hsc : blockSwap k ℓ ∘ Fin.castAdd ℓ = Fin.natAdd ℓ := by
    funext a; simp only [Function.comp_apply, blockSwap, Fin.addCases_left]
  have hsn : blockSwap k ℓ ∘ Fin.natAdd k = Fin.castAdd k := by
    funext j; simp only [Function.comp_apply, blockSwap, Fin.addCases_right]
  ext v
  simp only [mem_funGraph, Set.mem_ofPred_eq, Function.comp_assoc, hsc, hsn]
  constructor
  · rintro ⟨hyT, hxg⟩
    obtain ⟨x₀, hx₀S, hfx₀⟩ := hbij.surjOn hyT
    have hgy : g (v ∘ Fin.castAdd k) = x₀ := by rw [← hfx₀]; exact hinv.1 hx₀S
    exact ⟨by rw [hxg, hgy]; exact hx₀S, by rw [hxg, hgy]; exact hfx₀.symm⟩
  · rintro ⟨hxS, hyf⟩
    exact ⟨by rw [hyf]; exact hbij.mapsTo hxS, by rw [hyf]; exact (hinv.1 hxS).symm⟩

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **Converse: a graph-transpose relation forces `g` to be the inverse of `f`.** If `funGraph T g`
is the `blockSwap` transpose of `funGraph S f`, then `g` is a two-sided inverse of `f` on `S, T`. -/
theorem invOn_of_funGraph_transpose {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin k → R)}
    (hgt : funGraph T g = {v : Fin (ℓ + k) → R | v ∘ blockSwap k ℓ ∈ funGraph S f}) :
    Set.InvOn g f S T := by
  have hmem : ∀ (x : Fin k → R) (y : Fin ℓ → R), (y ∈ T ∧ x = g y) ↔ (x ∈ S ∧ y = f x) := by
    intro x y
    have h := congrArg (Fin.append y x ∈ ·) hgt
    simpa only [eq_iff_iff, mem_funGraph, Set.mem_ofPred_eq, blockSwap_append,
      append_comp_castAdd, append_comp_natAdd] using h
  exact ⟨fun x hx => ((hmem x (f x)).mpr ⟨hx, rfl⟩).2.symm,
    fun y hy => ((hmem (g y) y).mp ⟨hy, rfl⟩).2.symm⟩

omit [IsRealClosed R] in
/-- **The inverse of a semialgebraic bijection is a semialgebraic function.** -/
theorem inverse_isSemialgebraicFunction {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin k → R)}
    (hf : IsSemialgebraicFunction S f) (hbij : Set.BijOn f S T) (hinv : Set.InvOn g f S T) :
    IsSemialgebraicFunction T g := by
  show IsSemialgebraicSet (funGraph T g)
  rw [funGraph_inverse_eq hbij hinv]
  exact IsSemialgebraicSet.comap (blockSwap k ℓ) hf

/-! ### Semialgebraic homeomorphisms form a groupoid -/

/-- **The identity is a semialgebraic homeomorphism.** -/
theorem IsSemialgebraicHomeomorphism.refl {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicHomeomorphism S S id id where
  isSemialgebraicFunction := isSemialgebraicFunction_id hS
  bijOn := Set.bijOn_id S
  continuousOn := continuousOn_id
  invOn := Set.invOn_id S
  continuousOn_inv := continuousOn_id

/-- **The inverse of a semialgebraic homeomorphism is a semialgebraic homeomorphism.** -/
theorem IsSemialgebraicHomeomorphism.symm {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin k → R)}
    (h : IsSemialgebraicHomeomorphism S T f g) :
    IsSemialgebraicHomeomorphism T S g f where
  isSemialgebraicFunction := inverse_isSemialgebraicFunction h.isSemialgebraicFunction h.bijOn h.invOn
  bijOn := Set.BijOn.symm h.invOn.symm h.bijOn
  continuousOn := h.continuousOn_inv
  invOn := h.invOn.symm
  continuousOn_inv := h.continuousOn

/-- **The composition of two semialgebraic homeomorphisms is a semialgebraic homeomorphism.** -/
theorem IsSemialgebraicHomeomorphism.trans {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {U : Set (Fin m → R)} {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin k → R)}
    {f' : (Fin ℓ → R) → (Fin m → R)} {g' : (Fin m → R) → (Fin ℓ → R)}
    (h₁ : IsSemialgebraicHomeomorphism S T f g) (h₂ : IsSemialgebraicHomeomorphism T U f' g') :
    IsSemialgebraicHomeomorphism S U (f' ∘ f) (g ∘ g') where
  isSemialgebraicFunction :=
    proposition_2_84 h₁.isSemialgebraicFunction h₂.isSemialgebraicFunction h₁.bijOn.mapsTo
  bijOn := h₂.bijOn.comp h₁.bijOn
  continuousOn := h₂.continuousOn.comp h₁.continuousOn h₁.bijOn.mapsTo
  invOn := h₁.invOn.comp h₂.invOn h₁.bijOn.mapsTo
    (Set.BijOn.symm h₂.invOn.symm h₂.bijOn).mapsTo
  continuousOn_inv := h₁.continuousOn_inv.comp h₂.continuousOn_inv
    (Set.BijOn.symm h₂.invOn.symm h₂.bijOn).mapsTo

end Azurite.BPR
