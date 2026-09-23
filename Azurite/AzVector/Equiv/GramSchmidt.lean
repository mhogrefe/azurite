/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzVector.GramSchmidt
import Azurite.AzVector.Equiv.Dot
import Azurite.AzVector.Equiv.Sub
import Azurite.AzVector.Equiv.SMul
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Correctness of `AzVector.gramSchmidt`

The computational Gram–Schmidt of §`AzVector.GramSchmidt` produces, from any input
list, a list of the same length whose vectors are pairwise orthogonal. Orthogonality
holds *unconditionally*: a linearly dependent input merely yields a zero vector, and
the dot product with a zero vector vanishes (the ordered field gives `w · w = 0 ↔
w = 0`, so the projection coefficients are well-behaved).

This is the computational counterpart of BPR Proposition 4.41
(`Azurite.BPR.Chapter4.proposition_4_41`): the abstract existence statement there
and this concrete algorithm agree under `AzVector.toFn`
(`AzVector.dot_eq_dotProduct`).
-/

namespace Azurite

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {n : Nat}

/-- One Gram–Schmidt step: the projection of `v` orthogonal to the accumulated
family `acc`. -/
private def gsProj (acc : List (AzVector R n)) (v : AzVector R n) : AzVector R n :=
  acc.foldl (fun u w => u - ((v.dot w / w.normSq : R) • w)) v

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The Gram–Schmidt fold step appends exactly one vector. -/
private theorem gramSchmidt_eq_foldl (vs : List (AzVector R n)) :
    AzVector.gramSchmidt vs =
      vs.foldl (fun acc v => acc ++ [gsProj acc v]) [] := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `gsProj` written as `v` minus the sum of the projections onto each `w ∈ acc`. -/
private theorem gsProj_eq (acc : List (AzVector R n)) (v : AzVector R n) :
    gsProj acc v = v - (acc.map (fun w => (v.dot w / w.normSq : R) • w)).sum := by
  unfold gsProj
  -- general fact about foldl of a subtraction
  suffices h : ∀ (l : List (AzVector R n)) (init : AzVector R n),
      l.foldl (fun u w => u - ((v.dot w / w.normSq : R) • w)) init =
        init - (l.map (fun w => (v.dot w / w.normSq : R) • w)).sum by
    simpa using h acc v
  intro l
  induction l with
  | nil => intro init; simp
  | cons a t ih =>
    intro init
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    abel

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `AzVector.dot` is symmetric. -/
private theorem dot_comm (v w : AzVector R n) : v.dot w = w.dot v := by
  rw [AzVector.dot_eq_dotProduct, AzVector.dot_eq_dotProduct, dotProduct_comm]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The fold's `toFn` of a list sum distributes over the list. -/
private theorem toFn_list_sum (l : List (AzVector R n)) :
    (l.sum).toFn = (l.map AzVector.toFn).sum := by
  have := map_list_sum (AzVector.toFnLM (R := R) (n := n)) l
  simpa [AzVector.toFnLM] using this

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Core computation: for `w` nonzero and `acc` pairwise orthogonal with `w ∈ acc`,
the sum of the projection terms (paired against `w`) collapses to `w ⬝ᵥ v`. -/
private theorem gsProj_sum_collapse (v w : AzVector R n)
    (hnorm : w.toFn ⬝ᵥ w.toFn ≠ 0) :
    ∀ (acc : List (AzVector R n)), acc.Pairwise (fun a b => a.dot b = 0) → w ∈ acc →
      (acc.map (fun w' => w.toFn ⬝ᵥ ((v.dot w' / w'.normSq : R) • w').toFn)).sum
        = w.toFn ⬝ᵥ v.toFn := by
  intro acc
  induction acc with
  | nil => intro _ hw; exact absurd hw (List.not_mem_nil)
  | cons a t ih =>
    intro hpair hw
    rw [List.pairwise_cons] at hpair
    obtain ⟨hhead, htail⟩ := hpair
    rw [List.map_cons, List.sum_cons]
    -- value of the head term
    have head_val : ∀ x : AzVector R n,
        w.toFn ⬝ᵥ ((v.dot x / x.normSq : R) • x).toFn
          = (v.dot x / x.normSq : R) * (w.toFn ⬝ᵥ x.toFn) := by
      intro x
      rw [AzVector.toFn_smul, dotProduct_smul, smul_eq_mul]
    by_cases ha : a = w
    · -- head is w: contributes w ⬝ᵥ v; tail all zero
      subst ha
      rw [head_val a, AzVector.normSq_eq_dotProduct, AzVector.dot_eq_dotProduct,
          div_mul_cancel₀ _ hnorm, dotProduct_comm a.toFn v.toFn]
      -- tail sum is zero: every w' ∈ t satisfies a ⬝ᵥ w' = 0
      have htzero : (t.map (fun w' => a.toFn ⬝ᵥ ((v.dot w' / w'.normSq : R) • w').toFn)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨w', hw'mem, rfl⟩ := hx
        rw [head_val w', AzVector.dot_eq_dotProduct] at *
        have : a.toFn ⬝ᵥ w'.toFn = 0 := by
          have := hhead w' hw'mem
          rwa [AzVector.dot_eq_dotProduct] at this
        rw [this, mul_zero]
      rw [htzero, add_zero]
    · -- head a ≠ w, so w ∈ t; head term is zero
      have hwt : w ∈ t := by
        cases hw with
        | head => exact absurd rfl ha
        | tail _ h => exact h
      have hazero : w.toFn ⬝ᵥ ((v.dot a / a.normSq : R) • a).toFn = 0 := by
        rw [head_val a]
        have : w.toFn ⬝ᵥ a.toFn = 0 := by
          -- a precedes w in (a :: t); by pairwise a.dot w = 0, symmetric to w.dot a
          have hd : a.dot w = 0 := hhead w hwt
          rw [dot_comm, AzVector.dot_eq_dotProduct] at hd
          exact hd
        rw [this, mul_zero]
      rw [hazero, zero_add]
      exact ih htail hwt

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `dotProduct` distributes over a list sum in the second argument. -/
private theorem dotProduct_list_sum (u : Fin n → R) (l : List (Fin n → R)) :
    u ⬝ᵥ l.sum = (l.map (fun x => u ⬝ᵥ x)).sum := by
  induction l with
  | nil => simp [dotProduct_zero]
  | cons a t ih => rw [List.sum_cons, dotProduct_add, ih, List.map_cons, List.sum_cons]

/-- If `acc` is pairwise orthogonal, then `gsProj acc v` is orthogonal to every
`w ∈ acc`. -/
private theorem gsProj_orthogonal (acc : List (AzVector R n)) (v : AzVector R n)
    (hacc : acc.Pairwise (fun a b => a.dot b = 0)) :
    ∀ w ∈ acc, (gsProj acc v).dot w = 0 := by
  intro w hw
  rw [gsProj_eq, dot_comm, AzVector.dot_eq_dotProduct,
      AzVector.toFn_sub, dotProduct_sub, toFn_list_sum, List.map_map,
      dotProduct_list_sum, List.map_map]
  simp only [Function.comp_def]
  -- now: w.toFn ⬝ᵥ v.toFn - ∑ (terms) = 0
  by_cases hw0 : w = 0
  · subst hw0
    simp [AzVector.toFn_zero]
  · have hwne : w.toFn ≠ 0 := by
      intro hc; exact hw0 (AzVector.toFn_injective (by simpa [AzVector.toFn_zero] using hc))
    have hnorm : w.toFn ⬝ᵥ w.toFn ≠ 0 := by
      rw [Ne, dotProduct_self_eq_zero]; exact hwne
    rw [gsProj_sum_collapse v w hnorm acc hacc hw, sub_self]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Gram–Schmidt preserves the number of vectors. -/
theorem AzVector.gramSchmidt_length (vs : List (AzVector R n)) :
    (AzVector.gramSchmidt vs).length = vs.length := by
  rw [gramSchmidt_eq_foldl]
  suffices h : ∀ (l : List (AzVector R n)) (acc : List (AzVector R n)),
      (l.foldl (fun acc v => acc ++ [gsProj acc v]) acc).length = acc.length + l.length by
    simpa using h vs []
  intro l
  induction l with
  | nil => intro acc; simp
  | cons a t ih =>
    intro acc
    rw [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil,
        List.length_cons]
    omega

/-- The accumulator stays pairwise orthogonal across the fold. -/
private theorem gramSchmidt_foldl_pairwise (vs : List (AzVector R n)) :
    ∀ (acc : List (AzVector R n)), acc.Pairwise (fun u w => u.dot w = 0) →
      (vs.foldl (fun acc v => acc ++ [gsProj acc v]) acc).Pairwise
        (fun u w => u.dot w = 0) := by
  induction vs with
  | nil => intro acc hacc; simpa using hacc
  | cons v vs' ih =>
    intro acc hacc
    rw [List.foldl_cons]
    apply ih
    -- acc ++ [gsProj acc v] is pairwise
    rw [List.pairwise_append]
    refine ⟨hacc, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    -- need a.dot (gsProj acc v) = 0, from gsProj_orthogonal (symmetric)
    have := gsProj_orthogonal acc v hacc a ha
    rw [dot_comm]; exact this

/-- **Correctness of Gram–Schmidt: the output is pairwise orthogonal.** -/
theorem AzVector.gramSchmidt_pairwise_orthogonal (vs : List (AzVector R n)) :
    (AzVector.gramSchmidt vs).Pairwise (fun u w => u.dot w = 0) := by
  rw [gramSchmidt_eq_foldl]
  exact gramSchmidt_foldl_pairwise vs [] List.Pairwise.nil

end Azurite
