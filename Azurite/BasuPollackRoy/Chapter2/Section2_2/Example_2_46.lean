/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.Corollary_2_49

/-!
# BPR Example 2.46

For a degree-2 polynomial `P`:

* If `P` has two distinct real roots `r₁ ≠ r₂`, then both have virtual
  multiplicity `1`.
* If `P` has no two distinct real roots, then there exists a root `r` of
  `P'` with virtual multiplicity `2`.

These follow from Corollary 2.49 (the lower-bound `rootMultiplicity ≤
virtualMultiplicity` plus the parity constraint) together with the
length-equals-degree property of `virtualRoots`.
-/

namespace Azurite.BPR.Lemma_2_48

open Polynomial Azurite.BPR Azurite.BPR.VirtualRoots

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Helper: in any list, the sum of counts of two distinct elements is at most
    the length of the list. -/
private lemma count_add_count_le_length {α : Type*} [DecidableEq α] {l : List α}
    {a b : α} (hne : a ≠ b) :
    l.count a + l.count b ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, List.length_cons]
    by_cases hxa : x = a
    · subst hxa
      have h2 : (x == b) = false := beq_eq_false_iff_ne.mpr hne
      simp [h2]; omega
    · have h1 : (x == a) = false := beq_eq_false_iff_ne.mpr hxa
      by_cases hxb : x = b
      · subst hxb
        simp [h1]; omega
      · have h2 : (x == b) = false := beq_eq_false_iff_ne.mpr hxb
        simp [h1, h2]; omega

/-- **BPR Example 2.46 (distinct roots case).** If `P` has degree 2 and two
    distinct real roots `r₁ ≠ r₂`, both have virtual multiplicity 1. -/
theorem example_2_46_distinct_roots
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hn : P.natDegree = 2)
    {r₁ r₂ : R} (h₁ : P.eval r₁ = 0) (h₂ : P.eval r₂ = 0) (hne : r₁ ≠ r₂) :
    virtualMultiplicity hIVP hP r₁ = 1 ∧ virtualMultiplicity hIVP hP r₂ = 1 := by
  have hlen : (virtualRoots hIVP hP).length = 2 := by
    rw [length_virtualRoots, hn]
  have hμ₁ : 1 ≤ P.rootMultiplicity r₁ :=
    (Polynomial.rootMultiplicity_pos hP).mpr h₁
  have hμ₂ : 1 ≤ P.rootMultiplicity r₂ :=
    (Polynomial.rootMultiplicity_pos hP).mpr h₂
  have hge₁ := (corollary_2_49 hIVP hP r₁).1
  have hge₂ := (corollary_2_49 hIVP hP r₂).1
  have hsum : (virtualRoots hIVP hP).count r₁ + (virtualRoots hIVP hP).count r₂
              ≤ (virtualRoots hIVP hP).length :=
    count_add_count_le_length hne
  rw [hlen] at hsum
  unfold virtualMultiplicity at hge₁ hge₂ ⊢
  exact ⟨by omega, by omega⟩

/-- **BPR Example 2.46 (no distinct roots case).** If `P` has degree 2 and no
    two distinct real roots, then there exists a root `r` of `P'` with virtual
    multiplicity 2. -/
theorem example_2_46_no_distinct_roots
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hn : P.natDegree = 2)
    (hno : ∀ r₁ r₂ : R, P.eval r₁ = 0 → P.eval r₂ = 0 → r₁ = r₂) :
    ∃ r : R, (derivative P).eval r = 0 ∧ virtualMultiplicity hIVP hP r = 2 := by
  have hlen : (virtualRoots hIVP hP).length = 2 := by
    rw [length_virtualRoots, hn]
  have hdP : derivative P ≠ 0 := by
    intro h
    have := Polynomial.derivative_eq_zero.mp h
    rw [hn] at this; omega
  have hlenP' : (virtualRoots hIVP hdP).length = 1 := by
    rw [length_virtualRoots]
    have h := Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_derivative (p := P) (by rw [hn]; omega))
    rw [hn] at h; omega
  -- Helper: any element x of virtualRoots P with virtualMultiplicity 1 is a root of P.
  have hroot_of_one :
      ∀ x ∈ virtualRoots hIVP hP, virtualMultiplicity hIVP hP x = 1 →
        P.eval x = 0 := by
    intro x _ hvx
    obtain ⟨hμ_le, heven⟩ := corollary_2_49 hIVP hP x
    rw [hvx] at hμ_le heven
    -- rootMultiplicity ≤ 1 and Even (1 - rootMultiplicity), so rootMultiplicity = 1.
    have hμ : P.rootMultiplicity x = 1 := by
      interval_cases P.rootMultiplicity x
      · exact absurd heven (by decide)
      · rfl
    exact (Polynomial.rootMultiplicity_pos hP).mp (by rw [hμ]; omega)
  -- virtualRoots P has length 2: get explicit form.
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  -- Show a = b: otherwise both are distinct roots of P, contradicting hno.
  have hab_eq : a = b := by
    by_contra hne
    have ha_mem : a ∈ virtualRoots hIVP hP := by rw [hab]; exact List.mem_cons_self
    have hb_mem : b ∈ virtualRoots hIVP hP := by
      rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have hva : virtualMultiplicity hIVP hP a = 1 := by
      unfold virtualMultiplicity
      rw [hab, List.count_cons, List.count_cons, List.count_nil]
      simp [Ne.symm hne]
    have hvb : virtualMultiplicity hIVP hP b = 1 := by
      unfold virtualMultiplicity
      rw [hab, List.count_cons, List.count_cons, List.count_nil]
      simp [hne]
    have hPa := hroot_of_one a ha_mem hva
    have hPb := hroot_of_one b hb_mem hvb
    exact hne (hno a b hPa hPb)
  -- So virtualRoots P = [a, a]; r := a has virtualMultiplicity 2.
  refine ⟨a, ?_, ?_⟩
  · -- Show P'.eval a = 0.
    -- count of a in virtualRoots P' is in {v(P,a) - 1, v(P,a), v(P,a) + 1} = {1, 2, 3},
    -- but ≤ length virtualRoots P' = 1, so count = 1.
    have hva : virtualMultiplicity hIVP hP a = 2 := by
      unfold virtualMultiplicity
      rw [hab, ← hab_eq]
      simp
    have hcases := virtualMultiplicity_derivative_cases hIVP hP hdP a
    have hcle : (virtualRoots hIVP hdP).count a ≤ 1 := by
      rw [← hlenP']; exact List.count_le_length
    have hc1 : (virtualRoots hIVP hdP).count a = 1 := by
      rw [hva] at hcases; omega
    -- corollary_2_49 for P' at a: rootMultiplicity ≤ 1 and Even (1 - rootMultiplicity),
    -- so rootMultiplicity = 1, hence P'.eval a = 0.
    obtain ⟨hμ'_le, heven'⟩ := corollary_2_49 hIVP hdP a
    have hvP'a : virtualMultiplicity hIVP hdP a = 1 := hc1
    rw [hvP'a] at hμ'_le heven'
    have hμ' : (derivative P).rootMultiplicity a = 1 := by
      interval_cases (derivative P).rootMultiplicity a
      · exact absurd heven' (by decide)
      · rfl
    exact (Polynomial.rootMultiplicity_pos hdP).mp (by rw [hμ']; omega)
  · unfold virtualMultiplicity
    rw [hab, ← hab_eq]
    simp

end Azurite.BPR.Lemma_2_48
