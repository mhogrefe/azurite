/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_13
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_87
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_84
import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunctionTuple

/-! # BPR §3.3 — Proposition 3.16: representatives and the extension `Ext(S, R⟨ε⟩)`

For a semialgebraic set `S ⊆ Rᵏ` and a tuple of germs `ϕ ∈ (R⟨ε⟩)ᵏ` with representatives
`f = (f₁, …, f_k)` on `(0, t)`, the point `ϕ` lies in `Ext(S, R⟨ε⟩)` exactly when the trajectory
`f(t')` eventually lies in `S` as `t' → 0⁺`. The engine is the **germ-evaluation bridge**: a
polynomial `P ∈ R[X₁, …, X_k]` evaluated at the germ tuple `ϕ` equals the germ of the pointwise
evaluation `u ↦ P(f₁(u), …, f_k(u))` (`aeval_germHom_tuple`), so the sign of `P(ϕ)` in the germ
field matches the eventual sign of `P(f(t'))` near `0⁺`. -/

namespace Azurite.BPR

open MvPolynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The constant embedding `R → semialgContSubring t` (`a ↦ the constant function `a`). -/
noncomputable def constSub (t : R) : R →+* semialgContSubring t :=
  (algebraMap R ((Fin 1 → R) → R)).codRestrict (semialgContSubring t)
    (fun a => mem_semialgContSubring.mpr (isSemialgContinuousOn_const a))

/-- The underlying function of `eval₂Hom (constSub t) c P` is the pointwise evaluation
`u ↦ P(c₁(u), …, c_k(u))`. -/
theorem eval₂Hom_constSub_val (t : R) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) (u : Fin 1 → R) :
    ((MvPolynomial.eval₂Hom (constSub t) c P : semialgContSubring t) : (Fin 1 → R) → R) u
      = MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) u) P := by
  have h1 : ((Pi.evalRingHom (fun _ : Fin 1 → R => R) u).comp
      (semialgContSubring t).subtype).comp (constSub t) = RingHom.id R := by ext a; rfl
  have h2 : (fun i => ((Pi.evalRingHom (fun _ : Fin 1 → R => R) u).comp
      (semialgContSubring t).subtype) (c i)) = (fun i => (c i : (Fin 1 → R) → R) u) := rfl
  show ((Pi.evalRingHom (fun _ : Fin 1 → R => R) u).comp (semialgContSubring t).subtype)
    (MvPolynomial.eval₂Hom (constSub t) c P) = _
  rw [MvPolynomial.map_eval₂Hom, h1, h2]
  rfl

/-- **The germ-evaluation bridge.** Evaluating `P` at the germ tuple `(⟦c₁⟧, …, ⟦c_k⟧)` equals the
germ of the pointwise evaluation `u ↦ P(c₁(u), …, c_k(u))`. -/
theorem aeval_germHom_tuple (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) :
    MvPolynomial.aeval (fun i => germHom t ht (c i)) P
      = germHom t ht (MvPolynomial.eval₂Hom (constSub t) c P) := by
  have hbridge : (MvPolynomial.aeval (fun i => germHom t ht (c i))).toRingHom
      = (germHom t ht).comp (MvPolynomial.eval₂Hom (constSub t) c) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show MvPolynomial.aeval _ (MvPolynomial.C a)
        = germHom t ht (MvPolynomial.eval₂Hom (constSub t) c (MvPolynomial.C a))
      rw [MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C, germHom_apply]
      show constGermHom a = _
      rw [constGermHom, RingHom.comp_apply, germHom_apply]
      exact Quotient.sound ⟨t, ht, fun _ _ _ => rfl⟩
    · intro i
      show MvPolynomial.aeval _ (MvPolynomial.X i)
        = germHom t ht (MvPolynomial.eval₂Hom (constSub t) c (MvPolynomial.X i))
      rw [MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
  exact DFunLike.congr_fun hbridge P

/-- The representative `u ↦ P(c₁(u), …, c_k(u))` of the germ `P(ϕ)`. -/
noncomputable def evalGermRep (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) : SemialgGermRep R :=
  ⟨t, ht, (MvPolynomial.eval₂Hom (constSub t) c P : semialgContSubring t),
    mem_semialgContSubring.mp (MvPolynomial.eval₂Hom (constSub t) c P).2⟩

theorem evalGermRep_toFun_apply (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) (s : R) :
    (evalGermRep t ht c P).toFun (constPt s)
      = MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P :=
  eval₂Hom_constSub_val t c P (constPt s)

theorem aeval_eq_evalGermRep (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) :
    MvPolynomial.aeval (fun i => germHom t ht (c i)) P = (evalGermRep t ht c P).germ := by
  rw [aeval_germHom_tuple, germHom_apply]; rfl

/-! ### Eventual behaviour near `0⁺` -/

/-- `Q` holds **eventually as `s → 0⁺`**: on some interval `(0, t)`. -/
def EvNhd (Q : R → Prop) : Prop := ∃ t : R, 0 < t ∧ ∀ s : R, 0 < s → s < t → Q s

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem EvNhd.and {A B : R → Prop} (hA : EvNhd A) (hB : EvNhd B) :
    EvNhd (fun s => A s ∧ B s) := by
  obtain ⟨tA, htA, HA⟩ := hA
  obtain ⟨tB, htB, HB⟩ := hB
  exact ⟨min tA tB, lt_min htA htB, fun s hs hst =>
    ⟨HA s hs (lt_of_lt_of_le hst (min_le_left _ _)), HB s hs (lt_of_lt_of_le hst (min_le_right _ _))⟩⟩

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem EvNhd.mono {A B : R → Prop} (h : ∀ s, A s → B s) (hA : EvNhd A) : EvNhd B := by
  obtain ⟨t, ht, H⟩ := hA
  exact ⟨t, ht, fun s hs hst => h s (H s hs hst)⟩

omit [IsRealClosed R] in
/-- An eventually-holding predicate holds at some positive point. -/
theorem EvNhd.exists_pos {A : R → Prop} (hA : EvNhd A) : ∃ s : R, 0 < s ∧ A s := by
  obtain ⟨t, ht, H⟩ := hA
  exact ⟨t / 2, by positivity, H _ (by positivity) (by linarith)⟩

omit [IsRealClosed R] in
theorem not_evNhd_false : ¬ EvNhd (fun _ : R => False) := fun h => (h.exists_pos).elim fun _ h => h.2

variable (R) in
omit [IsRealClosed R] in
/-- Two contradictory predicates cannot both hold eventually. -/
theorem EvNhd.not_and_of_disjoint {A B : R → Prop} (hA : EvNhd A) (hB : EvNhd B)
    (hAB : ∀ s, ¬ (A s ∧ B s)) : False :=
  not_evNhd_false (R := R) ((hA.and hB).mono (fun s h => hAB s h))

/-- **Base sign bridge (zero).** `P(ϕ) = 0` in the germ field iff `P(f(t'))` is eventually `0`. -/
theorem aeval_eq_zero_iff (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) :
    MvPolynomial.aeval (fun i => germHom t ht (c i)) P = 0
      ↔ EvNhd (fun s => MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P = 0) := by
  rw [aeval_eq_evalGermRep, SemialgGermRep.germ,
    show (0 : SemialgGerm R) = Quotient.mk _ SemialgGermRep.zero from rfl, Quotient.eq]
  constructor
  · rintro ⟨t', ht', H⟩
    refine ⟨t', ht', fun s hs hst => ?_⟩
    have := H s hs hst
    rwa [evalGermRep_toFun_apply, SemialgGermRep.zero_toFun, Pi.zero_apply] at this
  · rintro ⟨t', ht', H⟩
    refine ⟨t', ht', fun s hs hst => ?_⟩
    rw [evalGermRep_toFun_apply, SemialgGermRep.zero_toFun, Pi.zero_apply]
    exact H s hs hst

/-- **Base sign bridge (positive).** `P(ϕ) > 0` iff `P(f(t'))` is eventually `> 0`. -/
theorem aeval_pos_iff (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) :
    0 < MvPolynomial.aeval (fun i => germHom t ht (c i)) P
      ↔ EvNhd (fun s => 0 < MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P) := by
  rw [aeval_eq_evalGermRep, SemialgGermRep.germ, SemialgGerm.lt_zero_iff, isPosGerm_mk]
  constructor
  · rintro ⟨t', ht', H⟩
    refine ⟨t', ht', fun s hs hst => ?_⟩
    show 0 < MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P
    rw [← evalGermRep_toFun_apply]; exact H s hs hst
  · rintro ⟨t', ht', H⟩
    refine ⟨t', ht', fun s hs hst => ?_⟩
    rw [evalGermRep_toFun_apply]; exact H s hs hst

/-- **Base sign bridge (negative).** `P(ϕ) < 0` iff `P(f(t'))` is eventually `< 0`. -/
theorem aeval_neg_iff (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) :
    MvPolynomial.aeval (fun i => germHom t ht (c i)) P < 0
      ↔ EvNhd (fun s => MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P < 0) := by
  rw [← neg_pos, aeval_eq_evalGermRep, SemialgGermRep.germ, germ_mk_neg, SemialgGerm.lt_zero_iff,
    isPosGerm_mk]
  constructor
  · rintro ⟨t', ht', H⟩
    refine ⟨t', ht', fun s hs hst => ?_⟩
    have := H s hs hst
    rw [SemialgGermRep.neg_toFun, Pi.neg_apply, evalGermRep_toFun_apply] at this
    linarith
  · rintro ⟨t', ht', H⟩
    refine ⟨t', ht', fun s hs hst => ?_⟩
    rw [SemialgGermRep.neg_toFun, Pi.neg_apply, evalGermRep_toFun_apply]
    have := H s hs hst; linarith

/-- **Eventual sign trichotomy.** Near `0⁺`, `P(f(t'))` is eventually `> 0`, eventually `= 0`, or
eventually `< 0`. -/
theorem evNhd_trichotomy (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) :
    EvNhd (fun s => 0 < MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P) ∨
    EvNhd (fun s => MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P = 0) ∨
    EvNhd (fun s => MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P < 0) := by
  rcases (evalGermRep t ht c P).trichotomy with h | h | h
  · left
    obtain ⟨t', ht', H⟩ := h
    refine ⟨t', ht', fun s hs hst => ?_⟩
    show 0 < MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P
    rw [← evalGermRep_toFun_apply]; exact H s hs hst
  · right; left
    obtain ⟨t', ht', H⟩ := h
    refine ⟨t', ht', fun s hs hst => ?_⟩
    have := H s hs hst
    rwa [SemialgGermRep.zero_toFun, Pi.zero_apply, evalGermRep_toFun_apply] at this
  · right; right
    obtain ⟨t', ht', H⟩ := h
    refine ⟨t', ht', fun s hs hst => ?_⟩
    show MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P < 0
    have := H s hs hst
    rw [SemialgGermRep.neg_toFun, Pi.neg_apply, evalGermRep_toFun_apply] at this
    linarith

/-- **Base sign bridge (`≠`).** -/
theorem aeval_ne_iff (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) :
    MvPolynomial.aeval (fun i => germHom t ht (c i)) P ≠ 0
      ↔ EvNhd (fun s => MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P ≠ 0) := by
  constructor
  · intro hg
    rcases lt_or_gt_of_ne hg with h | h
    · exact ((aeval_neg_iff t ht c P).mp h).mono (fun s hs => ne_of_lt hs)
    · exact ((aeval_pos_iff t ht c P).mp h).mono (fun s hs => (ne_of_lt hs).symm)
  · intro hev hg0
    exact EvNhd.not_and_of_disjoint R hev ((aeval_eq_zero_iff t ht c P).mp hg0) (fun s h => h.1 h.2)

/-- **Base sign bridge (`≤`).** -/
theorem aeval_nonpos_iff (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) :
    MvPolynomial.aeval (fun i => germHom t ht (c i)) P ≤ 0
      ↔ EvNhd (fun s => MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P ≤ 0) := by
  constructor
  · intro hg
    rcases evNhd_trichotomy t ht c P with h | h | h
    · exact absurd ((aeval_pos_iff t ht c P).mpr h) (not_lt.mpr hg)
    · exact h.mono (fun s he => le_of_eq he)
    · exact h.mono (fun s hl => le_of_lt hl)
  · intro hev
    by_contra hg
    rw [not_le] at hg
    exact EvNhd.not_and_of_disjoint R hev ((aeval_pos_iff t ht c P).mp hg)
      (fun s h => absurd h.1 (not_le.mpr h.2))

/-- **Base sign bridge (`≥`).** -/
theorem aeval_nonneg_iff (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (P : MvPolynomial (Fin k) R) :
    0 ≤ MvPolynomial.aeval (fun i => germHom t ht (c i)) P
      ↔ EvNhd (fun s => 0 ≤ MvPolynomial.eval (fun i => (c i : (Fin 1 → R) → R) (constPt s)) P) := by
  constructor
  · intro hg
    rcases evNhd_trichotomy t ht c P with h | h | h
    · exact h.mono (fun s hl => le_of_lt hl)
    · exact h.mono (fun s he => le_of_eq he.symm)
    · exact absurd ((aeval_neg_iff t ht c P).mpr h) (not_lt.mpr hg)
  · intro hev
    by_contra hg
    rw [not_le] at hg
    exact EvNhd.not_and_of_disjoint R hev ((aeval_neg_iff t ht c P).mp hg)
      (fun s h => absurd h.1 (not_le.mpr h.2))

/-! ### The realization bridge -/

open Formula

/-- **Forward implications of the realization bridge.** For a quantifier-free formula `Φ`, if the
germ tuple `ϕ` satisfies `Φ` (resp. fails `Φ`) over the germ field, then the trajectory `f(t')`
eventually satisfies (resp. fails) `Φ` over `R`. -/
theorem forward_bridge (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) :
    Φ.IsQuantifierFree →
      ((fun i => germHom t ht (c i)) ∈ Φ.realization (C := SemialgGerm R) →
        EvNhd (fun s => (fun i => (c i : (Fin 1 → R) → R) (constPt s)) ∈ Φ.realization (C := R)))
      ∧ ((fun i => germHom t ht (c i)) ∉ Φ.realization (C := SemialgGerm R) →
        EvNhd (fun s => (fun i => (c i : (Fin 1 → R) → R) (constPt s)) ∉ Φ.realization (C := R))) := by
  induction Φ with
  | atom a =>
    intro _
    obtain ⟨P, rel⟩ := a
    cases rel <;>
    refine ⟨fun h => ?_, fun h => ?_⟩
    -- the 12 atom cases: each is a base sign bridge, on `interpret` (defeq to `aeval _ P rel 0`)
    · exact (aeval_eq_zero_iff t ht c P).mp h
    · exact (aeval_ne_iff t ht c P).mp h
    · exact (aeval_ne_iff t ht c P).mp h
    · exact ((aeval_eq_zero_iff t ht c P).mp (not_not.mp h)).mono fun s hs => not_not.mpr hs
    · exact (aeval_neg_iff t ht c P).mp h
    · exact ((aeval_nonneg_iff t ht c P).mp (not_lt.mp h)).mono fun s hs => not_lt.mpr hs
    · exact (aeval_pos_iff t ht c P).mp h
    · exact ((aeval_nonpos_iff t ht c P).mp (not_lt.mp h)).mono fun s hs => not_lt.mpr hs
    · exact (aeval_nonpos_iff t ht c P).mp h
    · exact ((aeval_pos_iff t ht c P).mp (not_le.mp h)).mono fun s hs => not_le.mpr hs
    · exact (aeval_nonneg_iff t ht c P).mp h
    · exact ((aeval_neg_iff t ht c P).mp (not_le.mp h)).mono fun s hs => not_le.mpr hs
  | not Φ ih =>
    intro hqf
    obtain ⟨f1, f2⟩ := ih hqf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [realization_not, Set.mem_compl_iff] at h
      exact (f2 h).mono fun s hs => by rw [realization_not, Set.mem_compl_iff]; exact hs
    · rw [realization_not, Set.mem_compl_iff, not_not] at h
      exact (f1 h).mono fun s hs => by rw [realization_not, Set.mem_compl_iff, not_not]; exact hs
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    intro hqf
    obtain ⟨g1, g2⟩ := ih₁ hqf.1
    obtain ⟨h1, h2⟩ := ih₂ hqf.2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [realization_and, Set.mem_inter_iff] at h
      exact ((g1 h.1).and (h1 h.2)).mono fun s hs => by
        rw [realization_and, Set.mem_inter_iff]; exact hs
    · rw [realization_and, Set.mem_inter_iff, not_and_or] at h
      rcases h with h | h
      · exact (g2 h).mono fun s hs => by rw [realization_and, Set.mem_inter_iff, not_and_or]; exact Or.inl hs
      · exact (h2 h).mono fun s hs => by rw [realization_and, Set.mem_inter_iff, not_and_or]; exact Or.inr hs
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    intro hqf
    obtain ⟨g1, g2⟩ := ih₁ hqf.1
    obtain ⟨h1, h2⟩ := ih₂ hqf.2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [realization_or, Set.mem_union] at h
      rcases h with h | h
      · exact (g1 h).mono fun s hs => by rw [realization_or, Set.mem_union]; exact Or.inl hs
      · exact (h1 h).mono fun s hs => by rw [realization_or, Set.mem_union]; exact Or.inr hs
    · rw [realization_or, Set.mem_union, not_or] at h
      exact ((g2 h.1).and (h2 h.2)).mono fun s hs => by
        rw [realization_or, Set.mem_union, not_or]; exact hs
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    intro hqf
    obtain ⟨g1, g2⟩ := ih₁ hqf.1
    obtain ⟨h1, h2⟩ := ih₂ hqf.2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [show (Φ₁.implies Φ₂).realization (C := SemialgGerm R)
          = (Φ₁.realization)ᶜ ∪ Φ₂.realization from rfl, Set.mem_union, Set.mem_compl_iff] at h
      rcases h with h | h
      · exact (g2 h).mono fun s hs => by
          rw [show (Φ₁.implies Φ₂).realization (C := R) = (Φ₁.realization)ᶜ ∪ Φ₂.realization from rfl,
            Set.mem_union, Set.mem_compl_iff]; exact Or.inl hs
      · exact (h1 h).mono fun s hs => by
          rw [show (Φ₁.implies Φ₂).realization (C := R) = (Φ₁.realization)ᶜ ∪ Φ₂.realization from rfl,
            Set.mem_union, Set.mem_compl_iff]; exact Or.inr hs
    · rw [show (Φ₁.implies Φ₂).realization (C := SemialgGerm R)
          = (Φ₁.realization)ᶜ ∪ Φ₂.realization from rfl, Set.mem_union, Set.mem_compl_iff,
        not_or, not_not] at h
      exact ((g1 h.1).and (h2 h.2)).mono fun s hs => by
        rw [show (Φ₁.implies Φ₂).realization (C := R) = (Φ₁.realization)ᶜ ∪ Φ₂.realization from rfl,
          Set.mem_union, Set.mem_compl_iff, not_or, not_not]; exact hs
  | exists_ x Φ ih => intro hqf; exact hqf.elim
  | forall_ x Φ ih => intro hqf; exact hqf.elim

/-- **The realization bridge.** For a quantifier-free formula `Φ`, the germ tuple `ϕ` satisfies `Φ`
over the germ field iff the trajectory `f(t')` eventually satisfies `Φ` over `R`. -/
theorem realization_bridge (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) (hqf : Φ.IsQuantifierFree) :
    (fun i => germHom t ht (c i)) ∈ Φ.realization (C := SemialgGerm R)
      ↔ EvNhd (fun s => (fun i => (c i : (Fin 1 → R) → R) (constPt s)) ∈ Φ.realization (C := R)) := by
  obtain ⟨f1, f2⟩ := forward_bridge t ht c Φ hqf
  refine ⟨f1, fun hev => ?_⟩
  by_contra hϕ
  exact EvNhd.not_and_of_disjoint R hev (f2 hϕ) (fun s h => h.2 h.1)

/-! ### Proposition 3.16, part 1: membership in `Ext(S, R⟨ε⟩)` -/

/-- **BPR Proposition 3.16 (first part).** Let `S ⊆ Rᵏ` be semialgebraic and let `f₁, …, f_k` be
semialgebraic continuous functions on `(0, t)` representing germs `ϕ₁, …, ϕ_k`. Then the germ tuple
`ϕ` lies in `Ext(S, R⟨ε⟩)` (here the real closed germ field, identified with `R⟨ε⟩` by Theorem 3.14)
exactly when the trajectory `f(t')` eventually lies in `S` as `t' → 0⁺`. -/
theorem proposition_3_16_mem (t : R) (ht : 0 < t) (c : Fin k → semialgContSubring t)
    (S : Set (Fin k → R)) (hS : IsSemialgebraicSet S) :
    (fun i => germHom t ht (c i)) ∈ extension (R' := SemialgGerm R) S hS
      ↔ EvNhd (fun s => (fun i => (c i : (Fin 1 → R) → R) (constPt s)) ∈ S) := by
  have : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  obtain ⟨Φ, hqf, hSeq⟩ := semialgebraic_isQFRealizable S hS
  rw [ext_eq hS hSeq, realization_bridge t ht c Φ hqf, ← hSeq]

/-! ### Proposition 3.16, part 3: `Ext(f, R⟨ε⟩)(ε) = ϕ` -/

/-- The projection `u ↦ u 0` is semialgebraic and continuous on any `(0, t)`. -/
theorem isSemialgContinuousOn_proj (t : R) :
    IsSemialgContinuousOn (rightNbhd t) (fun u : Fin 1 → R => u 0) := by
  have hsf : scalarFun (fun u : Fin 1 → R => u 0) = polynomialMap ![MvPolynomial.X 0] := by
    funext u i; rw [Subsingleton.elim i 0]; simp [scalarFun, constPt, polynomialMap]
  exact ⟨by rw [hsf]; exact isSemialgebraicFunction_polynomialMap (isSemialgebraicSet_rightNbhd t) _,
    by rw [hsf]; exact (continuous_polynomialMap _).continuousOn⟩

/-- The identity representative `u ↦ u 0` (representing `ε`) as an element of `semialgContSubring t`. -/
noncomputable def idSub (t : R) : semialgContSubring t :=
  ⟨fun u => u 0, mem_semialgContSubring.mpr (isSemialgContinuousOn_proj t)⟩

theorem germHom_idSub (t : R) (ht : 0 < t) : germHom t ht (idSub t) = idGerm := by
  rw [germHom_apply]; exact Quotient.sound ⟨1, one_pos, fun _ _ _ => rfl⟩

/-- **BPR Proposition 3.16 (last part).** `Ext(f, R⟨ε⟩)(ε) = ϕ`: extending the representative tuple
`f = (f₁, …, f_k)` (a semialgebraic function `(0, t) → Rᵏ`) and evaluating at `ε` returns the germ
tuple `ϕ`. Formalized as graph membership: the point `(ε, ϕ)` lies in `Ext(graph f, R⟨ε⟩)`, which is
the graph of `Ext(f)`, so `Ext(f)(ε) = ϕ`. This is the special case `S = (0, t)`, `g = f`, with `ε`
the germ of the identity (`germHom_idSub`); the trajectory `(t', f(t'))` lies in `graph f` for all
small `t'`, so Claim 1 applies. -/
theorem proposition_3_16_id [Nonempty (Fin k)] (t : R) (ht : 0 < t)
    (c : Fin k → semialgContSubring t) :
    Fin.append (fun _ : Fin 1 => idGerm) (fun i => germHom t ht (c i))
      ∈ extension (R' := SemialgGerm R)
          (funGraph (rightNbhd t) (fun x : Fin 1 → R => fun i => (c i : (Fin 1 → R) → R) x))
          (isSemialgebraicFunction_of_coords
            (fun j => (mem_semialgContSubring.mp (c j).2).1)) := by
  set c' : Fin (1 + k) → semialgContSubring t :=
    Fin.append (fun _ : Fin 1 => idSub t) c with hc'
  have hgermtup : (fun i => germHom t ht (c' i))
      = Fin.append (fun _ : Fin 1 => idGerm) (fun i => germHom t ht (c i)) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i
    · rw [hc', Fin.append_left, Fin.append_left, germHom_idSub]
    · rw [hc', Fin.append_right, Fin.append_right]
  rw [← hgermtup]
  refine (proposition_3_16_mem t ht c' _ _).mpr ?_
  refine ⟨t, ht, fun s hs hst => ?_⟩
  show (fun i => (c' i : (Fin 1 → R) → R) (constPt s))
    ∈ funGraph (rightNbhd t) (fun x : Fin 1 → R => fun i => (c i : (Fin 1 → R) → R) x)
  rw [mem_funGraph]
  have hin : (fun i => (c' i : (Fin 1 → R) → R) (constPt s)) ∘ Fin.castAdd k = constPt s := by
    funext a
    show ((c' (Fin.castAdd k a) : (Fin 1 → R) → R) (constPt s)) = s
    rw [hc', Fin.append_left]; rfl
  have hout : (fun i => (c' i : (Fin 1 → R) → R) (constPt s)) ∘ Fin.natAdd 1
      = fun j => (c j : (Fin 1 → R) → R) (constPt s) := by
    funext j
    show ((c' (Fin.natAdd 1 j) : (Fin 1 → R) → R) (constPt s)) = _
    rw [hc', Fin.append_right]
  refine ⟨?_, ?_⟩
  · rw [hin]; exact ⟨hs, hst⟩
  · rw [hin, hout]

/-! ### Proposition 3.16, part 2: `Ext(g, R⟨ε⟩)(ϕ) = g ∘ ϕ` -/

/-- The trajectory `u ↦ (c₁(u), …, c_k(u))` is a semialgebraic function on `(0, t)`. -/
theorem traj_isSemialgebraicFunction [Nonempty (Fin k)] (t : R)
    (c : Fin k → semialgContSubring t) :
    IsSemialgebraicFunction (rightNbhd t)
      (fun u : Fin 1 → R => fun i => (c i : (Fin 1 → R) → R) u) :=
  isSemialgebraicFunction_of_coords (fun j => (mem_semialgContSubring.mp (c j).2).1)

/-- **Coordinate-wise continuity (euclidean topology).** A map into `Rˡ` whose coordinate functions
are each continuous on `S` is continuous on `S`. -/
theorem continuousOn_of_components {ℓ : ℕ} [Nonempty (Fin ℓ)]
    {f : (Fin k → R) → (Fin ℓ → R)} {S : Set (Fin k → R)}
    (h : ∀ j, ContinuousOn (fun x : Fin k → R => fun _ : Fin 1 => f x j) S) :
    ContinuousOn f S := by
  rw [continuousOn_iff_ball]
  intro x hx r hr
  set ε : R := r / ((ℓ : R) + 1) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hcomp : ∀ j, ∃ δ, 0 < δ ∧ ∀ y ∈ S, euclideanNorm (y - x) < δ → |f y j - f x j| < ε := by
    intro j
    obtain ⟨δ, hδ, hb⟩ := (continuousOn_iff_ball.mp (h j)) x hx ε hε
    refine ⟨δ, hδ, fun y hy hyx => ?_⟩
    calc |f y j - f x j|
        = |((fun _ : Fin 1 => f y j) - (fun _ : Fin 1 => f x j)) 0| := by simp
      _ ≤ euclideanNorm ((fun _ : Fin 1 => f y j) - (fun _ : Fin 1 => f x j)) := abs_coord_le_norm _ 0
      _ < ε := hb y hy hyx
  choose δ hδpos hδ using hcomp
  refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, fun y hy hyx => ?_⟩
  · rw [Finset.lt_inf'_iff]; exact fun j _ => hδpos j
  have hcompbd : ∀ j, |f y j - f x j| < ε := fun j =>
    hδ j y hy (lt_of_lt_of_le hyx (Finset.inf'_le _ (Finset.mem_univ j)))
  have hsq : euclideanNormSq (f y - f x) < r ^ 2 := by
    have h1 : euclideanNormSq (f y - f x) = ∑ j, (f y j - f x j) ^ 2 := by
      simp only [euclideanNormSq, Pi.sub_apply]
    rw [h1]
    have h2 : ∑ j : Fin ℓ, (f y j - f x j) ^ 2 < ∑ _j : Fin ℓ, ε ^ 2 :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun j _ => by nlinarith [hcompbd j, abs_nonneg (f y j - f x j), sq_abs (f y j - f x j)])
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : (ℓ : R) * ε ^ 2 < r ^ 2 := by
      rw [hεdef, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hr hr, sq_nonneg ((ℓ : R)), Nat.cast_nonneg (α := R) ℓ]
    linarith
  nlinarith [euclideanNorm_sq (f y - f x), euclideanNorm_nonneg (f y - f x), hr, hsq]

/-- The trajectory is continuous on `(0, t)`. -/
theorem traj_continuousOn [Nonempty (Fin k)] (t : R) (c : Fin k → semialgContSubring t) :
    ContinuousOn (fun u : Fin 1 → R => fun i => (c i : (Fin 1 → R) → R) u) (rightNbhd t) :=
  continuousOn_of_components fun i => (mem_semialgContSubring.mp (c i).2).2

/-- The composite `(g ∘ f)_j`: the `j`-th coordinate of `g` applied to the trajectory, as an element
of `semialgContSubring t`. These are the representatives of the germ tuple `g ∘ ϕ`. -/
noncomputable def germCompTuple [Nonempty (Fin k)] {ℓ : ℕ} (t : R)
    (c : Fin k → semialgContSubring t) (g : (Fin k → R) → (Fin ℓ → R)) {S : Set (Fin k → R)}
    (hg : ∀ j, IsSemialgContinuousOn S (fun y => g y j))
    (hmaps : Set.MapsTo (fun u : Fin 1 → R => fun i => (c i : (Fin 1 → R) → R) u) (rightNbhd t) S)
    (j : Fin ℓ) : semialgContSubring t :=
  ⟨fun u => g (fun i => (c i : (Fin 1 → R) → R) u) j,
    mem_semialgContSubring.mpr
      ⟨proposition_2_84 (traj_isSemialgebraicFunction t c) (hg j).1 hmaps,
        (hg j).2.comp (traj_continuousOn t c) hmaps⟩⟩

/-- **BPR Proposition 3.16 (second part).** Let `g : S → Rˡ` be a semialgebraic continuous function
(given coordinate-wise) defined on the image of the trajectory `f` on `(0, t)`. Then
`Ext(g, R⟨ε⟩)(ϕ) = g ∘ ϕ`, formalized as graph membership: the point `(ϕ, g ∘ ϕ)` lies in
`Ext(graph g, R⟨ε⟩)`, the graph of `Ext(g, R⟨ε⟩)`. (The hypothesis `hmaps` says `g` is defined on the
image of `f`; it forces the trajectory into `S`, whence `ϕ ∈ Ext(S)` by the first part.) -/
theorem proposition_3_16_comp [Nonempty (Fin k)] {ℓ : ℕ} [Nonempty (Fin ℓ)] (t : R) (ht : 0 < t)
    (c : Fin k → semialgContSubring t) (g : (Fin k → R) → (Fin ℓ → R)) {S : Set (Fin k → R)}
    (hg : ∀ j, IsSemialgContinuousOn S (fun y => g y j))
    (hmaps : Set.MapsTo (fun u : Fin 1 → R => fun i => (c i : (Fin 1 → R) → R) u) (rightNbhd t) S) :
    Fin.append (fun i => germHom t ht (c i))
        (fun j => germHom t ht (germCompTuple t c g hg hmaps j))
      ∈ extension (R' := SemialgGerm R) (funGraph S g)
          (isSemialgebraicFunction_of_coords (fun j => (hg j).1)) := by
  set c' : Fin (k + ℓ) → semialgContSubring t :=
    Fin.append c (germCompTuple t c g hg hmaps) with hc'
  have hgermtup : (fun i => germHom t ht (c' i))
      = Fin.append (fun i => germHom t ht (c i))
          (fun j => germHom t ht (germCompTuple t c g hg hmaps j)) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · rw [hc', Fin.append_left, Fin.append_left]
    · rw [hc', Fin.append_right, Fin.append_right]
  rw [← hgermtup]
  refine (proposition_3_16_mem t ht c' _ _).mpr ?_
  refine ⟨t, ht, fun s hs hst => ?_⟩
  show (fun i => (c' i : (Fin 1 → R) → R) (constPt s)) ∈ funGraph S g
  rw [mem_funGraph]
  have hin : (fun i => (c' i : (Fin 1 → R) → R) (constPt s)) ∘ Fin.castAdd ℓ
      = fun i => (c i : (Fin 1 → R) → R) (constPt s) := by
    funext i
    show ((c' (Fin.castAdd ℓ i) : (Fin 1 → R) → R) (constPt s)) = _
    rw [hc', Fin.append_left]
  have hout : (fun i => (c' i : (Fin 1 → R) → R) (constPt s)) ∘ Fin.natAdd k
      = fun j => g (fun i => (c i : (Fin 1 → R) → R) (constPt s)) j := by
    funext j
    show ((c' (Fin.natAdd k j) : (Fin 1 → R) → R) (constPt s)) = _
    rw [hc', Fin.append_right]; rfl
  rw [hin, hout]
  exact ⟨hmaps ⟨hs, hst⟩, rfl⟩
