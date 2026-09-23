/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_3
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Corollary_2_79

/-! # BPR §3.1, Proposition 3.4 — Intermediate Value Theorem (semialgebraic)

A semialgebraic continuous `f : [a,b] → R` with `f(a) f(b) < 0` has a zero in `(a,b)`.

Over a general real closed field `R` there is no Dedekind completeness, but **semialgebraic** subsets
of `R` do have suprema (o-minimality). We capture this via `ConstOnGaps`: a set `T ⊆ R` is constant
on the gaps between a finite set of breakpoints. This invariant is preserved by Boolean operations
and holds for one-variable polynomial sign loci (breakpoints = roots), hence for every semialgebraic
section (`isSemialgebraicSet_sect_constOnGaps`); a `ConstOnGaps` set that is nonempty and bounded
above has a least upper bound (`ConstOnGaps.exists_isLUB`). The IVT then follows by the classical
supremum argument. -/

namespace Azurite.BPR

open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `T ⊆ R` is **constant on gaps**: there is a finite set of breakpoints `F` such that `T` has the
same truth value on any two points with no breakpoint between them. -/
def ConstOnGaps (T : Set R) : Prop :=
  ∃ F : Finset R, ∀ x y : R, x < y → (∀ z ∈ F, z < x ∨ y < z) → (x ∈ T ↔ y ∈ T)

/-- **A nonempty, bounded-above `ConstOnGaps` set has a least upper bound.** The LUB is the smallest
breakpoint that is an upper bound. -/
theorem ConstOnGaps.exists_isLUB {T : Set R} (h : ConstOnGaps T)
    (hne : T.Nonempty) (hbdd : BddAbove T) : ∃ c, IsLUB T c := by
  classical
  obtain ⟨F, hF⟩ := h
  obtain ⟨M, hM⟩ := hbdd
  set F' : Finset R := insert M F with hF'd
  have hF'ne : F'.Nonempty := ⟨M, Finset.mem_insert_self _ _⟩
  have hF' : ∀ x y : R, x < y → (∀ z ∈ F', z < x ∨ y < z) → (x ∈ T ↔ y ∈ T) :=
    fun x y hxy hz => hF x y hxy fun z hz' => hz z (Finset.mem_insert_of_mem hz')
  set C : Finset R := F'.filter (· ∈ upperBounds T) with hCd
  have hmaxUB : F'.max' hF'ne ∈ upperBounds T :=
    fun t ht => le_trans (hM ht) (Finset.le_max' F' M (Finset.mem_insert_self _ _))
  have hCne : C.Nonempty := ⟨F'.max' hF'ne, Finset.mem_filter.mpr ⟨F'.max'_mem hF'ne, hmaxUB⟩⟩
  set c := C.min' hCne with hcd
  have hcUB : c ∈ upperBounds T := (Finset.mem_filter.mp (C.min'_mem hCne)).2
  refine ⟨c, hcUB, ?_⟩
  intro d hd
  by_contra hlt
  rw [not_le] at hlt
  -- there is `s ∈ T` lying above every breakpoint `≤ d`
  obtain ⟨s, hsT, hsP⟩ : ∃ s ∈ T, ∀ z ∈ F', z ≤ d → z < s := by
    by_cases hPne : (F'.filter (· ≤ d)).Nonempty
    · set p := (F'.filter (· ≤ d)).max' hPne with hpd
      have hple : p ≤ d := (Finset.mem_filter.mp ((F'.filter (· ≤ d)).max'_mem hPne)).2
      have hpF' : p ∈ F' := (Finset.mem_filter.mp ((F'.filter (· ≤ d)).max'_mem hPne)).1
      obtain ⟨s, hsT, hps⟩ : ∃ s ∈ T, p < s := by
        by_contra hcon
        push Not at hcon
        exact absurd (le_trans (Finset.min'_le C p
          (Finset.mem_filter.mpr ⟨hpF', fun t ht => hcon t ht⟩)) hple) (not_le.mpr hlt)
      exact ⟨s, hsT, fun z hzF' hzd =>
        lt_of_le_of_lt (Finset.le_max' (F'.filter (· ≤ d)) z
          (Finset.mem_filter.mpr ⟨hzF', hzd⟩)) hps⟩
    · obtain ⟨s, hsT⟩ := hne
      rw [Finset.not_nonempty_iff_eq_empty] at hPne
      refine ⟨s, hsT, fun z hzF' hzd => ?_⟩
      have hz : z ∈ F'.filter (· ≤ d) := Finset.mem_filter.mpr ⟨hzF', hzd⟩
      rw [hPne] at hz; exact absurd hz (Finset.notMem_empty z)
  -- no breakpoint lies in `(d, c)`
  have hnogap : ∀ z ∈ F', d < z → c ≤ z := fun z hzF' hdz =>
    Finset.min'_le C z (Finset.mem_filter.mpr ⟨hzF', fun t ht => le_trans (hd ht) (le_of_lt hdz)⟩)
  set m := (d + c) / 2 with hmd
  have hdm : d < m := by rw [hmd]; exact left_lt_add_div_two.mpr hlt
  have hmc : m < c := by rw [hmd]; exact add_div_two_lt_right.mpr hlt
  have hsm : s < m := lt_of_le_of_lt (hd hsT) hdm
  have hcond : ∀ z ∈ F', z < s ∨ m < z := by
    intro z hzF'
    rcases le_or_gt z d with hzd | hzd
    · exact Or.inl (hsP z hzF' hzd)
    · exact Or.inr (lt_of_lt_of_le hmc (hnogap z hzF' hzd))
  exact absurd (hd ((hF' s m hsm hcond).mp hsT)) (not_le.mpr hdm)

/-! ### `ConstOnGaps` is preserved by Boolean operations and holds for polynomial sign loci -/

omit [Field R] [IsStrictOrderedRing R] in
theorem constOnGaps_univ : ConstOnGaps (Set.univ : Set R) := ⟨∅, fun x y _ _ => by simp⟩

omit [Field R] [IsStrictOrderedRing R] in
theorem ConstOnGaps.compl {T : Set R} (h : ConstOnGaps T) : ConstOnGaps Tᶜ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun x y hxy hz => by simp only [Set.mem_compl_iff]; rw [hF x y hxy hz]⟩

omit [Field R] [IsStrictOrderedRing R] in
theorem ConstOnGaps.inter {S T : Set R} (hS : ConstOnGaps S) (hT : ConstOnGaps T) :
    ConstOnGaps (S ∩ T) := by
  obtain ⟨F, hF⟩ := hS; obtain ⟨G, hG⟩ := hT
  refine ⟨F ∪ G, fun x y hxy hz => ?_⟩
  rw [Set.mem_inter_iff, Set.mem_inter_iff]
  exact and_congr (hF x y hxy fun z hzF => hz z (Finset.mem_union_left _ hzF))
    (hG x y hxy fun z hzG => hz z (Finset.mem_union_right _ hzG))

variable [IsRealClosed R]

omit [IsRealClosed R] in
/-- A univariate polynomial zero locus is constant on the gaps between its roots. -/
theorem constOnGaps_zero_locus (q : R[X]) : ConstOnGaps {t : R | q.eval t = 0} := by
  classical
  by_cases hq : q = 0
  · subst hq; exact ⟨∅, fun x y _ _ => by simp⟩
  · refine ⟨q.roots.toFinset, fun x y hxy hz => ?_⟩
    have key : ∀ t : R, q.eval t = 0 → t ∈ q.roots.toFinset := fun t ht =>
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots').mpr ⟨hq, ht⟩)
    have hx0 : q.eval x ≠ 0 := fun h => by rcases hz x (key x h) with h' | h' <;> linarith
    have hy0 : q.eval y ≠ 0 := fun h => by rcases hz y (key y h) with h' | h' <;> linarith
    simp only [Set.mem_ofPred_eq]; exact ⟨fun h => absurd h hx0, fun h => absurd h hy0⟩

/-- A univariate polynomial positivity locus is constant on the gaps between the roots. -/
theorem constOnGaps_pos_locus (q : R[X]) : ConstOnGaps {t : R | 0 < q.eval t} := by
  classical
  by_cases hq : q = 0
  · subst hq; exact ⟨∅, fun x y _ _ => by simp⟩
  · refine ⟨q.roots.toFinset, fun x y hxy hz => ?_⟩
    have hrf : ∀ t ∈ Set.Icc x y, q.eval t ≠ 0 := by
      rintro t ⟨htx, hty⟩ ht
      have : t ∈ q.roots.toFinset := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots').mpr ⟨hq, ht⟩)
      rcases hz t this with h' | h' <;> linarith
    have hxC : x ∈ Set.Icc x y := ⟨le_refl x, le_of_lt hxy⟩
    have hyC : y ∈ Set.Icc x y := ⟨le_of_lt hxy, le_refl y⟩
    simp only [Set.mem_ofPred_eq]
    rcases const_sign_ordConnected Set.ordConnected_Icc q hrf with hpos | hneg
    · exact ⟨fun _ => hpos y hyC, fun _ => hpos x hxC⟩
    · exact ⟨fun h => absurd h (not_lt.mpr (le_of_lt (hneg x hxC))),
        fun h => absurd h (not_lt.mpr (le_of_lt (hneg y hyC)))⟩

omit [IsRealClosed R] in
/-- A finite intersection of one-variable zero loci is constant on gaps. -/
theorem constOnGaps_forall_zero (pset : Finset (MvPolynomial (Fin 1) R)) :
    ConstOnGaps {t : R | ∀ P ∈ pset,
      Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) P) = 0} := by
  classical
  induction pset using Finset.induction with
  | empty => simpa using constOnGaps_univ
  | insert P pset _ ih =>
    have heq : {t : R | ∀ Q ∈ insert P pset,
          Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) Q) = 0}
        = {t : R | Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) P) = 0} ∩
          {t : R | ∀ Q ∈ pset,
            Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) Q) = 0} := by
      ext t; simp only [Finset.forall_mem_insert, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [heq]; exact (constOnGaps_zero_locus _).inter ih

/-- **Every semialgebraic section is constant on gaps** (the constructive content of Cor. 2.79). -/
theorem isSemialgebraicSet_sect_constOnGaps {S : Set (Fin 1 → R)} (hS : IsSemialgebraicSet S) :
    ConstOnGaps (constPt ⁻¹' S) := by
  induction hS with
  | algebraic h =>
    obtain ⟨pset, rfl⟩ := h
    have hset : (constPt ⁻¹' Zer pset) = {t : R | ∀ P ∈ pset,
        Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) P) = 0} := by
      ext t
      simp only [Set.mem_preimage, Zer, Set.mem_ofPred_eq]
      exact forall_congr' fun P => imp_congr_right fun _ => by rw [eval_constPt_eq_eval_toPoly]
    rw [hset]; exact constOnGaps_forall_zero pset
  | pos_locus P =>
    have hset : (constPt ⁻¹' {x : Fin 1 → R | MvPolynomial.eval x P > 0})
        = {t : R | 0 < Polynomial.eval t (MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X) P)} := by
      ext t; simp only [Set.mem_preimage, Set.mem_ofPred_eq, gt_iff_lt]
      rw [eval_constPt_eq_eval_toPoly]
    rw [hset]; exact constOnGaps_pos_locus _
  | compl _ ih => rw [Set.preimage_compl]; exact ih.compl
  | inter _ _ ihV ihW => rw [Set.preimage_inter]; exact ihV.inter ihW

/-! ### The Intermediate Value Theorem -/

omit [Field R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem mem_Icc_constPt {a b t : R} :
    constPt t ∈ Set.Icc (constPt a) (constPt b) ↔ a ≤ t ∧ t ≤ b := by
  simp only [Set.mem_Icc]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1 0, h2 0⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, fun _ => h2⟩⟩

/-- The IVT in the case `f(a) > 0 > f(b)`: the supremum of `{x ∈ [a,b] | f(x) > 0}` is a zero. -/
theorem ivt_pos {f : (Fin 1 → R) → (Fin 1 → R)} {a b : R} (hab : a < b)
    (hSf : IsSemialgebraicFunction (Set.Icc (constPt a) (constPt b)) f)
    (hcont : ContinuousOn f (Set.Icc (constPt a) (constPt b)))
    (hfa : 0 < f (constPt a) 0) (hfb : f (constPt b) 0 < 0) :
    ∃ x : R, a < x ∧ x < b ∧ f (constPt x) 0 = 0 := by
  have hPos : IsSemialgebraicSet {y : Fin 1 → R | 0 < y 0} := by
    have heq : {y : Fin 1 → R | 0 < y 0} = {y | MvPolynomial.eval y (MvPolynomial.X 0) > 0} := by
      ext y; simp [MvPolynomial.eval_X]
    rw [heq]; exact IsSemialgebraicSet.gtZero _
  have hA := (proposition_2_83 hSf).2 hPos
  set A' : Set R := constPt ⁻¹'
    (Set.Icc (constPt a) (constPt b) ∩ f ⁻¹' {y : Fin 1 → R | 0 < y 0}) with hA'd
  have hmemA' : ∀ t : R, t ∈ A' ↔ (a ≤ t ∧ t ≤ b) ∧ 0 < f (constPt t) 0 := fun t => by
    rw [hA'd, Set.mem_preimage, Set.mem_inter_iff, mem_Icc_constPt, Set.mem_preimage,
      Set.mem_ofPred_eq]
  have hCOG : ConstOnGaps A' := isSemialgebraicSet_sect_constOnGaps hA
  have haA : a ∈ A' := (hmemA' a).mpr ⟨⟨le_refl a, le_of_lt hab⟩, hfa⟩
  obtain ⟨c, hc⟩ := hCOG.exists_isLUB ⟨a, haA⟩ ⟨b, fun t ht => ((hmemA' t).mp ht).1.2⟩
  have hca : a ≤ c := hc.1 haA
  have hcb : c ≤ b := hc.2 (fun t ht => ((hmemA' t).mp ht).1.2)
  rw [continuousOn_fin_one_iff] at hcont
  -- the constant-section norm is the coordinate distance
  have hnorm : ∀ s : R, euclideanNorm (constPt s - constPt c) = |s - c| := fun s => by
    rw [show constPt s - constPt c = constPt (s - c) from by funext i; simp [constPt],
      euclideanNorm_fin_one]; rfl
  have hfc_le : f (constPt c) 0 ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    obtain ⟨δ, hδ, hδf⟩ := hcont (constPt c) (mem_Icc_constPt.mpr ⟨hca, hcb⟩) _ hpos
    have hcb' : c < b := lt_of_le_of_ne hcb (fun h => by rw [h] at hpos; linarith)
    set ε := min (δ / 2) ((b - c) / 2) with hεd
    have hε : 0 < ε := lt_min (by linarith) (by linarith)
    have hεδ : ε ≤ δ / 2 := min_le_left _ _
    have hεb : ε ≤ (b - c) / 2 := min_le_right _ _
    have hfpos : 0 < f (constPt (c + ε)) 0 := by
      have := hδf (constPt (c + ε)) (mem_Icc_constPt.mpr ⟨by linarith, by linarith⟩)
        (by rw [hnorm, abs_of_pos (by linarith)]; linarith)
      have := abs_lt.mp this; linarith [this.1]
    exact absurd (hc.1 ((hmemA' _).mpr ⟨⟨by linarith, by linarith⟩, hfpos⟩)) (by linarith)
  have hfc_ge : 0 ≤ f (constPt c) 0 := by
    by_contra hneg
    rw [not_le] at hneg
    obtain ⟨δ, hδ, hδf⟩ := hcont (constPt c) (mem_Icc_constPt.mpr ⟨hca, hcb⟩) _ (by linarith : (0:R) < -f (constPt c) 0)
    obtain ⟨t, htA', htc⟩ : ∃ t, t ∈ A' ∧ c - δ < t := by
      by_contra hcon
      push Not at hcon
      exact absurd (hc.2 (fun t ht => hcon t ht)) (by linarith)
    have htab := ((hmemA' t).mp htA').1
    have htle : t ≤ c := hc.1 htA'
    have hflt := hδf (constPt t) (mem_Icc_constPt.mpr htab)
      (by rw [hnorm, abs_of_nonpos (by linarith), neg_sub]; linarith)
    have := abs_lt.mp hflt
    exact absurd ((hmemA' t).mp htA').2 (by linarith [this.2])
  have hfc : f (constPt c) 0 = 0 := le_antisymm hfc_le hfc_ge
  refine ⟨c, lt_of_le_of_ne hca (fun h => by rw [← h] at hfc; linarith),
    lt_of_le_of_ne hcb (fun h => by rw [h] at hfc; linarith), hfc⟩

/-- **BPR Proposition 3.4 (Intermediate Value Theorem).** A semialgebraic continuous function `f`
on `[a,b]` with `f(a) f(b) < 0` has a zero in `(a,b)`. -/
theorem proposition_3_4 {f : (Fin 1 → R) → (Fin 1 → R)} {a b : R} (hab : a < b)
    (hSf : IsSemialgebraicFunction (Set.Icc (constPt a) (constPt b)) f)
    (hcont : ContinuousOn f (Set.Icc (constPt a) (constPt b)))
    (hsign : f (constPt a) 0 * f (constPt b) 0 < 0) :
    ∃ x : R, a < x ∧ x < b ∧ f (constPt x) 0 = 0 := by
  rcases mul_neg_iff.mp hsign with ⟨hfa, hfb⟩ | ⟨hfa, hfb⟩
  · exact ivt_pos hab hSf hcont hfa hfb
  · obtain ⟨x, hxa, hxb, hxf⟩ :=
      ivt_pos hab hSf.neg (ContinuousOn.fin_one_neg hcont) (by simpa using hfa) (by simpa using hfb)
    exact ⟨x, hxa, hxb, by simpa using hxf⟩

end Azurite.BPR
