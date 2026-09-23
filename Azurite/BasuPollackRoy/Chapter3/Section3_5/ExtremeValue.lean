/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_4
import Azurite.BasuPollackRoy.Chapter3.Section3_4.Theorem_3_20
import Azurite.BasuPollackRoy.Chapter3.Section3_5.Limits

/-! # BPR §3.5 — extreme values on a closed bounded interval

The unnumbered remark opening BPR §3.5: **Theorem 3.20 implies that a semialgebraic function
continuous on a closed and bounded interval is bounded and attains its bounds**
(`exists_min_max_Icc`).

The interval `[a, b]` (as the subset `Icc (constPt a) (constPt b)` of the line `R¹`) is
semialgebraic, closed, and bounded, so by Theorem 3.20 the image `f([a, b])` is closed and
bounded. Its section `T ⊆ R` is then a nonempty, bounded-above semialgebraic set, so it has a
least upper bound `c` by o-minimality (`ConstOnGaps.exists_isLUB`, as in the IVT of §3.1) — and
`c ∈ T` because the image is closed: otherwise a ball around `constPt c` would miss `f([a, b])`,
contradicting leastness. The minimum follows by applying the maximum to `-f`. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### `Fin 1` helpers -/

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Every point of the line `R¹` is the constant point of its coordinate. -/
theorem constPt_eta (y : Fin 1 → R) : constPt (y 0) = y :=
  funext fun i => by rw [Fin.eq_zero i]; rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem euclideanNormSq_fin_one (w : Fin 1 → R) : euclideanNormSq w = w 0 ^ 2 := by
  simp [euclideanNormSq]

omit [Field R] [IsRealClosed R] in
/-- Membership in the segment `[constPt a, constPt b] ⊆ R¹`, for an arbitrary point. -/
theorem mem_Icc_fin_one {a b : R} {y : Fin 1 → R} :
    y ∈ Set.Icc (constPt a) (constPt b) ↔ a ≤ y 0 ∧ y 0 ≤ b := by
  rw [← constPt_eta y, mem_Icc_constPt]
  exact Iff.rfl

/-! ### `[a, b]` is semialgebraic, closed, and bounded -/

omit [IsRealClosed R] in
/-- The interval `[a, b] ⊆ R¹` is semialgebraic. -/
theorem isSemialgebraicSet_Icc (a b : R) :
    IsSemialgebraicSet (Set.Icc (constPt a) (constPt b)) := by
  have heq : Set.Icc (constPt a) (constPt b)
      = {y : Fin 1 → R | eval y (X 0 - C a) ≥ 0} ∩ {y | eval y (X 0 - C b) ≤ 0} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, map_sub, eval_X, eval_C, ge_iff_le,
      sub_nonneg, sub_nonpos, mem_Icc_fin_one]
  rw [heq]
  exact (IsSemialgebraicSet.geZero _).inter (IsSemialgebraicSet.leZero _)

/-- The interval `[a, b] ⊆ R¹` is closed. -/
theorem isClosed_Icc_constPt (a b : R) : IsClosed (Set.Icc (constPt a) (constPt b)) := by
  rw [isClosed_iff]
  rw [isOpen_iff]
  intro y hy
  rw [Set.mem_compl_iff, mem_Icc_fin_one, not_and_or, not_le, not_le] at hy
  have hkey : ∀ s t r : R, 0 < r → (s - t) ^ 2 < r ^ 2 → |s - t| < r := by
    intro s t r hr hsq
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd hsq (not_lt.mpr (by nlinarith [abs_nonneg (s - t), sq_abs (s - t)]))
  rcases hy with hya | hyb
  · refine ⟨y, a - y 0, by linarith, mem_openBall_self y (by linarith), fun z hz => ?_⟩
    rw [mem_openBall, euclideanNormSq_fin_one, Pi.sub_apply] at hz
    rw [Set.mem_compl_iff, mem_Icc_fin_one, not_and_or]
    exact Or.inl (not_le.mpr (by
      have := abs_lt.mp (hkey _ _ _ (by linarith) hz)
      linarith [this.1]))
  · refine ⟨y, y 0 - b, by linarith, mem_openBall_self y (by linarith), fun z hz => ?_⟩
    rw [mem_openBall, euclideanNormSq_fin_one, Pi.sub_apply] at hz
    rw [Set.mem_compl_iff, mem_Icc_fin_one, not_and_or]
    exact Or.inr (not_le.mpr (by
      have := abs_lt.mp (hkey _ _ _ (by linarith) hz)
      linarith [this.2]))

/-- The interval `[a, b] ⊆ R¹` is bounded. -/
theorem isBoundedSet_Icc (a b : R) : IsBoundedSet (Set.Icc (constPt a) (constPt b)) := by
  refine ⟨|a| + |b| + 1, by positivity, fun y hy => ?_⟩
  rw [mem_Icc_fin_one] at hy
  rw [mem_closedBall, sub_zero, euclideanNormSq_fin_one]
  have h1 : -(|a| + |b| + 1) ≤ y 0 := by
    have := neg_abs_le a; have := abs_nonneg b; linarith [hy.1]
  have h2 : y 0 ≤ |a| + |b| + 1 := by
    have := le_abs_self b; have := abs_nonneg a; linarith [hy.2]
  nlinarith

/-! ### The extreme value theorem -/

/-- The maximum half: a semialgebraic function continuous on `[a, b]` attains a maximum. -/
theorem exists_max_Icc {f : (Fin 1 → R) → (Fin 1 → R)} {a b : R} (hab : a ≤ b)
    (hSf : IsSemialgebraicFunction (Set.Icc (constPt a) (constPt b)) f)
    (hcont : ContinuousOn f (Set.Icc (constPt a) (constPt b))) :
    ∃ d, (a ≤ d ∧ d ≤ b) ∧ ∀ x, a ≤ x → x ≤ b →
      f (constPt x) 0 ≤ f (constPt d) 0 := by
  set S := Set.Icc (constPt a) (constPt b) with hSd
  have hS : IsSemialgebraicSet S := isSemialgebraicSet_Icc a b
  have hScl : IsClosed S := isClosed_Icc_constPt a b
  have hSb : IsBoundedSet S := isBoundedSet_Icc a b
  -- the coordinatewise hypothesis of Theorem 3.20, from the bundled ones
  have hg : ∀ j : Fin 1, IsSemialgContinuousOn S (fun y => f y j) := by
    intro j
    rw [Fin.eq_zero j]
    have hfeq : scalarFun (fun y => f y 0) = f := funext fun y => constPt_eta (f y)
    rw [IsSemialgContinuousOn, hfeq]
    exact ⟨hSf, hcont⟩
  obtain ⟨hclosed, hbdd⟩ := theorem_3_20 S hS hScl hSb f hg
  have hTsa : IsSemialgebraicSet (f '' S) := (proposition_2_83 hSf).1 hS (subset_refl S)
  -- the section `T ⊆ R` of the image
  set T : Set R := constPt ⁻¹' (f '' S) with hTd
  have hCOG : ConstOnGaps T := isSemialgebraicSet_sect_constOnGaps hTsa
  have hval : ∀ y ∈ S, f y 0 ∈ T := fun y hy => by
    show constPt (f y 0) ∈ f '' S
    rw [constPt_eta (f y)]
    exact Set.mem_image_of_mem f hy
  have hne : T.Nonempty :=
    ⟨f (constPt a) 0, hval _ (mem_Icc_constPt.mpr ⟨le_refl a, hab⟩)⟩
  have hbddAbove : BddAbove T := by
    obtain ⟨M, hM, hsub⟩ := hbdd
    refine ⟨M, fun t ht => ?_⟩
    have hball := hsub ht
    rw [mem_closedBall, sub_zero, euclideanNormSq_fin_one] at hball
    have hball' : t ^ 2 ≤ M ^ 2 := hball
    nlinarith [hball']
  obtain ⟨c, hc⟩ := hCOG.exists_isLUB hne hbddAbove
  -- the LUB lies in `T` because the image is closed
  have hcT : c ∈ T := by
    by_contra hcT
    have hmem : (f '' S)ᶜ ∈ nhds (constPt c) := hclosed.isOpen_compl.mem_nhds hcT
    obtain ⟨r, hr, hsub⟩ := mem_nhds_iff_openBall.mp hmem
    obtain ⟨t, htT, htgt⟩ : ∃ t ∈ T, c - r < t := by
      by_contra hcon
      push Not at hcon
      have : c ≤ c - r := hc.2 (fun t ht => hcon t ht)
      linarith
    have htle : t ≤ c := hc.1 htT
    have hin : constPt t ∈ openBall (constPt c) r := by
      rw [mem_openBall, euclideanNormSq_fin_one, Pi.sub_apply]
      show (t - c) ^ 2 < r ^ 2
      nlinarith
    exact hsub hin htT
  obtain ⟨y, hyS, hyfc⟩ := hcT
  have hymem := mem_Icc_fin_one.mp hyS
  refine ⟨y 0, hymem, fun x hx1 hx2 => ?_⟩
  have hfx : f (constPt x) 0 ≤ c := hc.1 (hval _ (mem_Icc_constPt.mpr ⟨hx1, hx2⟩))
  have hfd : f (constPt (y 0)) 0 = c := by
    rw [constPt_eta y, hyfc]
    rfl
  rw [hfd]
  exact hfx

/-- **BPR §3.5 (unnumbered remark).** Theorem 3.20 implies that a semialgebraic function
continuous on a closed and bounded interval is bounded and attains its bounds: there are
`c, d ∈ [a, b]` with `f(c) ≤ f(x) ≤ f(d)` for all `x ∈ [a, b]`. -/
theorem exists_min_max_Icc {f : (Fin 1 → R) → (Fin 1 → R)} {a b : R} (hab : a ≤ b)
    (hSf : IsSemialgebraicFunction (Set.Icc (constPt a) (constPt b)) f)
    (hcont : ContinuousOn f (Set.Icc (constPt a) (constPt b))) :
    ∃ c d : R, (a ≤ c ∧ c ≤ b) ∧ (a ≤ d ∧ d ≤ b) ∧ ∀ x, a ≤ x → x ≤ b →
      f (constPt c) 0 ≤ f (constPt x) 0 ∧ f (constPt x) 0 ≤ f (constPt d) 0 := by
  obtain ⟨d, hd, hdmax⟩ := exists_max_Icc hab hSf hcont
  obtain ⟨c, hcmem, hcmax⟩ :=
    exists_max_Icc hab hSf.neg (ContinuousOn.fin_one_neg hcont)
  refine ⟨c, d, hcmem, hd, fun x hx1 hx2 => ⟨?_, hdmax x hx1 hx2⟩⟩
  have := hcmax x hx1 hx2
  simp only [Pi.neg_apply, neg_le_neg_iff] at this
  exact this

end Azurite.BPR
