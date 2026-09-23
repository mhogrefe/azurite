/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_c_a
import Azurite.BasuPollackRoy.Chapter3.Section3_3.GermPolynomial
import Azurite.BasuPollackRoy.Chapter3.Section3_3.GermRootSelection
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Lemma_3_12
import Azurite.BasuPollackRoy.Chapter3.Section3_3.SemialgebraicGermOrdered

/-! # BPR §3.3, Proposition 3.11 — the germ field is real closed

The germs of semialgebraic continuous functions at the right of the origin form a real closed field.

The ordered-field structure is established in `SemialgebraicGermOrdered.lean`. By Theorem 2.11, an
ordered field is real closed as soon as it has the intermediate value property; and by Lemma 3.12, the
intermediate value property need only be checked for *separable* polynomials. This file records that
reduction: `IsRealClosed (SemialgGerm R)` follows from
`HasSeparableIntermediateValueProperty (SemialgGerm R)`.

The remaining hypothesis — the intermediate value property for separable polynomials over the germ
field — is BPR's deferred argument (parametrized roots via Proposition 3.10, root-counting via
Sturm/Tarski, and continuous root selection); it is developed separately. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR Proposition 3.11 (reduction).** The germ field is real closed provided it has the
intermediate value property for separable polynomials. -/
theorem isRealClosed_semialgGerm_of_separableIVP
    (h : HasSeparableIntermediateValueProperty (SemialgGerm R)) :
    IsRealClosed (SemialgGerm R) :=
  Theorem2_11.theorem_2_11_c_a (lemma_3_12.mpr h)

end Azurite.BPR

/-! # BPR §3.3 — the germ field has the separable intermediate value property (Proposition 3.11)

Assembling the milestones: given a separable germ polynomial `P` with `P(ϕ₁) P(ϕ₂) < 0`, take
representatives over a common interval `(0, t₁)` on which the fiber `P(t, ·)` is nonzero with a fixed
number of simple roots and a sign change between `f₁(t)` and `f₂(t)`. The selection
`smallestRootIn Q f₁ f₂` is semialgebraic (`isSemialgebraicFunction_smallestRootIn`) and continuous
(`continuousOn_smallestRootIn`), hence a germ `c` with `ϕ₁ < c < ϕ₂` and `P(c) = 0`. So the germ
field has the separable intermediate value property, and is therefore real closed (Proposition 3.11). -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Converse of `germ_lt_eventually`:** an eventual pointwise strict inequality of representatives
gives a strict inequality of germs. -/
theorem germ_lt_of_eventually {r₁ r₂ : SemialgGermRep R}
    (h : ∃ t, 0 < t ∧ ∀ s : R, 0 < s → s < t → r₁.toFun (constPt s) < r₂.toFun (constPt s)) :
    (Quotient.mk (semialgGermSetoid R) r₁ : SemialgGerm R) < Quotient.mk _ r₂ := by
  show IsPosGerm (Quotient.mk _ r₂ - Quotient.mk _ r₁)
  rw [sub_eq_add_neg, germ_mk_neg, germ_mk_add, isPosGerm_mk]
  obtain ⟨t, ht, H⟩ := h
  refine ⟨t, ht, fun s hs hst => ?_⟩
  have hH := H s hs hst
  simp only [SemialgGermRep.add_toFun, SemialgGermRep.neg_toFun, Pi.add_apply, Pi.neg_apply]
  linarith

/-- **BPR's separable intermediate value property for the germ field.** -/
theorem hasSeparableIntermediateValueProperty_semialgGerm :
    HasSeparableIntermediateValueProperty (SemialgGerm R) := by
  intro P hsep A B hAB hsign
  obtain ⟨f₁, rfl⟩ := Quotient.exists_rep A
  obtain ⟨f₂, rfl⟩ := Quotient.exists_rep B
  obtain ⟨t₀, ht₀, Q, hQ₀, hrep, hQdeg⟩ := exists_germPoly_rep P
  -- `P` is nonconstant (it changes sign).
  have hp1 : 1 ≤ P.natDegree := by
    by_contra h
    rw [not_le, Nat.lt_one_iff] at h
    rw [Polynomial.eq_C_of_natDegree_eq_zero h, Polynomial.eval_C, Polynomial.eval_C] at hsign
    exact absurd hsign (not_lt.mpr (mul_self_nonneg _))
  -- The four eventual facts, on intervals `(0, ·)`.
  obtain ⟨tc, htc, Hcoprime⟩ := germPoly_coprime ht₀ hQ₀ hrep hQdeg hp1 hsep
  obtain ⟨tn, htn, r, Hcount⟩ := germPoly_rootCount_eventually_constant ht₀ hQ₀ hrep hQdeg hp1
  obtain ⟨ts, hts, Hsign⟩ := germPoly_sign_change ht₀ hQ₀ hrep f₁ f₂ hsign
  obtain ⟨tl, htl, Hlt⟩ := germ_lt_eventually hAB
  -- A common interval `(0, t₁)`.
  set t₁ : R := min (min (min tc tn) (min ts tl)) (min t₀ (min f₁.bound f₂.bound)) with ht₁def
  have ht₁ : 0 < t₁ :=
    lt_min (lt_min (lt_min htc htn) (lt_min hts htl))
      (lt_min ht₀ (lt_min f₁.bound_pos f₂.bound_pos))
  have le_tc : t₁ ≤ tc := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have le_tn : t₁ ≤ tn := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have le_ts : t₁ ≤ ts := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have le_tl : t₁ ≤ tl := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have le_t0 : t₁ ≤ t₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have le_b1 : t₁ ≤ f₁.bound :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have le_b2 : t₁ ≤ f₂.bound :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- restrict the coefficient/representative data to `(0, t₁)`
  have hQ₁ : HasSemialgContinuousCoeffs (rightNbhd t₁) Q := fun i =>
    (hQ₀ i).mono (isSemialgebraicSet_rightNbhd _) (rightNbhd_subset le_t0)
  have hf₁ := f₁.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd t₁) (rightNbhd_subset le_b1)
  have hf₂ := f₂.isSemialgContinuous.mono (isSemialgebraicSet_rightNbhd t₁) (rightNbhd_subset le_b2)
  -- convert the eventual facts to `∀ w ∈ rightNbhd t₁`
  have hwc : ∀ w : Fin 1 → R, w = constPt (w 0) := fun w => by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have hnz : ∀ w ∈ rightNbhd t₁, specializeAt Q w ≠ 0 := fun w hw => by
    rw [hwc w]; exact (Hcount (w 0) hw.1 (lt_of_lt_of_le hw.2 le_tn)).1
  have hcount : ∀ w ∈ rightNbhd t₁, (specializeAt Q w).roots.toFinset.card = r := fun w hw => by
    rw [hwc w]; exact (Hcount (w 0) hw.1 (lt_of_lt_of_le hw.2 le_tn)).2
  have hcoprime : ∀ w ∈ rightNbhd t₁,
      IsCoprime (specializeAt Q w) (Polynomial.derivative (specializeAt Q w)) := fun w hw => by
    rw [hwc w]; exact Hcoprime (w 0) hw.1 (lt_of_lt_of_le hw.2 le_tc)
  have hlt' : ∀ w ∈ rightNbhd t₁, f₁.toFun w < f₂.toFun w := fun w hw => by
    rw [hwc w]; exact Hlt (w 0) hw.1 (lt_of_lt_of_le hw.2 le_tl)
  have hsign' : ∀ w ∈ rightNbhd t₁,
      (specializeAt Q w).eval (f₁.toFun w) * (specializeAt Q w).eval (f₂.toFun w) < 0 := fun w hw => by
    rw [hwc w]; exact Hsign (w 0) hw.1 (lt_of_lt_of_le hw.2 le_ts)
  -- the selected root is a germ
  have hcsa := isSemialgebraicFunction_smallestRootIn hQ₁ hf₁.1 hf₂.1 hnz hlt' hsign'
  have hccont := continuousOn_smallestRootIn hQ₁ hnz hcount hcoprime hf₁.2 hf₂.2 hlt' hsign'
  set crep : SemialgGermRep R :=
    ⟨t₁, ht₁, smallestRootIn Q f₁.toFun f₂.toFun, ⟨hcsa, hccont⟩⟩ with hcrepdef
  -- the pointwise spec of the selection on `(0, t₁)`
  have hspec : ∀ s : R, 0 < s → s < t₁ →
      (specializeAt Q (constPt s)).eval (crep.toFun (constPt s)) = 0 ∧
        f₁.toFun (constPt s) < crep.toFun (constPt s) ∧
        crep.toFun (constPt s) < f₂.toFun (constPt s) := fun s hs hst => by
    obtain ⟨he, ha, hb, _⟩ := smallestRootIn_spec (hnz (constPt s) ⟨hs, hst⟩)
      (hlt' (constPt s) ⟨hs, hst⟩) (hsign' (constPt s) ⟨hs, hst⟩)
    exact ⟨he, ha, hb⟩
  refine ⟨Quotient.mk _ crep, ?_, ?_, ?_⟩
  · exact germ_lt_of_eventually ⟨t₁, ht₁, fun s hs hst => (hspec s hs hst).2.1⟩
  · exact germ_lt_of_eventually ⟨t₁, ht₁, fun s hs hst => (hspec s hs hst).2.2⟩
  · obtain ⟨_, heval⟩ := germPoly_eval ht₀ hQ₀ hrep crep
    rw [heval]
    apply Quotient.sound
    refine ⟨t₁, ht₁, fun s hs hst => ?_⟩
    simp only [SemialgGermRep.zero_toFun, Pi.zero_apply]
    rw [eval_pi_apply]
    exact (hspec s hs hst).1

/-- **BPR Proposition 3.11.** The germs of semialgebraic continuous functions at the right of the
origin form a real closed field. -/
theorem isRealClosed_semialgGerm : IsRealClosed (SemialgGerm R) :=
  isRealClosed_semialgGerm_of_separableIVP hasSeparableIntermediateValueProperty_semialgGerm

end Azurite.BPR
