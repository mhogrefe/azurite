/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.SturmTarskiTransfer
import Azurite.BasuPollackRoy.Chapter2.Section2_4.ParametrizedTarskiQuery
import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunctionTuple
import Azurite.BasuPollackRoy.Chapter3.Section3_3.GermPolynomial
import Azurite.BasuPollackRoy.Chapter3.Section3_3.SemialgebraicGermField

/-! # BPR §3.3 — the coefficient locus of a fixed distinct-root count is semialgebraic

Towards the `Aᵣ` partition of BPR's intermediate value argument: the set of coefficient vectors
`y ∈ R^n` for which the polynomial `∑ᵢ yᵢ Yⁱ` is nonzero with exactly `c` distinct real roots is a
semialgebraic subset of `R^n`.

This is the parametrized-root-counting content, obtained from the Sturm–Tarski machinery of
Theorem 2.62: the number of distinct roots is the Tarski query `TaQ(1, ·)`
(`tarskiQuery_one`), and the locus where a *generic* polynomial has Tarski query `= c` is
semialgebraic over the base field (`tarskiLocus_isSemialgebraicSetOver`). Pulling this back along a
semialgebraic coefficient map yields the eventual constancy of the root count of a germ polynomial. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The **generic polynomial** `∑ᵢ Xᵢ Yⁱ` of degree `< n`, whose `i`-th coefficient is the `i`-th
indeterminate `Xᵢ`. -/
noncomputable def genericPoly (n : ℕ) : Polynomial (MvPolynomial (Fin n) R) :=
  ∑ i : Fin n, Polynomial.monomial (i : ℕ) (MvPolynomial.X i)

/-- The polynomial `∑ᵢ yᵢ Yⁱ` with coefficient vector `y`. -/
noncomputable def coeffPoly (n : ℕ) (y : Fin n → R) : Polynomial R :=
  ∑ i : Fin n, Polynomial.monomial (i : ℕ) (y i)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem genericPoly_map (n : ℕ) (y : Fin n → R) :
    (genericPoly n).map (MvPolynomial.aeval (R := R) y).toRingHom = coeffPoly n y := by
  rw [genericPoly, coeffPoly, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_monomial]
  congr 1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]

/-- **The coefficient locus of a fixed distinct-root count is semialgebraic.** For each target count
`c`, the set of coefficient vectors `y ∈ R^n` for which `∑ᵢ yᵢ Yⁱ` is nonzero with exactly `c`
distinct real roots is a semialgebraic subset of `R^n`. -/
theorem coeffPoly_rootCount_isSemialgebraicSet (n : ℕ) (c : ℤ) :
    IsSemialgebraicSet
      {y : Fin n → R | coeffPoly n y ≠ 0 ∧ ((coeffPoly n y).roots.toFinset.card : ℤ) = c} := by
  apply IsSemialgebraicSet.of_definedOver (D := R)
  have hset :
      {y : Fin n → R | coeffPoly n y ≠ 0 ∧ ((coeffPoly n y).roots.toFinset.card : ℤ) = c}
        = {y : Fin n → R | (genericPoly n).map (MvPolynomial.aeval (R := R) y).toRingHom ≠ 0 ∧
            tarskiQuery
              (familyPow (fun _ : Fin 1 =>
                ((1 : Polynomial (MvPolynomial (Fin n) R)).map
                  (MvPolynomial.aeval (R := R) y).toRingHom))
                (fun _ => 0))
              ((genericPoly n).map (MvPolynomial.aeval (R := R) y).toRingHom) = c} := by
    ext y
    simp only [Set.mem_ofPred_eq, genericPoly_map]
    have hfam : familyPow (fun _ : Fin 1 =>
        ((1 : Polynomial (MvPolynomial (Fin n) R)).map (MvPolynomial.aeval (R := R) y).toRingHom))
        (fun _ => 0) = (1 : Polynomial R) := by simp [familyPow]
    rw [hfam, tarskiQuery_one]
  rw [hset]
  exact tarskiLocus_isSemialgebraicSetOver (genericPoly n) (fun _ : Fin 1 => 1) (fun _ => 0) c
    (algebraMap R R).injective

end Azurite.BPR

/-! # BPR §3.3 — the number of distinct roots of a germ polynomial is eventually constant

Pulling back the coefficient-space root-count locus `Bᵣ` (`coeffPoly_rootCount_isSemialgebraicSet`)
along the semialgebraic coefficient map `u ↦ (Q.coeff i u)ᵢ` shows that, for each fixed count `c`, the
set `Aᵣ` of small `t` for which `P(t, ·) = specializeAt Q t` is nonzero with exactly `c` distinct
roots is semialgebraic in `t`. Near `0⁺` the leading coefficient germ is nonzero, so `P(t, ·)` is
nonzero with a bounded number of distinct roots; the finitely many `Aᵣ` therefore cover an interval
`(0, t₁)`, and the one-dimensional `FUOC_dichotomy_at_zero` forces one of them to contain a whole
interval `(0, t)`. This is BPR's "the number of distinct roots is eventually constant", the
combinatorial heart of the intermediate value argument for the germ field. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The `j`-th coefficient of `coeffPoly n y` is `y j` (and `0` past degree `n`). -/
theorem coeffPoly_coeff (n : ℕ) (y : Fin n → R) (j : ℕ) :
    (coeffPoly n y).coeff j = if h : j < n then y ⟨j, h⟩ else 0 := by
  rw [coeffPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  split
  · next h =>
    rw [Finset.sum_eq_single (⟨j, h⟩ : Fin n)]
    · simp
    · intro b _ hb; rw [ite_eq_right]; exact fun hbj => hb (Fin.ext hbj)
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  · next h =>
    rw [Finset.sum_eq_zero]
    intro i _; rw [ite_eq_right]; intro hij; exact h (hij ▸ i.isLt)

/-- The **coefficient map** `u ↦ (Q.coeff i u)ᵢ : R¹ → Rⁿ`. -/
noncomputable def coeffMap (n : ℕ) (Q : Polynomial ((Fin 1 → R) → R)) :
    (Fin 1 → R) → (Fin n → R) :=
  fun u i => Q.coeff (i : ℕ) u

omit [IsRealClosed R] in
/-- **Cover-to-interval for one-dimensional semialgebraic sets.** If finitely many finite-unions-of-
ord-connected sets cover an interval `(0, t₀)`, then one of them contains a whole interval `(0, t)`
near the origin. -/
theorem exists_Ioo_subset_of_cover_FUOC {ι : Type*} (s : Finset ι) {W : ι → Set R} {t₀ : R}
    (ht₀ : 0 < t₀) (hW : ∀ c ∈ s, IsFinUnionOfOrdConnected (W c))
    (hcover : Set.Ioo 0 t₀ ⊆ ⋃ c ∈ s, W c) :
    ∃ c ∈ s, ∃ t, 0 < t ∧ Set.Ioo 0 t ⊆ W c := by
  by_contra hcon
  push Not at hcon
  have hdisj : ∀ c ∈ s, ∃ t, 0 < t ∧ Set.Ioo 0 t ∩ W c = ∅ := by
    intro c hc
    rcases FUOC_dichotomy_at_zero (hW c hc) with ⟨t, ht, hsub⟩ | h
    · exact absurd hsub (hcon c hc t ht)
    · exact h
  choose! tf htf_pos htf_disj using hdisj
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with rfl | h
    · refine absurd (hcover (a := t₀ / 2) ⟨by positivity, by linarith⟩) ?_
      simp
    · exact h
  set t := min t₀ (s.inf' hne tf) with ht
  have ht_pos : 0 < t :=
    lt_min ht₀ ((Finset.lt_inf'_iff hne).mpr fun c hc => htf_pos c hc)
  obtain ⟨c, hc, hmem⟩ := Set.mem_iUnion₂.mp (hcover (a := t / 2) ⟨by positivity,
    lt_of_lt_of_le (half_lt_self ht_pos) (min_le_left _ _)⟩)
  have hmem' : t / 2 ∈ Set.Ioo 0 (tf c) :=
    ⟨by positivity, lt_of_lt_of_le (half_lt_self ht_pos)
      (le_trans (min_le_right _ _) (Finset.inf'_le tf hc))⟩
  have hd := htf_disj c hc
  rw [Set.eq_empty_iff_forall_notMem] at hd
  exact hd (t / 2) ⟨hmem', hmem⟩

section GermPoly

variable {P : Polynomial (SemialgGerm R)} {t₀ : R} (ht₀ : 0 < t₀)
  {Q : Polynomial ((Fin 1 → R) → R)} (hQ : HasSemialgContinuousCoeffs (rightNbhd t₀) Q)
  (hrep : ∀ i, (Quotient.mk (semialgGermSetoid R) ⟨t₀, ht₀, Q.coeff i, hQ i⟩ : SemialgGerm R)
    = P.coeff i)
  (hQdeg : Q.natDegree ≤ P.natDegree)

include hQ in
/-- The coefficient map is a semialgebraic function on `(0, t₀)` — a vector of the semialgebraic
coefficient functions of `Q`. -/
theorem coeffMap_isSemialgebraicFunction :
    IsSemialgebraicFunction (rightNbhd t₀) (coeffMap (P.natDegree + 1) Q) :=
  isSemialgebraicFunction_of_coords fun j => (hQ (j : ℕ)).1

include hQdeg in
/-- Plugging the coefficient vector of `u` back into the generic polynomial recovers the fiber
`specializeAt Q u = P(u, ·)`. -/
theorem coeffPoly_coeffMap_eq (u : Fin 1 → R) :
    coeffPoly (P.natDegree + 1) (coeffMap (P.natDegree + 1) Q u) = specializeAt Q u := by
  refine Polynomial.ext fun j => ?_
  rw [coeffPoly_coeff, specializeAt, Polynomial.coeff_map, Pi.evalRingHom_apply]
  by_cases h : j < P.natDegree + 1
  · rw [dite_eq_left h]; rfl
  · rw [dite_eq_right h]
    have : Q.coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQdeg (by omega))
    rw [this]; rfl

include hQ hQdeg in
/-- **The fixed-distinct-root-count locus is semialgebraic.** For each target count `c`, the set of
`u ∈ (0, t₀)` for which the fiber `P(u, ·)` is nonzero with exactly `c` distinct roots is a
semialgebraic subset of `R¹`. -/
theorem germPoly_rootCount_isSemialgebraicSet (c : ℤ) :
    IsSemialgebraicSet {u : Fin 1 → R | u ∈ rightNbhd t₀ ∧
      specializeAt Q u ≠ 0 ∧ ((specializeAt Q u).roots.toFinset.card : ℤ) = c} := by
  have hpre := (proposition_2_83 (coeffMap_isSemialgebraicFunction (P := P) hQ)).2
    (coeffPoly_rootCount_isSemialgebraicSet (R := R) (P.natDegree + 1) c)
  have hset : (rightNbhd t₀ ∩ coeffMap (P.natDegree + 1) Q ⁻¹'
      {y : Fin (P.natDegree + 1) → R | coeffPoly (P.natDegree + 1) y ≠ 0 ∧
        ((coeffPoly (P.natDegree + 1) y).roots.toFinset.card : ℤ) = c})
      = {u : Fin 1 → R | u ∈ rightNbhd t₀ ∧
        specializeAt Q u ≠ 0 ∧ ((specializeAt Q u).roots.toFinset.card : ℤ) = c} := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      coeffPoly_coeffMap_eq (P := P) hQdeg]
  rwa [hset] at hpre

include hQdeg in
/-- The number of distinct roots of a fiber is bounded by `deg P`. -/
theorem rootCount_le (s : R) (_hs : specializeAt Q (constPt s) ≠ 0) :
    (specializeAt Q (constPt s)).roots.toFinset.card ≤ P.natDegree :=
  calc (specializeAt Q (constPt s)).roots.toFinset.card
      ≤ Multiset.card (specializeAt Q (constPt s)).roots := Multiset.toFinset_card_le _
    _ ≤ (specializeAt Q (constPt s)).natDegree := Polynomial.card_roots' _
    _ ≤ Q.natDegree := Polynomial.natDegree_map_le
    _ ≤ P.natDegree := hQdeg

include ht₀ hQ hrep hQdeg in
/-- **The number of distinct roots of `P(t, ·)` is eventually constant near `0⁺`.** For all small
`t`, the fiber `P(t, ·) = specializeAt Q t` is nonzero and has a fixed number `r` of distinct roots.
This is BPR's `Aᵣ`-partition conclusion: the leading coefficient germ is nonzero (so the fiber is
eventually nonzero with at most `deg P` distinct roots), the finitely many fixed-count loci are
semialgebraic and cover an interval `(0, t₁)`, and the one-dimensional dichotomy forces one to
contain a whole interval. -/
theorem germPoly_rootCount_eventually_constant (hp1 : 1 ≤ P.natDegree) :
    ∃ t, 0 < t ∧ ∃ r : ℕ, ∀ s : R, 0 < s → s < t →
      specializeAt Q (constPt s) ≠ 0 ∧ (specializeAt Q (constPt s)).roots.toFinset.card = r := by
  have hP0 : P ≠ 0 := fun h => by simp [h] at hp1
  have hlc : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hgne : (Quotient.mk (semialgGermSetoid R)
      ⟨t₀, ht₀, Q.coeff P.natDegree, hQ P.natDegree⟩ : SemialgGerm R) ≠ 0 := by
    rw [hrep]; exact hlc
  obtain ⟨tlc, htlc, Hlc⟩ := germ_ne_zero_eventually hgne
  -- Near `0⁺` the fiber is nonzero, since its leading coefficient is.
  have hnz : ∀ s : R, 0 < s → s < tlc → specializeAt Q (constPt s) ≠ 0 := by
    intro s hs hst hz
    refine Hlc s hs hst ?_
    show Q.coeff P.natDegree (constPt s) = 0
    have hcoeff : (specializeAt Q (constPt s)).coeff P.natDegree
        = Q.coeff P.natDegree (constPt s) := by
      rw [specializeAt, Polynomial.coeff_map, Pi.evalRingHom_apply]
    rw [← hcoeff, hz, Polynomial.coeff_zero]
  -- The fixed-count loci, pulled back to `R`, are finite unions of ord-connected sets.
  set W : ℕ → Set R := fun c => constPt ⁻¹' {u : Fin 1 → R | u ∈ rightNbhd t₀ ∧
    specializeAt Q u ≠ 0 ∧ ((specializeAt Q u).roots.toFinset.card : ℤ) = (c : ℤ)} with hW
  have hWfin : ∀ c ∈ Finset.range (P.natDegree + 1), IsFinUnionOfOrdConnected (W c) := fun c _ =>
    semialgebraic_sect_FUOC (germPoly_rootCount_isSemialgebraicSet (P := P) hQ hQdeg (c : ℤ))
  -- They cover `(0, min t₀ tlc)`.
  have hcover : Set.Ioo 0 (min t₀ tlc) ⊆ ⋃ c ∈ Finset.range (P.natDegree + 1), W c := by
    intro s hs
    obtain ⟨hs0, hst⟩ := hs
    have hsne : specializeAt Q (constPt s) ≠ 0 :=
      hnz s hs0 (lt_of_lt_of_le hst (min_le_right _ _))
    rw [Set.mem_iUnion₂]
    refine ⟨(specializeAt Q (constPt s)).roots.toFinset.card,
      Finset.mem_range.mpr (Nat.lt_succ_of_le (rootCount_le (P := P) hQdeg s hsne)), ?_⟩
    exact ⟨⟨hs0, lt_of_lt_of_le hst (min_le_left _ _)⟩, hsne, rfl⟩
  obtain ⟨c, _, t, ht, hsub⟩ := exists_Ioo_subset_of_cover_FUOC (Finset.range (P.natDegree + 1))
    (lt_min ht₀ htlc) hWfin hcover
  refine ⟨t, ht, c, fun s hs hst => ?_⟩
  obtain ⟨_, hne, hcard⟩ := hsub ⟨hs, hst⟩
  exact ⟨hne, by exact_mod_cast hcard⟩

end GermPoly

end Azurite.BPR
