/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.Lemma_2_74
import Azurite.BasuPollackRoy.Chapter2.Section2_1.SignAtPoint
import Azurite.BasuPollackRoy.Chapter2.Section2_1.IntermediateValueProperty
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_20
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_22

/-!
# BPR Lemma 2.75

Let `σ` be a strict sign condition on `𝒬`. Whether or not `Reali(σ) = ∅`
is determined by the degrees and leading-coefficient signs of the signed
remainder sequences `SRemS(C, C')` (with `C = ∏_{Q} Q`) and
`SRemS(C', C''𝒬^α)` for all `α ∈ A = {0,1,2}^𝒬`.

## The geometric reduction

The heart of the proof is `lemma_2_75_reduction`: for strict `σ`,

`Reali(σ) ≠ ∅  ⟺  σ = sign-vec at −∞  ∨  σ = sign-vec at +∞  ∨
                    σ is realized at some root of C'`,

where `C = ∏ Q` and `C' = C'`. The realization `Reali(σ)` is a union of
connected components of `R ∖ Zer(C)`, each an interval whose two endpoints
are `±∞` or roots of `C`. An unbounded component contributes a `±∞`
sign-vector; a bounded component `(a, b)` (between consecutive roots of
`C`) contains a root of `C'` by Rolle (`proposition_2_22`), at which `σ`
is realized (constant sign on the interval, `proposition_2_20`).

This subsumes BPR's three cases (no roots / one root / `≥ 2` roots): the
`±∞` disjuncts cover the unbounded components, and the `C'`-root disjunct
is exactly the situation of Lemma 2.74 (with `P = C'`), which determines
it from the Tarski queries `TaQ(𝒬^α, C')`, hence from the leading-
coefficient signs of `SRemS(C', C''𝒬^α)` (Theorem 2.61). The signs at
`±∞` are the signs of the leading coefficients (with the degree parity at
`−∞`).
-/

open scoped Polynomial Matrix

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `P` has sign `signAtPosInfty P` at `+∞`. -/
theorem hasSignAtPosInfty_self (P : R[X]) : HasSignAtPosInfty P (signAtPosInfty P) := by
  rw [signAtPosInfty_eq_sign_leadingCoeff]; exact hasSignAtPosInfty_leadingCoeff P

/-- `P` has sign `signAtNegInfty P` at `−∞`. -/
theorem hasSignAtNegInfty_self (P : R[X]) : HasSignAtNegInfty P (signAtNegInfty P) := by
  rw [signAtNegInfty_eq_sign_leadingCoeff]; exact hasSignAtNegInfty_leadingCoeff P

/-- A point below all of a finite family of bounds. -/
theorem exists_lt_forall {ι : Type*} [Fintype ι] (M : ι → R) : ∃ x, ∀ i, x < M i := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨0, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨x, hx⟩ := exists_lt (Finset.univ.inf' Finset.univ_nonempty M)
    exact ⟨x, fun i => lt_of_lt_of_le hx (Finset.inf'_le _ (Finset.mem_univ i))⟩

/-- A point above all of a finite family of bounds. -/
theorem exists_gt_forall {ι : Type*} [Fintype ι] (M : ι → R) : ∃ x, ∀ i, M i < x := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨0, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨x, hx⟩ := exists_gt (Finset.univ.sup' Finset.univ_nonempty M)
    exact ⟨x, fun i => lt_of_le_of_lt (Finset.le_sup' _ (Finset.mem_univ i)) hx⟩

/-- If `σ` is the sign-vector of `Q` at `+∞`, it is realized (far enough to
the right). -/
theorem realizable_of_eq_signAtPosInfty {ι : Type*} [Fintype ι] (σ : SignCondition ι)
    (Q : ι → R[X]) (h : ∀ i, σ i = signAtPosInfty (Q i)) :
    (σ.realization (fun i x => (Q i).eval x)).Nonempty := by
  choose M hM using fun i => hasSignAtPosInfty_self (Q i)
  obtain ⟨x, hx⟩ := exists_gt_forall M
  exact ⟨x, fun i => (hM i x (hx i)).trans (h i).symm⟩

/-- If `σ` is the sign-vector of `Q` at `−∞`, it is realized (far enough to
the left). -/
theorem realizable_of_eq_signAtNegInfty {ι : Type*} [Fintype ι] (σ : SignCondition ι)
    (Q : ι → R[X]) (h : ∀ i, σ i = signAtNegInfty (Q i)) :
    (σ.realization (fun i x => (Q i).eval x)).Nonempty := by
  choose M hM using fun i => hasSignAtNegInfty_self (Q i)
  obtain ⟨x, hx⟩ := exists_lt_forall M
  exact ⟨x, fun i => (hM i x (hx i)).trans (h i).symm⟩

/-- If `P` has no root above `x` (and `P x ≠ 0`), then `sign (P x)` is the
sign of `P` at `+∞`. -/
theorem sign_eq_signAtPosInfty_of_no_root_above (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (x : R) (hx : P.eval x ≠ 0) (hno : ∀ y, x < y → P.eval y ≠ 0) :
    SignType.sign (P.eval x) = signAtPosInfty P := by
  have hP : P ≠ 0 := fun h => hx (by rw [h]; simp)
  obtain ⟨M, hM⟩ := hasSignAtPosInfty_self P
  obtain ⟨y, hy⟩ := exists_gt (max x M)
  have hxy : x < y := lt_of_le_of_lt (le_max_left _ _) hy
  have hsy : SignType.sign (P.eval y) = signAtPosInfty P :=
    hM y (lt_of_le_of_lt (le_max_right _ _) hy)
  by_contra hne
  rw [← hsy] at hne
  have hPy : P.eval y ≠ 0 := by
    rw [← sign_ne_zero, hsy, signAtPosInfty_eq_sign_leadingCoeff, sign_ne_zero]
    exact leadingCoeff_ne_zero.mpr hP
  have hprod : P.eval x * P.eval y < 0 := by
    rcases lt_or_gt_of_ne hx with hx0 | hx0 <;> rcases lt_or_gt_of_ne hPy with hy0 | hy0
    · exact absurd ((sign_eq_neg_one_iff.mpr hx0).trans (sign_eq_neg_one_iff.mpr hy0).symm) hne
    · exact mul_neg_of_neg_of_pos hx0 hy0
    · exact mul_neg_of_pos_of_neg hx0 hy0
    · exact absurd ((sign_eq_one_iff.mpr hx0).trans (sign_eq_one_iff.mpr hy0).symm) hne
  obtain ⟨z, hxz, _, hPz⟩ := hIVP P x y hxy hprod
  exact hno z hxz hPz

/-- If `P` has no root below `x` (and `P x ≠ 0`), then `sign (P x)` is the
sign of `P` at `−∞`. -/
theorem sign_eq_signAtNegInfty_of_no_root_below (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (x : R) (hx : P.eval x ≠ 0) (hno : ∀ y, y < x → P.eval y ≠ 0) :
    SignType.sign (P.eval x) = signAtNegInfty P := by
  have hP : P ≠ 0 := fun h => hx (by rw [h]; simp)
  obtain ⟨M, hM⟩ := hasSignAtNegInfty_self P
  obtain ⟨y, hy⟩ := exists_lt (min x M)
  have hyx : y < x := lt_of_lt_of_le hy (min_le_left _ _)
  have hsy : SignType.sign (P.eval y) = signAtNegInfty P :=
    hM y (lt_of_lt_of_le hy (min_le_right _ _))
  by_contra hne
  rw [← hsy] at hne
  have hsign_ne : signAtNegInfty P ≠ 0 := by
    rw [signAtNegInfty_eq_sign_leadingCoeff]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (sign_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP))
  have hPy : P.eval y ≠ 0 := sign_ne_zero.mp (hsy.trans_ne hsign_ne)
  have hprod : P.eval y * P.eval x < 0 := by
    rcases lt_or_gt_of_ne hPy with hy0 | hy0 <;> rcases lt_or_gt_of_ne hx with hx0 | hx0
    · exact absurd ((sign_eq_neg_one_iff.mpr hy0).trans (sign_eq_neg_one_iff.mpr hx0).symm).symm hne
    · exact mul_neg_of_neg_of_pos hy0 hx0
    · exact mul_neg_of_pos_of_neg hy0 hx0
    · exact absurd ((sign_eq_one_iff.mpr hy0).trans (sign_eq_one_iff.mpr hx0).symm).symm hne
  obtain ⟨z, _, hzx, hPz⟩ := hIVP P y x hyx hprod
  exact hno z hzx hPz

/-- **The geometric reduction of BPR Lemma 2.75.** For a strict sign
condition `σ` on a family `Q` of nonzero polynomials, `Reali(σ)` is
non-empty if and only if `σ` is the sign-vector of `Q` at `−∞`, or at
`+∞`, or `σ` is realized at some root of `C' = (∏ Q)'`. -/
theorem lemma_2_75_reduction (hIVP : HasIntermediateValueProperty R) {ι : Type*} [Fintype ι]
    (σ : SignCondition ι) (hσ : σ.IsStrict) (Q : ι → R[X]) (hQ : ∀ i, Q i ≠ 0) :
    (σ.realization (fun i x => (Q i).eval x)).Nonempty
      ↔ (∀ i, σ i = signAtNegInfty (Q i)) ∨ (∀ i, σ i = signAtPosInfty (Q i))
        ∨ (σ.realizationOver (∏ i, Q i).derivative Q).Nonempty := by
  classical
  constructor
  · rintro ⟨x, hxreal⟩
    have hxreal : ∀ i, SignType.sign ((Q i).eval x) = σ i := hxreal
    set C : R[X] := ∏ i, Q i with hCdef
    have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hQ i)
    have hQx : ∀ i, (Q i).eval x ≠ 0 := fun i => by rw [← sign_ne_zero, hxreal i]; exact hσ i
    have hCx : C.eval x ≠ 0 := by
      rw [hCdef, eval_prod]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hQx i)
    have hQrootC : ∀ (i) (r), (Q i).eval r = 0 → C.eval r = 0 := fun i r hr => by
      rw [hCdef, eval_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) hr
    set above := C.roots.toFinset.filter (x < ·) with habovedef
    set below := C.roots.toFinset.filter (· < x) with hbelowdef
    by_cases haboveEmpty : above = ∅
    · refine Or.inr (Or.inl fun i => ?_)
      rw [← hxreal i]
      apply sign_eq_signAtPosInfty_of_no_root_above hIVP (Q i) x (hQx i)
      intro y hy hQy
      have hm : y ∈ above := by
        rw [habovedef, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hC]
        exact ⟨hQrootC i y hQy, hy⟩
      rw [haboveEmpty] at hm; simp at hm
    · by_cases hbelowEmpty : below = ∅
      · refine Or.inl fun i => ?_
        rw [← hxreal i]
        apply sign_eq_signAtNegInfty_of_no_root_below hIVP (Q i) x (hQx i)
        intro y hy hQy
        have hm : y ∈ below := by
          rw [hbelowdef, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hC]
          exact ⟨hQrootC i y hQy, hy⟩
        rw [hbelowEmpty] at hm; simp at hm
      · refine Or.inr (Or.inr ?_)
        have hbne : below.Nonempty := Finset.nonempty_iff_ne_empty.mpr hbelowEmpty
        have hane : above.Nonempty := Finset.nonempty_iff_ne_empty.mpr haboveEmpty
        set a := below.max' hbne
        set b := above.min' hane
        have ha_mem := below.max'_mem hbne
        have hb_mem := above.min'_mem hane
        have hax : a < x := (Finset.mem_filter.mp ha_mem).2
        have hxb : x < b := (Finset.mem_filter.mp hb_mem).2
        have hCa : C.eval a = 0 :=
          (mem_roots hC).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp ha_mem).1)
        have hCb : C.eval b = 0 :=
          (mem_roots hC).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hb_mem).1)
        have hab : a < b := lt_trans hax hxb
        have hfree : ∀ r, a < r → r < b → C.eval r ≠ 0 := by
          intro r har hrb hCr
          rcases lt_trichotomy r x with hrx | hrx | hrx
          · have hm : r ∈ below := by
              rw [hbelowdef, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hC]
              exact ⟨hCr, hrx⟩
            exact absurd (below.le_max' r hm) (not_le.mpr har)
          · rw [hrx] at hCr; exact hCx hCr
          · have hm : r ∈ above := by
              rw [habovedef, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hC]
              exact ⟨hCr, hrx⟩
            exact absurd (above.min'_le r hm) (not_le.mpr hrb)
        obtain ⟨c, hc, hCc⟩ := Proposition2_22.proposition_2_22 hIVP C hab hCa hCb
        refine ⟨c, hCc, fun i => ?_⟩
        have hQno : ∀ z ∈ Set.Ioo a b, (Q i).eval z ≠ 0 :=
          fun z hz hQz => hfree z hz.1 hz.2 (hQrootC i z hQz)
        have hsigncx : SignType.sign ((Q i).eval c) = SignType.sign ((Q i).eval x) := by
          rcases Proposition2_20.proposition_2_20 hIVP (Q i) a b hQno with hpos | hneg
          · rw [sign_eq_one_iff.mpr (hpos c hc), sign_eq_one_iff.mpr (hpos x ⟨hax, hxb⟩)]
          · rw [sign_eq_neg_one_iff.mpr (hneg c hc), sign_eq_neg_one_iff.mpr (hneg x ⟨hax, hxb⟩)]
        rw [hsigncx]; exact hxreal i
  · rintro (h | h | ⟨c, _, hc⟩)
    · exact realizable_of_eq_signAtNegInfty σ Q h
    · exact realizable_of_eq_signAtPosInfty σ Q h
    · exact ⟨c, hc⟩

/-- **BPR Lemma 2.75.** For a strict sign condition `σ = signFn s j` on a
family `Q` of nonzero polynomials with `C' = (∏ Q)' ≠ 0`, whether
`Reali(σ)` is empty is determined by data: it is non-empty iff `σ` is the
sign-vector of `Q` at `−∞` or at `+∞` (the signs of the leading
coefficients, with degree parity at `−∞`), or the `σ`-component of
`Mₛ⁻¹ · TaQ(𝒬^A, C')` is positive (Lemma 2.74, with the Tarski queries
`TaQ(𝒬^α, C')` determined by `SRemS(C', C''𝒬^α)` via Theorem 2.61). -/
theorem lemma_2_75 (hIVP : HasIntermediateValueProperty R) (s : Nat) (Q : Fin s → R[X])
    (hQ : ∀ i, Q i ≠ 0) (hC' : (∏ i, Q i).derivative ≠ 0) (j : Fin (3 ^ s))
    (hσ : SignCondition.IsStrict (signFn s j)) :
    (SignCondition.realization (signFn s j) (fun i x => (Q i).eval x)).Nonempty
      ↔ (∀ i, signFn s j i = signAtNegInfty (Q i))
        ∨ (∀ i, signFn s j i = signAtPosInfty (Q i))
        ∨ 0 < ((signMatrixQ s)⁻¹ *ᵥ
            (fun α => (tarskiQuery (familyPow Q (expFn s α)) (∏ i, Q i).derivative : ℚ))) j := by
  rw [lemma_2_75_reduction hIVP (signFn s j) hσ Q hQ,
    lemma_2_74 s (∏ i, Q i).derivative Q hC' j]

end Azurite.BPR
