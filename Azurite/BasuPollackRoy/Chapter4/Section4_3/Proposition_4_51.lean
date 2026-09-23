/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_50

/-!
# BPR Proposition 4.51: a polynomial splits iff its subdiscriminants form the staircase

Let `P = a_p X^p + ⋯ + a_0 ∈ R[X]`. All roots of `P` lie in `R` (equivalently, `P` splits
over `R`) if and only if there is `k` with `0 ≤ k ≤ p-1` such that `sDisc_i(P) > 0` for
`k ≤ i ≤ p-1` and `sDisc_i(P) = 0` for `0 ≤ i < k`.

* `⟹` Every polynomial with all roots in `R` is (a scalar multiple of) the characteristic
  polynomial of a diagonal symmetric matrix with entries in `R`; Proposition 4.50/4.49
  then forces the staircase sign pattern (the `a_p^{2k-2}` factor relating `sDisc_i(P)` to
  the monic subdiscriminant is an even power, hence positive, so signs are preserved).
* `⟸` From the staircase, the number of real roots is `p − k` (Theorem 4.34, via `PmV` of
  the subdiscriminant sequence) and the number of distinct complex roots is also `p − k`
  (Proposition 4.26, via `deg gcd(P, P')`); the counts agree, so all roots are real.
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open Matrix _root_.Polynomial

section

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Reusable splitting criterion -/

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- If a polynomial of degree `p` has `p − k` distinct roots in `R` and exactly `p − k`
distinct roots in an algebraically closed extension `C` (so every `C`-root is the image of
an `R`-root), then `P` splits over `R`. This is the "combine" step of Proposition 4.50,
factored out for reuse. -/
private theorem splits_of_distinct_counts_eq {C : Type*} [Field C] [Algebra R C]
    [IsAlgClosed C] [DecidableEq C] (P : R[X]) (hPne : P ≠ 0)
    (hcounts : P.roots.toFinset.card = (P.aroots C).toFinset.card) :
    Polynomial.Splits P := by
  classical
  set φ := algebraMap R C with hφ
  have hφinj : Function.Injective φ := FaithfulSMul.algebraMap_injective R C
  have hmapne : P.map φ ≠ 0 := by rwa [Ne, Polynomial.map_eq_zero_iff hφinj]
  rw [Polynomial.splits_iff_card_roots]
  have haroots_eq : P.aroots C = (P.map φ).roots := by rw [Polynomial.aroots]
  -- The φ-image of a distinct real root is a distinct complex root.
  have himg : ∀ r ∈ P.roots.toFinset, φ r ∈ (P.aroots C).toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset] at hr ⊢
    rw [haroots_eq, Polynomial.mem_roots hmapne]
    have hroot : Polynomial.eval r P = 0 := (Polynomial.mem_roots hPne).mp hr
    refine Polynomial.IsRoot.def.mpr ?_
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hroot, map_zero]
  -- Injective map between equal-card finsets is surjective.
  have hsurj : ∀ c ∈ (P.aroots C).toFinset, ∃ r ∈ P.roots.toFinset, φ r = c := by
    have hbij := Finset.surjOn_of_injOn_of_card_le
      (f := φ) (s := P.roots.toFinset) (t := (P.aroots C).toFinset)
      (fun r hr => himg r hr) (fun a _ b _ h => hφinj h) (by rw [hcounts])
    intro c hc
    obtain ⟨r, hr, hrc⟩ := hbij hc
    exact ⟨r, hr, hrc⟩
  -- Every complex root with multiplicity matches the φ-image of a real root.
  have hmulti : (P.map φ).roots = P.roots.map φ := by
    refine Multiset.ext.mpr (fun c => ?_)
    by_cases hcr : c ∈ Set.range φ
    · obtain ⟨r, rfl⟩ := hcr
      rw [Multiset.count_map_eq_count' φ _ hφinj]
      rw [Polynomial.count_roots, Polynomial.count_roots,
        ← Polynomial.eq_rootMultiplicity_map hφinj r]
    · have hc1 : Multiset.count c (P.map φ).roots = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        have : c ∈ (P.aroots C).toFinset := by
          rw [Multiset.mem_toFinset, haroots_eq]; exact hmem
        obtain ⟨r, _, hrc⟩ := hsurj c this
        exact hcr ⟨r, hrc⟩
      have hc2 : Multiset.count c (P.roots.map φ) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        rw [Multiset.mem_map] at hmem
        obtain ⟨r, _, hrc⟩ := hmem
        exact hcr ⟨r, hrc⟩
      rw [hc1, hc2]
  have hcardmap : (P.map φ).roots.card = P.natDegree := by
    rw [← haroots_eq, IsAlgClosed.card_aroots_eq_natDegree]
  rw [hmulti, Multiset.card_map] at hcardmap
  exact hcardmap

/-! ### `⟹`: the scaling transfer

If `P = C a · Q` with `a := P.leadingCoeff ≠ 0` and `Q` monic of the same degree (so the
roots multisets over `C` coincide), then `sDiscK P i = a^{2(p-i-1)} · sDiscK Q i`; the
factor is a square, hence the signs and zero-locus of the subdiscriminants agree. -/

omit [IsRealClosed R] in
/-- The scaling identity `sDiscK P i = a^{2((aroots).card - i - 1)} · sDiscK Q i` when
`P = C a · Q` with `Q` monic of equal degree. Proven by transporting through `sDisc` over
`C := AlgebraicClosure R` via Remark 4.29: the root-multiset-based part of `sDisc` is
identical for `P` and `Q` (same roots), differing only by the leading-coefficient power. -/
private theorem sDiscK_smul_eq {Q : R[X]} {P : R[X]} (hQmonic : Q.Monic)
    (heq : P = Polynomial.C P.leadingCoeff * Q) (hP : 0 < P.natDegree)
    (i : ℕ) (hi : i ≤ P.natDegree) :
    sDiscK P i = P.leadingCoeff ^ (2 * ((P.aroots (AlgebraicClosure R)).card - i) - 2)
      * sDiscK Q i := by
  classical
  set C := AlgebraicClosure R with hC
  set φ := algebraMap R C with hφ
  have hφinj : Function.Injective φ := FaithfulSMul.algebraMap_injective R C
  have ha : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (fun h => by
    rw [h] at hP; simp at hP)
  -- degrees: deg P = deg Q (both = p).
  have hdeg : P.natDegree = Q.natDegree := by
    rw [heq, Polynomial.natDegree_C_mul ha]
  have hQne : Q ≠ 0 := hQmonic.ne_zero
  have hQdeg : 0 < Q.natDegree := by omega
  -- roots multisets coincide over C: `P.aroots C = Q.aroots C`.
  have haroots : P.aroots C = Q.aroots C := by
    rw [heq, Polynomial.aroots_C_mul Q (a := P.leadingCoeff) ha]
  -- `sDisc P i = (algebraMap a)^(...) * sDisc Q i` from the definition of `sDisc`.
  have hsDisc : (sDisc P i : C)
      = φ P.leadingCoeff ^ (2 * ((P.aroots C).card - i) - 2) * sDisc Q i := by
    unfold sDisc
    rw [haroots, hQmonic.leadingCoeff, map_one, one_pow, one_mul, ← hφ]
  -- transport to `sDiscK` via Remark 4.29 (both sides positive degree).
  have hr29P := Remark_4_29 (C := C) P hP i hi
  have hr29Q := Remark_4_29 (C := C) Q hQdeg i (by omega)
  -- `φ (sDiscK P i) = φ (a^... * sDiscK Q i)`, then inject.
  have hkey : φ (sDiscK P i)
      = φ (P.leadingCoeff ^ (2 * ((P.aroots C).card - i) - 2) * sDiscK Q i) := by
    rw [hr29P, map_mul, map_pow, hr29Q, hsDisc]
  exact hφinj hkey

/-! ### Main statement -/

/-- **Proposition 4.51.** A polynomial `P` over a real closed field `R` splits over `R`
(all its roots lie in `R`) iff its subdiscriminants form a staircase: there is
`k ≤ p - 1` with `sDisc_i(P) > 0` for `k ≤ i ≤ p - 1` and `sDisc_i(P) = 0` for `i < k`. -/
theorem proposition_4_51 (P : R[X]) (hp : 0 < P.natDegree) :
    Polynomial.Splits P ↔
      ∃ k, k ≤ P.natDegree - 1 ∧
        (∀ i, k ≤ i → i ≤ P.natDegree - 1 → 0 < sDiscK P i) ∧
        (∀ i, i < k → sDiscK P i = 0) := by
  classical
  have hPne : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hp
  set p := P.natDegree with hpdef
  set AC := AlgebraicClosure R with hAC
  set φ := algebraMap R AC with hφ
  have hφinj : Function.Injective φ := FaithfulSMul.algebraMap_injective R AC
  have ha : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hderdeg : P.derivative.natDegree < P.natDegree :=
    Polynomial.natDegree_derivative_lt (by omega)
  constructor
  · ------------------------------------------------------------------
    -- ⟹ : Splits → staircase
    ------------------------------------------------------------------
    intro hsplit
    have hNeZero : NeZero p := ⟨by omega⟩
    -- Realize `P` (up to leading scalar) as the charpoly of a diagonal symmetric matrix.
    have hcardroots : P.roots.card = p := (Polynomial.splits_iff_card_roots.mp hsplit)
    set n := P.roots.toList.length with hn
    have hnp : n = p := by rw [hn, Multiset.length_toList, hcardroots]
    have hNeZeroN : NeZero n := ⟨by omega⟩
    -- enumeration of the roots
    set v : Fin n → R := fun i => P.roots.toList[i] with hv
    set M : Matrix (Fin n) (Fin n) R := Matrix.diagonal v with hM
    have hMsymm : M.IsSymm := Matrix.isSymm_diagonal v
    -- the multiset of values of `v` is exactly `P.roots`.
    have hvmap : (Finset.univ : Finset (Fin n)).val.map v = P.roots := by
      rw [Finset.val_univ_fin, hv, Multiset.map_coe, ← List.ofFn_eq_map,
        show (List.ofFn fun i => P.roots.toList[i]) = P.roots.toList from
          List.ofFn_getElem (xs := P.roots.toList)]
      exact Multiset.coe_toList _
    -- `M.charpoly = ∏ i, (X - C (v i))`.
    have hMcp : M.charpoly = ∏ i, (X - C (v i)) := by
      rw [hM, Matrix.charpoly_diagonal]
    -- `(∏ i, (X - C (v i))) = (P.roots.map (X - C ·)).prod`.
    have hprodroots : (∏ i, (X - C (v i))) = (P.roots.map (fun a => X - C a)).prod := by
      rw [Finset.prod_eq_multiset_prod, ← hvmap, Multiset.map_map]
      rfl
    -- `M.charpoly` is monic; its degree is `n`.
    have hMmonic : M.charpoly.Monic := M.charpoly_monic
    have hMdeg : M.charpoly.natDegree = n := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    -- `P = C a · M.charpoly` via `eq_prod_roots_of_splits_id`.
    have hPeq : P = Polynomial.C P.leadingCoeff * M.charpoly := by
      rw [hMcp, hprodroots]
      exact hsplit.eq_prod_roots
    -- Proposition 4.49 staircase for the matrix subdiscriminants.
    obtain ⟨k, hk, hpos, hzero⟩ := proposition_4_49 M hMsymm
    refine ⟨k, by omega, ?_, ?_⟩
    · -- positivity transfers
      intro i hki hip
      -- `sDiscK P i = a^{even} · sDiscK M.charpoly i`, and `sDiscK M.charpoly i > 0`.
      have hiP : i ≤ p := by omega
      have hsq := sDiscK_smul_eq hMmonic hPeq hp i (by omega)
      -- matrix subdisc → sDiscK M.charpoly
      have hMsub : sDiscK M.charpoly i = sDiscOfMatrix i M :=
        (sDiscOfMatrix_eq_sDiscK_charpoly M i (by omega)).symm
      have hMpos : 0 < sDiscK M.charpoly i := by
        rw [hMsub]; exact hpos i hki (by omega)
      rw [hsq]
      apply mul_pos _ hMpos
      have hexp : 2 * ((P.aroots AC).card - i) - 2 = 2 * ((P.aroots AC).card - i - 1) := by omega
      rw [hexp, pow_mul]
      exact pow_pos (sq_pos_of_ne_zero ha) _
    · -- vanishing transfers
      intro i hik
      have hki : k ≤ p - 1 := by omega
      have hiP : i ≤ p := by omega
      have hsq := sDiscK_smul_eq hMmonic hPeq hp i (by omega)
      have hMsub : sDiscK M.charpoly i = sDiscOfMatrix i M :=
        (sDiscOfMatrix_eq_sDiscK_charpoly M i (by omega)).symm
      have hMzero : sDiscK M.charpoly i = 0 := by rw [hMsub]; exact hzero i hik
      rw [hsq, hMzero, mul_zero]
  · ------------------------------------------------------------------
    -- ⟸ : staircase → Splits
    ------------------------------------------------------------------
    rintro ⟨k, hk, hpos, hzero⟩
    -- (P3) PmV of subdiscriminant sequence = p - k, giving real-root count.
    have hpmv : PmV (sDiscSeq P) = (p : ℤ) - k := by
      set f : ℕ → R := fun j => sDiscK P (P.natDegree - j) with hf
      set m := p - k + 1 with hm
      have hsplit : sDiscSeq P
          = (List.range m).map f ++ (List.range k).map (fun x => f (m + x)) := by
        rw [sDiscSeq, show P.natDegree + 1 = m + k from by omega,
          List.range_add, List.map_append, List.map_map]
        rfl
      rw [hsplit]
      have hposK : ∀ i, k ≤ i → i ≤ p → 0 < sDiscK P i := by
        intro i hki hip
        rcases eq_or_lt_of_le hip with h | h
        · subst h; rw [sDiscK, ite_eq_right (by omega)]; exact one_pos
        · exact hpos i hki (by omega)
      have hposBlock : ∀ x ∈ (List.range m).map f, 0 < x := by
        intro x hx
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        rw [hf]; exact hposK (p - j) (by omega) (by omega)
      have hzeroBlock : ∀ x ∈ (List.range k).map (fun x => f (m + x)), x = 0 := by
        intro x hx
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        rw [hf]; exact hzero (p - (m + j)) (by omega)
      have hne : (List.range m).map f ≠ [] := by
        simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega
      rw [pmv_pos_append_zeros _ _ hne hposBlock hzeroBlock]
      simp only [List.length_map, List.length_range]
      push_cast [hm]; omega
    have hreal : (P.roots.toFinset.card : ℤ) = (p : ℤ) - k := by
      rw [← theorem_4_34 P hp]; exact hpmv
    have hrealN : P.roots.toFinset.card = p - k := by
      have := hreal; omega
    -- (P4) deg gcd(P, P') = k via Proposition 4.26.
    have hP'ne : P.derivative ≠ 0 := fun h => by
      have := Polynomial.derivative_eq_zero.mp h; omega
    have hderdeg_eq : P.derivative.natDegree = p - 1 := by
      have h := Polynomial.degree_derivative (p := P) (by omega)
      exact Polynomial.natDegree_eq_of_degree_eq_some h
    have hsres : ∀ i, i ≤ p →
        (sRes P P.derivative i = 0 ↔ sDiscK P i = 0) := by
      intro i hi
      rw [sRes_eq_leadingCoeff_mul_sDiscK P hderdeg hi, mul_eq_zero]
      simp [ha]
    have hgcd : (gcd P P.derivative).natDegree = k := by
      rw [Proposition_4_26 P P.derivative hPne hP'ne k (by rw [hderdeg_eq]; omega)
        (by omega)]
      refine ⟨?_, ?_⟩
      · intro i hik
        rw [hsres i (by omega)]; exact hzero i hik
      · rw [Ne, hsres k (by omega)]
        exact ne_of_gt (hpos k (le_refl k) (by omega))
    -- (P4 count) distinct complex roots = p - (gcd degree) = p - k.
    have hcplx : (P.aroots AC).toFinset.card = p - k := by
      rw [card_aroots_toFinset_eq P hPne, hgcd]
    -- Combine: real and complex distinct-root counts agree.
    exact splits_of_distinct_counts_eq (C := AC) P hPne (by rw [hrealN, hcplx])

end

end Azurite.BPR.Chapter4
