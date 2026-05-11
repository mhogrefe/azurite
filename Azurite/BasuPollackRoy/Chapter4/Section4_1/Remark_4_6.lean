import Azurite.BasuPollackRoy.Chapter4.Section4_1.Subdiscriminant
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Remark_4_4

/-!
# BPR Remark 4.6: vanishing pattern of subdiscriminants

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

When all roots of `P : R[X]` lie in the linearly ordered field `R`, the
subdiscriminants vanish in the pattern

  `sDisc_0(P) = ... = sDisc_{j-1}(P) = 0  and  sDisc_j(P) ≠ 0`

iff `P` has exactly `p - j` distinct roots in `R`. BPR notes that the
hypothesis can be dropped later; we formalise the Remark 4.6 version here.

The argument runs on the R-side: define `sDiscR P j : R` by the same
multiset formula as `sDisc P j`, but on `P.roots : Multiset R`. Each
summand `(-1)^{k(k-1)/2} · ∏(off-diag)` over a `k`-sub-multiset is a
Vandermonde square — non-negative, and positive exactly when the
sub-multiset is `Nodup`. Hence `sDiscR P j ≠ 0` iff some `Nodup`
`k`-sub-multiset exists, iff `k ≤ |P.roots.toFinset|`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

section sDiscR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

open Classical in
/-- R-side subdiscriminant: the analog of `sDisc P j` computed on
    `P.roots : Multiset R` rather than `P.aroots C`. -/
noncomputable def sDiscR (P : R[X]) (j : ℕ) : R :=
  (-1 : R) ^ ((P.roots.card - j) * (P.roots.card - j - 1) / 2) *
    ((P.roots.powersetCard (P.roots.card - j)).map (fun t =>
      ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod)).sum

omit [IsStrictOrderedRing R] in
/-- For any multiset `t` over a field, the off-diagonal product
    `∏_{(a, b) ∈ (t ×ˢ t) \ Δ}(a − b)` vanishes iff `t` has a duplicate. -/
lemma offdiag_prod_eq_zero_iff_not_nodup (t : Multiset R) :
    ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod = 0
      ↔ ¬ t.Nodup := by
  classical
  rw [Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, heq⟩
    simp only at heq
    rw [sub_eq_zero] at heq
    subst heq
    rw [← Multiset.one_le_count_iff_mem, Multiset.count_sub,
        count_product_eq, count_diag_map] at hmem
    rw [Multiset.nodup_iff_count_le_one]
    push Not
    refine ⟨a, ?_⟩
    by_contra h
    push Not at h
    interval_cases (t.count a) <;> omega
  · intro hnotdup
    rw [Multiset.nodup_iff_count_le_one] at hnotdup
    push Not at hnotdup
    obtain ⟨a, ha⟩ := hnotdup
    refine ⟨(a, a), ?_, by simp⟩
    rw [← Multiset.one_le_count_iff_mem, Multiset.count_sub,
        count_product_eq, count_diag_map]
    have hge : 2 ≤ t.count a := ha
    have : 2 * t.count a ≤ t.count a * t.count a := Nat.mul_le_mul_right _ hge
    omega

/-- The signed off-diagonal product is non-negative. -/
lemma sign_smul_offdiag_prod_nonneg (t : Multiset R) :
    0 ≤ (-1 : R) ^ (t.card * (t.card - 1) / 2) *
      ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod := by
  classical
  by_cases ht : t.Nodup
  · rw [discR_aux_eq_sq t ht]
    exact sq_nonneg _
  · rw [(offdiag_prod_eq_zero_iff_not_nodup t).mpr ht, mul_zero]

/-- The signed off-diagonal product is positive when `t` is `Nodup`. -/
lemma sign_smul_offdiag_prod_pos_of_nodup (t : Multiset R) (ht : t.Nodup) :
    0 < (-1 : R) ^ (t.card * (t.card - 1) / 2) *
      ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod := by
  classical
  rw [discR_aux_eq_sq t ht]
  exact sq_pos_of_ne_zero (filter_gt_prod_ne_zero t ht)

omit [IsStrictOrderedRing R] in
/-- The signed off-diagonal product is zero when `t` is not `Nodup`. -/
lemma sign_smul_offdiag_prod_eq_zero_of_not_nodup (t : Multiset R) (ht : ¬ t.Nodup) :
    (-1 : R) ^ (t.card * (t.card - 1) / 2) *
      ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod = 0 := by
  classical
  rw [(offdiag_prod_eq_zero_iff_not_nodup t).mpr ht, mul_zero]

omit [Field R] [IsStrictOrderedRing R] in
/-- A `Nodup` `k`-sub-multiset of `s` exists iff `k ≤ s.toFinset.card`. -/
lemma exists_nodup_mem_powersetCard_iff (s : Multiset R) (k : ℕ) :
    (∃ t ∈ s.powersetCard k, t.Nodup) ↔ k ≤ s.toFinset.card := by
  classical
  refine ⟨?_, ?_⟩
  · rintro ⟨t, hmem, hnodup⟩
    rw [Multiset.mem_powersetCard] at hmem
    obtain ⟨hle, hcard⟩ := hmem
    have h1 : t.toFinset.card = t.card := Multiset.toFinset_card_of_nodup hnodup
    have h2 : t.toFinset ⊆ s.toFinset :=
      Multiset.toFinset_subset.mpr (Multiset.subset_of_le hle)
    calc k = t.card := hcard.symm
      _ = t.toFinset.card := h1.symm
      _ ≤ s.toFinset.card := Finset.card_le_card h2
  · intro hk
    obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hk
    refine ⟨I.val, ?_, I.nodup⟩
    rw [Multiset.mem_powersetCard]
    refine ⟨?_, hIcard⟩
    rw [Multiset.le_iff_subset I.nodup]
    intro a ha
    have h_in_finset : a ∈ s.toFinset := hIsub ha
    rwa [Multiset.mem_toFinset] at h_in_finset

omit [IsStrictOrderedRing R] in
/-- The off-diagonal sum, with the sign factor pulled in, expresses
    `sDiscR P j` as a sum of non-negative terms (one per `k`-sub-multiset). -/
lemma sDiscR_eq_sum_signed (P : R[X]) (j : ℕ) :
    sDiscR P j =
      ((P.roots.powersetCard (P.roots.card - j)).map (fun t : Multiset R =>
        (-1 : R) ^ (t.card * (t.card - 1) / 2) *
        ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod)).sum := by
  classical
  unfold sDiscR
  set k := P.roots.card - j
  rw [← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  rw [Multiset.mem_powersetCard] at ht
  rw [ht.2]

/-- **Main R-side characterisation**: `sDiscR P j ≠ 0` iff `P` has at least
    `P.roots.card − j` distinct roots in `R`. -/
theorem sDiscR_ne_zero_iff (P : R[X]) (j : ℕ) :
    sDiscR P j ≠ 0 ↔ P.roots.card - j ≤ P.roots.toFinset.card := by
  classical
  set s := P.roots
  set k := s.card - j
  -- Rewrite `sDiscR P j` as a sum of non-negative terms.
  rw [sDiscR_eq_sum_signed]
  set m : Multiset R := ((s.powersetCard k).map (fun t : Multiset R =>
        (-1 : R) ^ (t.card * (t.card - 1) / 2) *
        ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod))
  have hnn : ∀ x ∈ m, 0 ≤ x := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Multiset.mem_map.mp hx
    exact sign_smul_offdiag_prod_nonneg t
  -- m.sum = 0 ↔ all elements zero (using nonneg + ordered structure).
  have hsum_iff : m.sum = 0 ↔ ∀ x ∈ m, x = 0 := by
    refine ⟨?_, Multiset.sum_eq_zero⟩
    intro hsum x hx
    exact Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hnn hsum x hx
  rw [show m.sum ≠ 0 ↔ ¬ m.sum = 0 from Iff.rfl, hsum_iff]
  push Not
  -- ∃ x ∈ m, x ≠ 0 ↔ ∃ t ∈ s.powersetCard k, sign · offdiag t ≠ 0
  --                ↔ ∃ t ∈ s.powersetCard k, t.Nodup
  --                ↔ k ≤ s.toFinset.card
  rw [show (∃ x ∈ m, x ≠ 0) ↔ ∃ t ∈ s.powersetCard k, t.Nodup from ?_,
      exists_nodup_mem_powersetCard_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, hxne⟩
    obtain ⟨t, htm, rfl⟩ := Multiset.mem_map.mp hx
    refine ⟨t, htm, ?_⟩
    by_contra hnotnodup
    exact hxne (sign_smul_offdiag_prod_eq_zero_of_not_nodup t hnotnodup)
  · rintro ⟨t, htm, hnodup⟩
    refine ⟨_, Multiset.mem_map.mpr ⟨t, htm, rfl⟩, ?_⟩
    exact ne_of_gt (sign_smul_offdiag_prod_pos_of_nodup t hnodup)

/-- **BPR Remark 4.6** (R-side form): `sDiscR_0(P) = ... = sDiscR_{j-1}(P) =
    0` and `sDiscR_j(P) ≠ 0` iff `P` has exactly `P.roots.card − j` distinct
    roots in `R`. -/
theorem sDiscR_first_nonzero_iff (P : R[X]) (j : ℕ) (hj : j ≤ P.roots.card) :
    ((∀ i < j, sDiscR P i = 0) ∧ sDiscR P j ≠ 0)
      ↔ P.roots.toFinset.card = P.roots.card - j := by
  set s := P.roots
  set p := s.card
  have hcard_le : s.toFinset.card ≤ p := by
    classical
    exact Multiset.toFinset_card_le s
  constructor
  · rintro ⟨hall, hne⟩
    have hge : p - j ≤ s.toFinset.card := (sDiscR_ne_zero_iff P j).mp hne
    -- Show s.toFinset.card ≤ p - j: contrapositive of hall.
    have hle : s.toFinset.card ≤ p - j := by
      by_contra hlt
      push Not at hlt
      -- hlt : p - j < s.toFinset.card
      -- Find i < j with sDiscR P i ≠ 0.
      have hexists : ∃ i, i < j ∧ p - i ≤ s.toFinset.card := by
        refine ⟨p - s.toFinset.card, ?_, ?_⟩
        · -- p - s.toFinset.card < j: from hlt, s.toFinset.card > p - j, so
          -- p - s.toFinset.card < p - (p - j) = j (since p - j ≤ p).
          omega
        · -- p - (p - s.toFinset.card) = s.toFinset.card ≤ s.toFinset.card
          omega
      obtain ⟨i, hij, hi⟩ := hexists
      have : sDiscR P i ≠ 0 := (sDiscR_ne_zero_iff P i).mpr hi
      exact this (hall i hij)
    omega
  · intro hcard
    refine ⟨?_, ?_⟩
    · intro i hij
      by_contra hne
      have hge : p - i ≤ s.toFinset.card := (sDiscR_ne_zero_iff P i).mp hne
      omega
    · exact (sDiscR_ne_zero_iff P j).mpr hcard.ge

end sDiscR

end Azurite.BPR.Chapter4
