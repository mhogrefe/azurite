import Azurite.BasuPollackRoy.Chapter2.Lemma_2_48
import Azurite.BasuPollackRoy.Chapter2.Theorem_2_35

/-!
# BPR Theorem 2.47: virtual roots count via sign variation of `Der(P)`

**Theorem 2.47 (BPR).** For a nonzero `P ∈ R[X]` and `a < b` in `R`,

  `v(P; (a, b]) = Var(Der(P); a, b)`.

The equality is a sharpening of the Budan-Fourier theorem (BPR Theorem 2.35),
where the left side counts **virtual** roots (with multiplicity) rather than
actual roots.

## Proof structure

The proof parallels `budan_fourier_finite_aux` but uses `lemma_2_48`
(equality) in place of `lemma_2_36_left` (inequality). Induct on
`(critPointsIoc P a b).card`:

* If it is `0`, `(a, b]` is iterated-derivative-root-free, so both sides are
  `0` (`lemma_2_36_right` for `Var`, and every virtual root is pinned down
  by `lemma_2_48` to have multiplicity `0` in this interval).

* Otherwise let `c = max (critPointsIoc P a b)` and pick `d < c` with
  `[d, c)` iterated-derivative-root-free. Applying `lemma_2_48` gives
  `v(P; (d, c]) = Var(Der P; d, c)`; the induction hypothesis handles
  `(a, d]`; and `(c, b]` contributes `0` on both sides by
  `lemma_2_36_right` and the absence of virtual roots in a
  root-free interval.
-/

namespace Azurite.BPR.Theorem_2_47

open Polynomial Azurite.BPR Azurite.BPR.VirtualRoots
  Azurite.BPR.Theorem2_35 Azurite.BPR.Lemma_2_48

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Definition: `numVirtualRoots` -/

/-- **BPR notation.** `v(P; (a, b])`: the number of virtual roots of `P`
    in the half-open interval `(a, b]`, for finite `a, b`, counted with
    multiplicity. -/
noncomputable def numVirtualRoots (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (a b : R) : ℕ :=
  ((↑(virtualRoots hIVP hP) : Multiset R).filter
    (fun r => a < r ∧ r ≤ b)).card

/-! ### Splitting -/

/-- Additivity over a middle point. -/
lemma numVirtualRoots_split (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) {a c b : R} (hac : a ≤ c) (hcb : c ≤ b) :
    numVirtualRoots hIVP hP a b =
      numVirtualRoots hIVP hP a c + numVirtualRoots hIVP hP c b := by
  classical
  unfold numVirtualRoots
  rw [← Multiset.card_add]
  congr 1
  conv_lhs => rw [← Multiset.filter_add_not (fun r : R => r ≤ c)
    ((↑(virtualRoots hIVP hP) : Multiset R).filter
      (fun r => a < r ∧ r ≤ b))]
  congr 1
  · rw [Multiset.filter_filter]
    congr 1
    funext r
    exact propext
      ⟨fun ⟨h0, h1, _⟩ => ⟨h1, h0⟩,
       fun ⟨h1, h2⟩ => ⟨h2, h1, le_trans h2 hcb⟩⟩
  · rw [Multiset.filter_filter]
    congr 1
    funext r
    simp only [not_le]
    exact propext
      ⟨fun ⟨h0, _, h2⟩ => ⟨h0, h2⟩,
       fun ⟨h0, h2⟩ => ⟨h0, lt_of_le_of_lt hac h0, h2⟩⟩

/-! ### Virtual roots in iter-deriv-root-free regions -/

/-- If `(a, b]` contains no root of any iterated derivative `P^{(k)}`
    (`k ≤ P.natDegree`), then no virtual root of `P` lies in `(a, b]`.

    Proof: for `x ∈ virtualRoots ∩ (a, b]`, pick `d ∈ (a, x)`; Lemma 2.48
    gives `v(P, x) = Var(Der P; d, x)`, and `lemma_2_36_right` on `(d, x]`
    forces `Var(Der P; d, x) = 0`, so `v(P, x) = 0`, contradicting `x`
    being a virtual root. -/
private lemma not_mem_virtualRoots_of_iter_deriv_root_free_Ioc
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0)
    {a b x : R} (hax : a < x) (hxb : x ≤ b)
    (hno : ∀ k ≤ P.natDegree, ∀ y ∈ Set.Ioc a b,
      ((⇑derivative)^[k] P).eval y ≠ 0) :
    x ∉ virtualRoots hIVP hP := by
  intro hmem
  obtain ⟨d, had, hdx⟩ := exists_between hax
  have h_no_Ico : ∀ k, k < P.natDegree → ∀ y ∈ Set.Ico d x,
      ((⇑derivative)^[k] P).eval y ≠ 0 := by
    intro k hk y hy
    refine hno k (le_of_lt hk) y ⟨?_, ?_⟩
    · exact lt_of_lt_of_le had hy.1
    · exact le_of_lt (lt_of_lt_of_le hy.2 hxb)
  have h_no_Ioc : ∀ k ≤ P.natDegree, ∀ y ∈ Set.Ioc d x,
      ((⇑derivative)^[k] P).eval y ≠ 0 := by
    intro k hk y hy
    refine hno k hk y ⟨?_, ?_⟩
    · exact lt_trans had hy.1
    · exact le_trans hy.2 hxb
  have h48 := lemma_2_48 hIVP hP hdx h_no_Ico
  have h36 := lemma_2_36_right hIVP P hP hdx h_no_Ioc
  rw [h36] at h48
  have hmult_zero : virtualMultiplicity hIVP hP x = 0 := by exact_mod_cast h48
  have hpos : 0 < virtualMultiplicity hIVP hP x := by
    unfold virtualMultiplicity
    exact List.count_pos_iff.mpr hmem
  omega

/-- If `(a, b)` (open) contains no root of any iterated derivative, no virtual
    root of `P` lies in the open interval `(a, b)`. Derived from the
    `Ioc` version by shrinking. -/
private lemma not_mem_virtualRoots_of_iter_deriv_root_free_Ioo
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0)
    {a b x : R} (hax : a < x) (hxb : x < b)
    (hno : ∀ k ≤ P.natDegree, ∀ y ∈ Set.Ioo a b,
      ((⇑derivative)^[k] P).eval y ≠ 0) :
    x ∉ virtualRoots hIVP hP := by
  obtain ⟨b', hxb', hb'b⟩ := exists_between hxb
  have hax' : a < b' := lt_trans hax hxb'
  have hno' : ∀ k ≤ P.natDegree, ∀ y ∈ Set.Ioc a b',
      ((⇑derivative)^[k] P).eval y ≠ 0 := by
    intro k hk y hy
    exact hno k hk y ⟨hy.1, lt_of_le_of_lt hy.2 hb'b⟩
  exact not_mem_virtualRoots_of_iter_deriv_root_free_Ioc
    hIVP hP hax (le_of_lt hxb') hno'

/-! ### Evaluation on root-free blocks -/

/-- If `(a, b]` has no iterated derivative root, `numVirtualRoots` vanishes. -/
lemma numVirtualRoots_eq_zero_of_no_iter_deriv_root_Ioc
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0)
    {a b : R}
    (hno : ∀ k ≤ P.natDegree, ∀ y ∈ Set.Ioc a b,
      ((⇑derivative)^[k] P).eval y ≠ 0) :
    numVirtualRoots hIVP hP a b = 0 := by
  classical
  unfold numVirtualRoots
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr ⟨har, hrb⟩
  exact not_mem_virtualRoots_of_iter_deriv_root_free_Ioc
    hIVP hP har hrb hno (Multiset.mem_coe.mp hr)

/-- If `(d, c)` is iterated-derivative-root-free, then
    `numVirtualRoots (d, c] = virtualMultiplicity c`. -/
lemma numVirtualRoots_eq_virtualMultiplicity_of_no_iter_deriv_root_Ioo
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0)
    {d c : R} (hdc : d < c)
    (hno : ∀ k ≤ P.natDegree, ∀ y ∈ Set.Ioo d c,
      ((⇑derivative)^[k] P).eval y ≠ 0) :
    numVirtualRoots hIVP hP d c = virtualMultiplicity hIVP hP c := by
  classical
  unfold numVirtualRoots virtualMultiplicity
  have hrw :
      ((↑(virtualRoots hIVP hP) : Multiset R).filter
          (fun r => d < r ∧ r ≤ c)) =
        ((↑(virtualRoots hIVP hP) : Multiset R).filter (fun r => r = c)) := by
    apply Multiset.filter_congr
    intro r hrmem
    constructor
    · rintro ⟨hdr, hrc⟩
      rcases lt_or_eq_of_le hrc with hrc' | heq
      · exfalso
        exact not_mem_virtualRoots_of_iter_deriv_root_free_Ioo
          hIVP hP hdr hrc' hno (Multiset.mem_coe.mp hrmem)
      · exact heq
    · rintro rfl
      exact ⟨hdc, le_refl _⟩
  rw [hrw, Multiset.filter_eq', Multiset.card_replicate]
  exact Multiset.coe_count c (virtualRoots hIVP hP)

/-! ### Main theorem -/

private theorem theorem_2_47_aux
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) :
    ∀ (N : ℕ) {a b : R}, a < b → (critPointsIoc P a b).card ≤ N →
      (numVirtualRoots hIVP hP a b : ℤ) =
        varBetween (der P) (.finite a) (.finite b) := by
  intro N
  induction N with
  | zero =>
    intro a b hab hle
    rw [Nat.le_zero, Finset.card_eq_zero] at hle
    have hnoIoc := no_iter_deriv_root_of_critPointsIoc_empty hP hle
    have hvar : varBetween (der P) (.finite a) (.finite b) = 0 :=
      lemma_2_36_right hIVP P hP hab hnoIoc
    have hnum : numVirtualRoots hIVP hP a b = 0 :=
      numVirtualRoots_eq_zero_of_no_iter_deriv_root_Ioc hIVP hP hnoIoc
    rw [hvar, hnum]; rfl
  | succ N ih =>
    intro a b hab hle
    by_cases hcard_zero : (critPointsIoc P a b).card = 0
    · rw [Finset.card_eq_zero] at hcard_zero
      have hnoIoc := no_iter_deriv_root_of_critPointsIoc_empty hP hcard_zero
      have hvar : varBetween (der P) (.finite a) (.finite b) = 0 :=
        lemma_2_36_right hIVP P hP hab hnoIoc
      have hnum : numVirtualRoots hIVP hP a b = 0 :=
        numVirtualRoots_eq_zero_of_no_iter_deriv_root_Ioc hIVP hP hnoIoc
      rw [hvar, hnum]; rfl
    have hne : (critPointsIoc P a b).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_zero)
    set c := (critPointsIoc P a b).max' hne with hc_def
    have hc_mem : c ∈ critPointsIoc P a b := Finset.max'_mem _ _
    have hc_max : ∀ r ∈ critPointsIoc P a b, r ≤ c :=
      fun r hr => Finset.le_max' _ r hr
    have hac : a < c ∧ c ≤ b := ((mem_critPointsIoc_iff hP).mp hc_mem).1
    have hnoCb : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc c b,
        ((⇑derivative)^[k] P).eval x ≠ 0 :=
      no_iter_deriv_root_Ioc_of_max_critPointsIoc hP hc_mem hc_max
    set S' := (critPointsIoc P a b).erase c with hS'_def
    have ⟨e, hae, hec, heS⟩ : ∃ e : R, a ≤ e ∧ e < c ∧
        ∀ r ∈ critPointsIoc P a b, r ≠ c → r ≤ e := by
      by_cases hS'ne : S'.Nonempty
      · refine ⟨S'.max' hS'ne, ?_, ?_, ?_⟩
        · have hmem_S' : S'.max' hS'ne ∈ S' := Finset.max'_mem _ _
          have : S'.max' hS'ne ∈ critPointsIoc P a b :=
            Finset.mem_of_mem_erase hmem_S'
          exact le_of_lt ((mem_critPointsIoc_iff hP).mp this).1.1
        · have hmem_S' : S'.max' hS'ne ∈ S' := Finset.max'_mem _ _
          have hne_c : S'.max' hS'ne ≠ c := (Finset.mem_erase.mp hmem_S').1
          have hmem : S'.max' hS'ne ∈ critPointsIoc P a b :=
            Finset.mem_of_mem_erase hmem_S'
          exact lt_of_le_of_ne (hc_max _ hmem) hne_c
        · intro r hr hrc
          exact Finset.le_max' _ _ (Finset.mem_erase.mpr ⟨hrc, hr⟩)
      · refine ⟨a, le_refl _, hac.1, ?_⟩
        intro r hr hrc
        exfalso
        exact hS'ne ⟨r, Finset.mem_erase.mpr ⟨hrc, hr⟩⟩
    obtain ⟨d₀, hd₀c, hd₀⟩ := exists_no_root_Ioo_left_forall_der hP c
    obtain ⟨d, hed, hdc⟩ : ∃ d, max e d₀ < d ∧ d < c :=
      exists_between (max_lt hec hd₀c)
    have hed' : e < d := lt_of_le_of_lt (le_max_left _ _) hed
    have hd₀d : d₀ < d := lt_of_le_of_lt (le_max_right _ _) hed
    have had : a < d := lt_of_le_of_lt hae hed'
    have hdb : d ≤ b := le_trans (le_of_lt hdc) hac.2
    have hnoDc : ∀ k, k < P.natDegree → ∀ x ∈ Set.Ico d c,
        ((⇑derivative)^[k] P).eval x ≠ 0 := by
      intro k hk x hx
      exact hd₀ x ⟨lt_of_lt_of_le hd₀d hx.1, hx.2⟩ k (le_of_lt hk)
    have hnoDc' : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioo d c,
        ((⇑derivative)^[k] P).eval x ≠ 0 := by
      intro k hk x hx
      exact hd₀ x ⟨lt_trans hd₀d hx.1, hx.2⟩ k hk
    have hcard_ad : (critPointsIoc P a d).card < (critPointsIoc P a b).card :=
      critPointsIoc_card_lt_of_lt_max hP hac.2 hdc hc_mem
    have hcard_ad_le : (critPointsIoc P a d).card ≤ N :=
      Nat.le_of_lt_succ (lt_of_lt_of_le hcard_ad hle)
    have h_ad := ih had hcard_ad_le
    have h_dc : (numVirtualRoots hIVP hP d c : ℤ) =
        varBetween (der P) (.finite d) (.finite c) := by
      rw [numVirtualRoots_eq_virtualMultiplicity_of_no_iter_deriv_root_Ioo
        hIVP hP hdc hnoDc']
      exact lemma_2_48 hIVP hP hdc hnoDc
    have hsplit_num : numVirtualRoots hIVP hP a b =
        numVirtualRoots hIVP hP a d +
        numVirtualRoots hIVP hP d c +
        numVirtualRoots hIVP hP c b := by
      rw [numVirtualRoots_split hIVP hP (le_of_lt had) hdb,
          numVirtualRoots_split hIVP hP (le_of_lt hdc) hac.2, ← add_assoc]
    have hsplit_var : varBetween (der P) (.finite a) (.finite b) =
        varBetween (der P) (.finite a) (.finite d) +
        varBetween (der P) (.finite d) (.finite c) +
        varBetween (der P) (.finite c) (.finite b) := by
      rw [← varBetween_split (der P) (.finite a) (.finite c) (.finite b),
          ← varBetween_split (der P) (.finite a) (.finite d) (.finite c)]
    rcases lt_or_eq_of_le hac.2 with hcb | hcb
    · have h_cb_var : varBetween (der P) (.finite c) (.finite b) = 0 :=
        lemma_2_36_right hIVP P hP hcb hnoCb
      have h_cb_num : numVirtualRoots hIVP hP c b = 0 :=
        numVirtualRoots_eq_zero_of_no_iter_deriv_root_Ioc hIVP hP hnoCb
      rw [hsplit_num, hsplit_var, h_cb_var, h_cb_num]
      push_cast
      linarith [h_ad, h_dc]
    · have h_cb_var : varBetween (der P) (.finite c) (.finite b) = 0 := by
        rw [hcb]; unfold varBetween; ring
      have h_cb_num : numVirtualRoots hIVP hP c b = 0 := by
        classical
        unfold numVirtualRoots
        rw [hcb, Multiset.card_eq_zero, Multiset.filter_eq_nil]
        rintro r _ ⟨h1, h2⟩
        exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
      rw [hsplit_num, hsplit_var, h_cb_var, h_cb_num]
      push_cast
      linarith [h_ad, h_dc]

/-- **BPR Theorem 2.47 (finite-endpoint case).** For any nonzero `P ∈ R[X]`
    and `a < b`, the number of virtual roots of `P` in `(a, b]` (with
    multiplicity) equals the sign variation of `Der(P)` between `a` and `b`. -/
theorem theorem_2_47_finite (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) {a b : R} (hab : a < b) :
    (numVirtualRoots hIVP hP a b : ℤ) =
      varBetween (der P) (.finite a) (.finite b) :=
  theorem_2_47_aux hIVP hP _ hab (le_refl _)

end Azurite.BPR.Theorem_2_47
