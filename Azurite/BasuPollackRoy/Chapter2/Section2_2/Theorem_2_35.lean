import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_36

/-!
# BPR Theorem 2.35: Budan-Fourier Theorem

For `P ∈ R[X]` of degree `p` over a real closed field `R`, and `a, b ∈ R ∪ {−∞, +∞}`:

  1. `Var(Der(P); a, b) ≥ num(P; (a, b])`
  2. `Var(Der(P); a, b) − num(P; (a, b])` is even.

Theorem 2.33 (Descartes' rule of signs) is a particular case, obtained at
`(0, +∞)` via the identity `Var(P) = Var(Der(P); 0, +∞)`.

The key technical input — BPR Lemma 2.36, plus its one-sided variants
`lemma_2_36_left` and `lemma_2_36_right` — is in
`Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_36`.
-/

namespace Azurite.BPR.Theorem2_35

open Polynomial Azurite.BPR Azurite.BPR.Proposition2_20 Azurite.BPR.Proposition2_21

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Critical points of `P` in a half-open interval -/

open Classical in
/-- The finite set of critical points of `P` in `(a, b]`: points `r ∈ (a, b]`
    at which some iterated derivative `P^{(k)}` (`k ≤ P.natDegree`) vanishes.
    For `P ≠ 0`, this captures the essential structure BPR uses to subdivide
    `(a, b]` in the proof of Theorem 2.35. -/
noncomputable def critPointsIoc (P : R[X]) (a b : R) : Finset R :=
  (Finset.range (P.natDegree + 1)).biUnion fun k =>
    (((⇑derivative)^[k] P).roots.toFinset).filter (fun r => a < r ∧ r ≤ b)

/-- Membership characterization: `r ∈ critPointsIoc P a b` iff `r ∈ (a, b]`
    and some `P^{(k)}` vanishes at `r`. -/
lemma mem_critPointsIoc_iff {P : R[X]} (hP : P ≠ 0) {r a b : R} :
    r ∈ critPointsIoc P a b ↔
    (a < r ∧ r ≤ b) ∧
      ∃ k ≤ P.natDegree, ((⇑derivative)^[k] P).eval r = 0 := by
  classical
  simp only [critPointsIoc, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_range, Multiset.mem_toFinset]
  constructor
  · rintro ⟨k, hk, hr_roots, hab⟩
    have hne := iterate_derivative_ne_zero_of_le_natDegree hP
      (Nat.lt_succ_iff.mp hk)
    rw [Polynomial.mem_roots hne] at hr_roots
    exact ⟨hab, k, Nat.lt_succ_iff.mp hk, hr_roots⟩
  · rintro ⟨hab, k, hk, hr⟩
    have hne := iterate_derivative_ne_zero_of_le_natDegree hP hk
    refine ⟨k, Nat.lt_succ_iff.mpr hk, ?_, hab⟩
    rw [Polynomial.mem_roots hne]
    exact hr

/-! ### Splitting `numRoots` and `varBetween` at an intermediate point -/

omit [IsStrictOrderedRing R] in
/-- Reduced form of `numRoots` at two finite endpoints: direct filter card. -/
lemma numRoots_finite_finite (P : R[X]) (a b : R) :
    numRoots P (.finite a) (.finite b) =
      (P.roots.filter (fun r => a < r ∧ r ≤ b)).card := rfl

omit [IsStrictOrderedRing R] in
/-- Additivity of `varBetween` over a middle point: the trivial consequence of
    `varBetween = varAt a - varAt b`. -/
lemma varBetween_split (P : List R[X]) (a c b : ExtendedPoint R) :
    varBetween P a c + varBetween P c b = varBetween P a b := by
  unfold varBetween; ring

omit [IsStrictOrderedRing R] in
/-- Additivity of `numRoots` over a middle point `c ∈ [a, b]`. Uses the
    partition of the half-open interval `(a, b]` into `(a, c] ⊔ (c, b]`. -/
lemma numRoots_split (P : R[X]) {a c b : R} (hac : a ≤ c) (hcb : c ≤ b) :
    numRoots P (.finite a) (.finite b) =
      numRoots P (.finite a) (.finite c) +
      numRoots P (.finite c) (.finite b) := by
  classical
  simp only [numRoots_finite_finite]
  rw [← Multiset.card_add]
  congr 1
  conv_lhs => rw [← Multiset.filter_add_not (fun r : R => r ≤ c)
    (P.roots.filter (fun r => a < r ∧ r ≤ b))]
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

omit [IsStrictOrderedRing R] in
/-- When `(d, c)` has no root of `P` and `d < c`, `numRoots P (d, c]` is just
    the multiplicity of `c` as a root (0 if `c` is not a root). -/
lemma numRoots_Ioc_of_no_root {P : R[X]} (hP : P ≠ 0) {d c : R} (hdc : d < c)
    (hno : ∀ x ∈ Set.Ioo d c, P.eval x ≠ 0) :
    numRoots P (.finite d) (.finite c) = P.rootMultiplicity c := by
  classical
  simp only [numRoots_finite_finite]
  have hmult : P.rootMultiplicity c = P.roots.count c :=
    (Polynomial.count_roots P).symm
  rw [hmult]
  have hfilter : P.roots.filter (fun r => d < r ∧ r ≤ c) =
      P.roots.filter (fun r => r = c) := by
    apply Multiset.filter_congr
    intro r hr
    constructor
    · rintro ⟨hd_lt, hr_le⟩
      rcases lt_or_eq_of_le hr_le with hlt | heq
      · exfalso
        have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
        exact hno r ⟨hd_lt, hlt⟩ hPr
      · exact heq
    · rintro rfl
      exact ⟨hdc, le_refl r⟩
  rw [hfilter, Multiset.filter_eq', Multiset.card_replicate]

/-- Absent all `P^{(k)}` roots in `(c, b]`, the right-side half `varBetween
    (der P); c, b` vanishes and `numRoots P (c, b] = 0`. Used for the
    rightmost piece in Budan-Fourier. -/
lemma varBetween_and_numRoots_eq_zero_of_no_root_Ioc
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0)
    {c b : R} (hcb : c < b)
    (hno : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc c b,
      ((⇑derivative)^[k] P).eval x ≠ 0) :
    varBetween (der P) (.finite c) (.finite b) = 0 ∧
    numRoots P (.finite c) (.finite b) = 0 := by
  refine ⟨lemma_2_36_right hIVP P hP hcb hno, ?_⟩
  classical
  simp only [numRoots_finite_finite]
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro r hr ⟨hcr, hrb⟩
  have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
  have hne := hno 0 (Nat.zero_le _) r ⟨hcr, hrb⟩
  simp at hne
  exact hne hPr

/-! ### Membership structure: `critPointsIoc` restricted to sub-intervals -/

omit [IsStrictOrderedRing R] in
/-- If the larger interval has empty `critPointsIoc`, so does the smaller. -/
lemma critPointsIoc_subset_of_Ioc_subset
    {P : R[X]} {a b a' b' : R} (ha : a ≤ a') (hb : b' ≤ b) :
    critPointsIoc P a' b' ⊆ critPointsIoc P a b := by
  classical
  intro r hr
  simp only [critPointsIoc, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_range] at hr ⊢
  obtain ⟨k, hk, hrk, hab'⟩ := hr
  exact ⟨k, hk, hrk, ⟨lt_of_le_of_lt ha hab'.1, le_trans hab'.2 hb⟩⟩

/-- If `critPointsIoc P a b = ∅` then no iterated derivative has a root in
    `(a, b]`. Used for the base case of Budan-Fourier. -/
lemma no_iter_deriv_root_of_critPointsIoc_empty
    {P : R[X]} (hP : P ≠ 0) {a b : R}
    (h : critPointsIoc P a b = ∅) :
    ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc a b, ((⇑derivative)^[k] P).eval x ≠ 0 := by
  intro k hk x hx hzero
  have hmem : x ∈ critPointsIoc P a b := (mem_critPointsIoc_iff hP).mpr
    ⟨⟨hx.1, hx.2⟩, k, hk, hzero⟩
  rw [h] at hmem
  exact Finset.notMem_empty _ hmem

/-- If `c = max (critPointsIoc P a b)`, then `(c, b]` contains no iterated
    derivative root. -/
lemma no_iter_deriv_root_Ioc_of_max_critPointsIoc
    {P : R[X]} (hP : P ≠ 0) {a b c : R}
    (hc : c ∈ critPointsIoc P a b)
    (hmax : ∀ r ∈ critPointsIoc P a b, r ≤ c) :
    ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc c b, ((⇑derivative)^[k] P).eval x ≠ 0 := by
  have hac : a < c ∧ c ≤ b := ((mem_critPointsIoc_iff hP).mp hc).1
  intro k hk x hx hzero
  have hmem : x ∈ critPointsIoc P a b := (mem_critPointsIoc_iff hP).mpr
    ⟨⟨lt_trans hac.1 hx.1, hx.2⟩, k, hk, hzero⟩
  exact absurd hx.1 (not_lt.mpr (hmax x hmem))

/-- Strict card decrease: if `c ∈ critPointsIoc P a b` and `d < c`, then
    `critPointsIoc P a d` has strictly fewer elements. -/
lemma critPointsIoc_card_lt_of_lt_max
    {P : R[X]} (hP : P ≠ 0) {a b d c : R} (hcb : c ≤ b) (hdc : d < c)
    (hc : c ∈ critPointsIoc P a b) :
    (critPointsIoc P a d).card < (critPointsIoc P a b).card := by
  apply Finset.card_lt_card
  refine ⟨critPointsIoc_subset_of_Ioc_subset (le_refl a) (le_trans (le_of_lt hdc) hcb), ?_⟩
  intro hsub
  have hcd : c ∈ critPointsIoc P a d := hsub hc
  have : c ≤ d := ((mem_critPointsIoc_iff hP).mp hcd).1.2
  exact absurd hdc (not_lt.mpr this)

/-! ### Main Budan-Fourier theorem (finite-endpoint case) -/

private theorem budan_fourier_finite_aux
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) :
    ∀ (N : ℕ) {a b : R}, a < b → (critPointsIoc P a b).card ≤ N →
      ((numRoots P (.finite a) (.finite b) : ℤ) ≤
        varBetween (der P) (.finite a) (.finite b)) ∧
      Even (varBetween (der P) (.finite a) (.finite b) -
        (numRoots P (.finite a) (.finite b) : ℤ)) := by
  intro N
  induction N with
  | zero =>
    intro a b hab hle
    rw [Nat.le_zero, Finset.card_eq_zero] at hle
    obtain ⟨hvar, hnum⟩ := varBetween_and_numRoots_eq_zero_of_no_root_Ioc
      hIVP hP hab (no_iter_deriv_root_of_critPointsIoc_empty hP hle)
    refine ⟨?_, ?_⟩
    · rw [hvar, hnum]; simp
    · rw [hvar, hnum]; simp
  | succ N ih =>
    intro a b hab hle
    by_cases hcard_zero : (critPointsIoc P a b).card = 0
    · rw [Finset.card_eq_zero] at hcard_zero
      obtain ⟨hvar, hnum⟩ := varBetween_and_numRoots_eq_zero_of_no_root_Ioc
        hIVP hP hab (no_iter_deriv_root_of_critPointsIoc_empty hP hcard_zero)
      refine ⟨?_, ?_⟩
      · rw [hvar, hnum]; simp
      · rw [hvar, hnum]; simp
    -- Nonempty case: pick c = max of critPointsIoc
    have hne : (critPointsIoc P a b).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_zero)
    set c := (critPointsIoc P a b).max' hne with hc_def
    have hc_mem : c ∈ critPointsIoc P a b := Finset.max'_mem _ _
    have hc_max : ∀ r ∈ critPointsIoc P a b, r ≤ c :=
      fun r hr => Finset.le_max' _ r hr
    have hac : a < c ∧ c ≤ b := ((mem_critPointsIoc_iff hP).mp hc_mem).1
    -- (c, b] has no iter. deriv. root
    have hnoCb : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc c b,
        ((⇑derivative)^[k] P).eval x ≠ 0 :=
      no_iter_deriv_root_Ioc_of_max_critPointsIoc hP hc_mem hc_max
    -- Find e: upper bound for non-c critical points
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
    -- Get buffer from exists_no_root_Ioo_left_forall_der
    obtain ⟨d₀, hd₀c, hd₀⟩ := exists_no_root_Ioo_left_forall_der hP c
    -- Pick d ∈ (max e d₀, c)
    obtain ⟨d, hed, hdc⟩ : ∃ d, max e d₀ < d ∧ d < c :=
      exists_between (max_lt hec hd₀c)
    have hed' : e < d := lt_of_le_of_lt (le_max_left _ _) hed
    have hd₀d : d₀ < d := lt_of_le_of_lt (le_max_right _ _) hed
    have had : a < d := lt_of_le_of_lt hae hed'
    have hdb : d ≤ b := le_trans (le_of_lt hdc) hac.2
    -- [d, c) root-free for all iter. derivs
    have hnoDc : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ico d c,
        ((⇑derivative)^[k] P).eval x ≠ 0 := by
      intro k hk x hx
      exact hd₀ x ⟨lt_of_lt_of_le hd₀d hx.1, hx.2⟩ k hk
    -- (d, c) root-free for P (special case k = 0)
    have hnoDc_P : ∀ x ∈ Set.Ioo d c, P.eval x ≠ 0 := by
      intro x hx hzero
      have := hnoDc 0 (Nat.zero_le _) x ⟨le_of_lt hx.1, hx.2⟩
      simp at this
      exact this hzero
    -- critPointsIoc P a d has smaller card
    have hcard_ad : (critPointsIoc P a d).card < (critPointsIoc P a b).card :=
      critPointsIoc_card_lt_of_lt_max hP hac.2 hdc hc_mem
    have hcard_ad_le : (critPointsIoc P a d).card ≤ N :=
      Nat.le_of_lt_succ (lt_of_lt_of_le hcard_ad hle)
    -- Apply IH to (a, d]
    obtain ⟨h_ad_ineq, h_ad_even⟩ := ih had hcard_ad_le
    -- Apply lemma_2_36_left at c
    obtain ⟨h_dc_ineq, h_dc_even⟩ := lemma_2_36_left hIVP P hP hdc hnoDc
    -- numRoots P (d, c] = rootMultiplicity c P
    have h_numDc : numRoots P (.finite d) (.finite c) = P.rootMultiplicity c :=
      numRoots_Ioc_of_no_root hP hdc hnoDc_P
    -- Split (a, b] at c and then at d
    have hsplit_num : numRoots P (.finite a) (.finite b) =
        numRoots P (.finite a) (.finite d) +
        numRoots P (.finite d) (.finite c) +
        numRoots P (.finite c) (.finite b) := by
      rw [numRoots_split P (le_of_lt had) hdb,
          numRoots_split P (le_of_lt hdc) hac.2, ← add_assoc]
    have hsplit_var : varBetween (der P) (.finite a) (.finite b) =
        varBetween (der P) (.finite a) (.finite d) +
        varBetween (der P) (.finite d) (.finite c) +
        varBetween (der P) (.finite c) (.finite b) := by
      rw [← varBetween_split (der P) (.finite a) (.finite c) (.finite b),
          ← varBetween_split (der P) (.finite a) (.finite d) (.finite c)]
    -- Case on c = b vs c < b to handle (c, b]
    rcases lt_or_eq_of_le hac.2 with hcb | hcb
    · -- c < b: use varBetween_and_numRoots_eq_zero_of_no_root_Ioc
      obtain ⟨h_cb_var, h_cb_num⟩ :=
        varBetween_and_numRoots_eq_zero_of_no_root_Ioc hIVP hP hcb hnoCb
      rw [hsplit_num, hsplit_var, h_cb_var, h_cb_num, h_numDc]
      push_cast
      refine ⟨?_, ?_⟩
      · linarith
      · have heven : Even ((varBetween (der P) (.finite a) (.finite d) -
              (numRoots P (.finite a) (.finite d) : ℤ)) +
            (varBetween (der P) (.finite d) (.finite c) -
              (P.rootMultiplicity c : ℤ))) := h_ad_even.add h_dc_even
        convert heven using 1
        ring
    · -- c = b: (c, b] is empty
      have h_cb_var : varBetween (der P) (.finite c) (.finite b) = 0 := by
        rw [hcb]; unfold varBetween; ring
      have h_cb_num : numRoots P (.finite c) (.finite b) = 0 := by
        rw [hcb]
        simp only [numRoots_finite_finite]
        rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
        rintro r _ ⟨h1, h2⟩
        exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
      rw [hsplit_num, hsplit_var, h_cb_var, h_cb_num, h_numDc]
      push_cast
      refine ⟨?_, ?_⟩
      · linarith
      · have heven : Even ((varBetween (der P) (.finite a) (.finite d) -
              (numRoots P (.finite a) (.finite d) : ℤ)) +
            (varBetween (der P) (.finite d) (.finite c) -
              (P.rootMultiplicity c : ℤ))) := h_ad_even.add h_dc_even
        convert heven using 1
        ring

/-- **BPR Theorem 2.35 (Budan-Fourier, finite-endpoint case).** For any nonzero
    `P ∈ R[X]` and `a < b`, the number of sign variations of `Der(P)` on `(a, b]`
    bounds the number of roots of `P` on `(a, b]` (counted with multiplicity),
    and the difference `Var(Der(P); a, b) − num(P; (a, b])` is even. -/
theorem budan_fourier_finite (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) {a b : R} (hab : a < b) :
    ((numRoots P (.finite a) (.finite b) : ℤ) ≤
      varBetween (der P) (.finite a) (.finite b)) ∧
    Even (varBetween (der P) (.finite a) (.finite b) -
      (numRoots P (.finite a) (.finite b) : ℤ)) :=
  budan_fourier_finite_aux hIVP hP _ hab (le_refl _)

/-! ### Reduction to the finite case for `±∞` endpoints

For `|x|` large, Proposition 2.4 (via `hasSignAtPosInfty_leadingCoeff`) says
`sign((⇑derivative)^[k] P .eval x) = sign((⇑derivative)^[k] P).leadingCoeff`.
Taking the max over `k ≤ natDegree P` of the bounds gives a single `B` at which
all iterated derivatives' signs stabilize. For such `B`:
  * `varAt (der P) (finite B) = varAt (der P) posInf` (by `Var_congr_sign`).
  * No root of `P` lies beyond `B` (since `P(x) ≠ 0` for `x > B`), so
    `numRoots P (finite a) (finite B) = numRoots P (finite a) posInf`.

The `±∞` cases then follow from `budan_fourier_finite`. -/

/-- There exists a bound `B` such that for every `x > B` and every `k ≤ natDegree P`,
    the sign of `(derivative)^[k] P` at `x` matches the sign of its leading
    coefficient. -/
private lemma exists_bound_pos_iterate_signs (P : R[X]) :
    ∃ B, ∀ k ≤ P.natDegree, ∀ x, B < x →
      SignType.sign (((⇑derivative)^[k] P).eval x) =
        SignType.sign ((⇑derivative)^[k] P).leadingCoeff := by
  classical
  choose M hM using (fun k : Fin (P.natDegree + 1) =>
    hasSignAtPosInfty_leadingCoeff ((⇑derivative)^[k.val] P))
  set S : Finset R := Finset.image M Finset.univ
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨S.max' hS, fun k hk x hx => ?_⟩
  have hM_mem : M ⟨k, Nat.lt_succ_of_le hk⟩ ∈ S :=
    Finset.mem_image.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, Finset.mem_univ _, rfl⟩
  have hM_le : M ⟨k, Nat.lt_succ_of_le hk⟩ ≤ S.max' hS :=
    Finset.le_max' _ _ hM_mem
  exact hM ⟨k, Nat.lt_succ_of_le hk⟩ x (lt_of_le_of_lt hM_le hx)

/-- Symmetric bound at `−∞`: for every `x < B` and every `k ≤ natDegree P`,
    `sign((derivative)^[k] P .eval x) = (-1)^natDegree · sign(leadingCoeff)`. -/
private lemma exists_bound_neg_iterate_signs (P : R[X]) :
    ∃ B, ∀ k ≤ P.natDegree, ∀ x, x < B →
      SignType.sign (((⇑derivative)^[k] P).eval x) =
        (-1) ^ ((⇑derivative)^[k] P).natDegree *
          SignType.sign ((⇑derivative)^[k] P).leadingCoeff := by
  classical
  choose M hM using (fun k : Fin (P.natDegree + 1) =>
    hasSignAtNegInfty_leadingCoeff ((⇑derivative)^[k.val] P))
  set S : Finset R := Finset.image M Finset.univ
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨S.min' hS, fun k hk x hx => ?_⟩
  have hM_mem : M ⟨k, Nat.lt_succ_of_le hk⟩ ∈ S :=
    Finset.mem_image.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, Finset.mem_univ _, rfl⟩
  have hM_ge : S.min' hS ≤ M ⟨k, Nat.lt_succ_of_le hk⟩ :=
    Finset.min'_le _ _ hM_mem
  exact hM ⟨k, Nat.lt_succ_of_le hk⟩ x (lt_of_lt_of_le hx hM_ge)

/-- If `B` stabilizes the signs of all iterated derivatives, then
    `varAt (der P) (finite B) = varAt (der P) posInf`. -/
private lemma varAt_finite_eq_posInf_of_signs_stable
    {P : R[X]} {B : R}
    (h : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B) =
        SignType.sign ((⇑derivative)^[k] P).leadingCoeff) :
    varAt (der P) (.finite B) = varAt (der P) ExtendedPoint.posInf := by
  rw [varAt_finite, varAt_posInf]
  apply Var_congr_sign
  unfold der
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp_apply]
  exact h i (Nat.lt_succ_iff.mp hi)

/-- Symmetric: if `B` stabilizes signs at `−∞`, then
    `varAt (der P) (finite B) = varAt (der P) negInf`. -/
private lemma varAt_finite_eq_negInf_of_signs_stable
    {P : R[X]} {B : R}
    (h : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B) =
        (-1) ^ ((⇑derivative)^[k] P).natDegree *
          SignType.sign ((⇑derivative)^[k] P).leadingCoeff) :
    varAt (der P) (.finite B) = varAt (der P) ExtendedPoint.negInf := by
  rw [varAt_finite, varAt_negInf]
  apply Var_congr_sign
  unfold der
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp hi
  have hsign_mul :
      SignType.sign ((-1 : R) ^ ((⇑derivative)^[i] P).natDegree *
        ((⇑derivative)^[i] P).leadingCoeff) =
      (-1) ^ ((⇑derivative)^[i] P).natDegree *
        SignType.sign ((⇑derivative)^[i] P).leadingCoeff := by
    rw [sign_mul]
    congr 1
    rcases Nat.even_or_odd ((⇑derivative)^[i] P).natDegree with hev | hod
    · rw [hev.neg_one_pow, hev.neg_one_pow, sign_one]
    · rw [hod.neg_one_pow, hod.neg_one_pow]
      exact _root_.sign_neg neg_one_lt_zero
  simp only [Function.comp_apply]
  rw [h i hi', hsign_mul]

omit [IsStrictOrderedRing R] in
/-- If every root of `P` is `≤ B`, then
    `numRoots P (finite a) (finite B) = numRoots P (finite a) posInf`. -/
private lemma numRoots_finite_eq_posInf_of_roots_bdd
    {P : R[X]} {a B : R} (hB : ∀ r ∈ P.roots, r ≤ B) :
    numRoots P (.finite a) (.finite B) = numRoots P (.finite a) .posInf := by
  classical
  show (P.roots.filter (fun r => a < r ∧ r ≤ B)).card =
    (P.roots.filter (a < ·)).card
  congr 1
  apply Multiset.filter_congr
  intro r hr
  exact ⟨fun h => h.1, fun h => ⟨h, hB r hr⟩⟩

omit [IsStrictOrderedRing R] in
/-- If every root of `P` is strictly `> B`, then
    `numRoots P (finite B) (finite b) = numRoots P negInf (finite b)`. -/
private lemma numRoots_finite_eq_negInf_of_roots_bdd
    {P : R[X]} {B b : R} (hB : ∀ r ∈ P.roots, B < r) :
    numRoots P (.finite B) (.finite b) = numRoots P .negInf (.finite b) := by
  classical
  show (P.roots.filter (fun r => B < r ∧ r ≤ b)).card =
    (P.roots.filter (· ≤ b)).card
  congr 1
  apply Multiset.filter_congr
  intro r hr
  exact ⟨fun h => h.2, fun h => ⟨hB r hr, h⟩⟩

omit [IsStrictOrderedRing R] in
/-- Symmetric versions for the `negInf, posInf` case. -/
private lemma numRoots_finite_finite_eq_negInf_posInf
    {P : R[X]} {B₁ B₂ : R} (hB₁ : ∀ r ∈ P.roots, B₁ < r)
    (hB₂ : ∀ r ∈ P.roots, r ≤ B₂) :
    numRoots P (.finite B₁) (.finite B₂) = numRoots P .negInf .posInf := by
  classical
  show (P.roots.filter (fun r => B₁ < r ∧ r ≤ B₂)).card = P.roots.card
  congr 1
  rw [Multiset.filter_eq_self]
  exact fun r hr => ⟨hB₁ r hr, hB₂ r hr⟩

/-- A witness `B > a` giving a finite endpoint that matches `posInf` for both
    `varBetween` and `numRoots`. -/
private lemma exists_finite_eq_posInf
    {P : R[X]} (hP : P ≠ 0) (a : R) :
    ∃ B, a < B ∧
      varAt (der P) (.finite B) = varAt (der P) .posInf ∧
      numRoots P (.finite a) (.finite B) = numRoots P (.finite a) .posInf := by
  obtain ⟨M, hM⟩ := exists_bound_pos_iterate_signs P
  -- Pick B strictly larger than both `a` and `M`.
  set B := max a M + 1 with hB_def
  have hMB : M < B := by rw [hB_def]; linarith [le_max_right a M]
  have haB : a < B := by rw [hB_def]; linarith [le_max_left a M]
  have hsign_at_B : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B) =
        SignType.sign ((⇑derivative)^[k] P).leadingCoeff :=
    fun k hk => hM k hk B hMB
  have hP_lc : P.leadingCoeff ≠ 0 := fun h => hP (Polynomial.leadingCoeff_eq_zero.mp h)
  have hroots_bd : ∀ r ∈ P.roots, r ≤ B := by
    intro r hr
    by_contra hrB
    push Not at hrB
    have hMr : M < r := lt_trans hMB hrB
    have hsign := hM 0 (Nat.zero_le _) r hMr
    simp only [Function.iterate_zero_apply] at hsign
    have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
    rw [hPr, _root_.sign_zero] at hsign
    have : SignType.sign P.leadingCoeff = 0 := hsign.symm
    rw [sign_eq_zero_iff] at this
    exact hP_lc this
  exact ⟨B, haB,
    varAt_finite_eq_posInf_of_signs_stable hsign_at_B,
    numRoots_finite_eq_posInf_of_roots_bdd hroots_bd⟩

/-- A witness `B < b` giving a finite endpoint that matches `negInf`. -/
private lemma exists_finite_eq_negInf
    {P : R[X]} (hP : P ≠ 0) (b : R) :
    ∃ B, B < b ∧
      varAt (der P) (.finite B) = varAt (der P) .negInf ∧
      numRoots P (.finite B) (.finite b) = numRoots P .negInf (.finite b) := by
  obtain ⟨M, hM⟩ := exists_bound_neg_iterate_signs P
  set B := min b M - 1 with hB_def
  have hBM : B < M := by rw [hB_def]; linarith [min_le_right b M]
  have hBb : B < b := by rw [hB_def]; linarith [min_le_left b M]
  have hsign_at_B : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B) =
        (-1) ^ ((⇑derivative)^[k] P).natDegree *
          SignType.sign ((⇑derivative)^[k] P).leadingCoeff :=
    fun k hk => hM k hk B hBM
  have hP_lc : P.leadingCoeff ≠ 0 := fun h => hP (Polynomial.leadingCoeff_eq_zero.mp h)
  have hroots_bd : ∀ r ∈ P.roots, B < r := by
    intro r hr
    by_contra hrB
    push Not at hrB
    have hrM : r < M := lt_of_le_of_lt hrB hBM
    have hsign := hM 0 (Nat.zero_le _) r hrM
    simp only [Function.iterate_zero_apply] at hsign
    have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
    rw [hPr, _root_.sign_zero] at hsign
    have hsign_lc_ne : SignType.sign P.leadingCoeff ≠ 0 := by
      rwa [ne_eq, sign_eq_zero_iff]
    have hpow_ne : ((-1 : SignType)) ^ P.natDegree ≠ 0 := by
      rcases Nat.even_or_odd P.natDegree with hev | hod
      · rw [hev.neg_one_pow]; decide
      · rw [hod.neg_one_pow]; decide
    exact mul_ne_zero hpow_ne hsign_lc_ne hsign.symm
  exact ⟨B, hBb,
    varAt_finite_eq_negInf_of_signs_stable hsign_at_B,
    numRoots_finite_eq_negInf_of_roots_bdd hroots_bd⟩

/-- **BPR Theorem 2.35 (Budan-Fourier), `(a, +∞)` case.** -/
theorem budan_fourier_posInf (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (a : R) :
    ((numRoots P (.finite a) .posInf : ℤ) ≤
      varBetween (der P) (.finite a) .posInf) ∧
    Even (varBetween (der P) (.finite a) .posInf -
      (numRoots P (.finite a) .posInf : ℤ)) := by
  obtain ⟨B, haB, hvar, hnum⟩ := exists_finite_eq_posInf hP a
  have hfin := budan_fourier_finite hIVP hP haB
  have hvar_eq : varBetween (der P) (.finite a) .posInf =
      varBetween (der P) (.finite a) (.finite B) := by
    unfold varBetween; rw [hvar]
  rw [hvar_eq, ← hnum]
  exact hfin

/-- **BPR Theorem 2.35 (Budan-Fourier), `(−∞, b]` case.** -/
theorem budan_fourier_negInf (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (b : R) :
    ((numRoots P .negInf (.finite b) : ℤ) ≤
      varBetween (der P) .negInf (.finite b)) ∧
    Even (varBetween (der P) .negInf (.finite b) -
      (numRoots P .negInf (.finite b) : ℤ)) := by
  obtain ⟨B, hBb, hvar, hnum⟩ := exists_finite_eq_negInf hP b
  have hfin := budan_fourier_finite hIVP hP hBb
  have hvar_eq : varBetween (der P) .negInf (.finite b) =
      varBetween (der P) (.finite B) (.finite b) := by
    unfold varBetween; rw [hvar]
  rw [hvar_eq, ← hnum]
  exact hfin

/-- **BPR Theorem 2.35 (Budan-Fourier), `(−∞, +∞)` case.** -/
theorem budan_fourier_negInf_posInf (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) :
    ((numRoots P .negInf .posInf : ℤ) ≤ varBetween (der P) .negInf .posInf) ∧
    Even (varBetween (der P) .negInf .posInf -
      (numRoots P .negInf .posInf : ℤ)) := by
  obtain ⟨Mp, hMp⟩ := exists_bound_pos_iterate_signs P
  obtain ⟨Mn, hMn⟩ := exists_bound_neg_iterate_signs P
  set B₂ := max Mp (Mn + 1) + 1 with hB₂_def
  set B₁ := min Mn (Mp - 1) - 1 with hB₁_def
  have hMpB₂ : Mp < B₂ := by rw [hB₂_def]; linarith [le_max_left Mp (Mn + 1)]
  have hB₁Mn : B₁ < Mn := by rw [hB₁_def]; linarith [min_le_left Mn (Mp - 1)]
  have hB₁_lt_B₂ : B₁ < B₂ := by
    have h1 : B₁ < Mp := by
      rw [hB₁_def]; linarith [min_le_right Mn (Mp - 1)]
    have h2 : Mn < B₂ := by
      rw [hB₂_def]; linarith [le_max_right Mp (Mn + 1)]
    -- Either pathway works; we just need B₁ < B₂. Use B₁ < Mp ≤ B₂.
    linarith
  -- Sign stabilization at B₂ (posInf side).
  have hsign_at_B₂ : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B₂) =
        SignType.sign ((⇑derivative)^[k] P).leadingCoeff :=
    fun k hk => hMp k hk B₂ hMpB₂
  -- Sign stabilization at B₁ (negInf side).
  have hsign_at_B₁ : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B₁) =
        (-1) ^ ((⇑derivative)^[k] P).natDegree *
          SignType.sign ((⇑derivative)^[k] P).leadingCoeff :=
    fun k hk => hMn k hk B₁ hB₁Mn
  have hP_lc : P.leadingCoeff ≠ 0 := fun h => hP (Polynomial.leadingCoeff_eq_zero.mp h)
  -- All roots ≤ B₂.
  have hroots_bd₂ : ∀ r ∈ P.roots, r ≤ B₂ := by
    intro r hr
    by_contra hrB
    push Not at hrB
    have hMr : Mp < r := lt_trans hMpB₂ hrB
    have hsign := hMp 0 (Nat.zero_le _) r hMr
    simp only [Function.iterate_zero_apply] at hsign
    have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
    rw [hPr, _root_.sign_zero] at hsign
    have : SignType.sign P.leadingCoeff = 0 := hsign.symm
    rw [sign_eq_zero_iff] at this
    exact hP_lc this
  -- All roots > B₁.
  have hroots_bd₁ : ∀ r ∈ P.roots, B₁ < r := by
    intro r hr
    by_contra hrB
    push Not at hrB
    have hrM : r < Mn := lt_of_le_of_lt hrB hB₁Mn
    have hsign := hMn 0 (Nat.zero_le _) r hrM
    simp only [Function.iterate_zero_apply] at hsign
    have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
    rw [hPr, _root_.sign_zero] at hsign
    have hsign_lc_ne : SignType.sign P.leadingCoeff ≠ 0 := by
      rwa [ne_eq, sign_eq_zero_iff]
    have hpow_ne : ((-1 : SignType)) ^ P.natDegree ≠ 0 := by
      rcases Nat.even_or_odd P.natDegree with hev | hod
      · rw [hev.neg_one_pow]; decide
      · rw [hod.neg_one_pow]; decide
    exact mul_ne_zero hpow_ne hsign_lc_ne hsign.symm
  have hvar_B₂ : varAt (der P) (.finite B₂) = varAt (der P) .posInf :=
    varAt_finite_eq_posInf_of_signs_stable hsign_at_B₂
  have hvar_B₁ : varAt (der P) (.finite B₁) = varAt (der P) .negInf :=
    varAt_finite_eq_negInf_of_signs_stable hsign_at_B₁
  have hnum_eq : numRoots P (.finite B₁) (.finite B₂) = numRoots P .negInf .posInf :=
    numRoots_finite_finite_eq_negInf_posInf hroots_bd₁ hroots_bd₂
  have hfin := budan_fourier_finite hIVP hP hB₁_lt_B₂
  have hvar_eq : varBetween (der P) .negInf .posInf =
      varBetween (der P) (.finite B₁) (.finite B₂) := by
    unfold varBetween; rw [hvar_B₁, hvar_B₂]
  rw [hvar_eq, ← hnum_eq]
  exact hfin

/-! Note: BPR Example 2.37 (refinement impossibility for `X² − X + 1` on
`(0, 1]`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_2.Example_2_37`. -/

/-! Note: BPR Exercise 2.12 (`numRoots_eq_zero_of_var_eq_zero`,
`numRoots_eq_one_of_var_eq_one`, `no_root_of_var_eq_zero`,
`unique_simple_root_of_var_eq_one`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_2.Exercise_2_12`. -/


/-! Note: BPR Remark 2.38 (`var_eq_numRoots_of_all_roots_real`, equality form
of Budan-Fourier when every root of `P` lies in the base field) is defined
in `Azurite.BasuPollackRoy.Chapter2.Section2_2.Remark_2_38`. -/

end Azurite.BPR.Theorem2_35
