import Azurite.BasuPollackRoy.Chapter4.Section4_7.WeakBezoutContinuity
import Azurite.BasuPollackRoy.Chapter4.Section4_7.AtLeastZerosSemialg
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Theorem_3_19

/-!
# BPR §4.7, Proposition 4.106: final assembly of the weak Bézout bound

This file supplies the three analytic inputs to the already-proven logical chain in
`WeakBezoutCount.lean` and assembles `proposition_4_106_of_sa` / `proposition_4_106`:

* a half-open deformation path `γ` from `(1:0)` to `(0:1)` whose interior `(0,1]` avoids the singular
  parameter set `Δ` (gap (a));
* relative openness of `Pm m` in `(0,1]` via the local implicit function theorem (gap (b));
* relative closedness of `Pm m` in `(0,1]` via curve selection and projective completeness (gap (c)).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

open scoped Azurite.BPR
open scoped Pointwise

/-! ### Half-open detour point -/

set_option linter.unusedSectionVars false in
/-- **Half-open detour point.** For `k ≥ 2`, a possibly-bad start `a` and a good end `b ∉ Δ`, there
is a detour point `w` with `w ∉ Δ`, `w ≠ a`, such that:
* the segment `[a,w]` avoids every point of `Δ` except possibly `a` itself, and
* the segment `[w,b]` avoids every point of `insert a Δ` (in particular it avoids `a`).
Mirrors `exists_detour_point`, but the `a`-endpoint may lie in `Δ`. -/
theorem exists_detour_point_halfopen {k : ℕ} (hk : 2 ≤ k) (Δ : Finset (Fin k → R))
    {a b : Fin k → R} (hb : b ∉ Δ) (hab : a ≠ b) :
    ∃ w : Fin k → R, w ∉ Δ ∧ w ≠ a ∧
      (∀ δ ∈ Δ, δ ≠ a → ∀ t : R, t ∈ Set.Icc (0 : R) 1 → δ ≠ (1 - t) • a + t • w) ∧
      (∀ δ ∈ insert a Δ, ∀ t : R, t ∈ Set.Icc (0 : R) 1 → δ ≠ (1 - t) • w + t • b) := by
  classical
  set Δa : Finset (Fin k → R) := insert a Δ with hΔa
  -- Coset data on `Fin 4 × (Fin k → R)`:
  -- label 0 ↦ point δ (forces w ∉ Δ);   label 3 ↦ point a (forces w ≠ a);
  -- label 1 ↦ line through a (x-side);   label 2 ↦ line through b (y-side, over insert a Δ).
  set s : Finset (Fin 4 × (Fin k → R)) :=
    insert (3, a)
      (({0} : Finset (Fin 4)) ×ˢ Δ
        ∪ ({1} : Finset (Fin 4)) ×ˢ Δ
        ∪ ({2} : Finset (Fin 4)) ×ˢ Δa) with hs
  set Wf : Fin 4 × (Fin k → R) → Submodule R (Fin k → R) := fun p =>
    if p.1 = 1 then Submodule.span R {p.2 - a}
    else if p.1 = 2 then Submodule.span R {p.2 - b}
    else ⊥ with hWf
  set gf : Fin 4 × (Fin k → R) → (Fin k → R) := fun p =>
    if p.1 = 0 then p.2
    else if p.1 = 1 then a
    else if p.1 = 2 then b
    else a with hgf
  have hproper : ∀ p ∈ s, Wf p ≠ ⊤ := by
    intro p _
    simp only [hWf]
    split_ifs
    · exact span_singleton_ne_top hk _
    · exact span_singleton_ne_top hk _
    · exact bot_ne_top hk
  have hne : ⋃ p ∈ s, (gf p +ᵥ (Wf p : Set (Fin k → R))) ≠ Set.univ :=
    coset_cover_proper_ne_univ hproper
  obtain ⟨w, hw⟩ : ∃ w, w ∉ ⋃ p ∈ s, (gf p +ᵥ (Wf p : Set (Fin k → R))) := by
    by_contra h
    push Not at h
    exact hne (Set.eq_univ_of_forall h)
  simp only [Set.mem_iUnion, not_exists] at hw
  -- membership helpers for `s`
  have hmem0 : ∀ δ ∈ Δ, (0, δ) ∈ s := by
    intro δ hδ
    rw [hs]; rw [Finset.mem_insert]; refine Or.inr ?_
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Finset.mem_product.mpr ⟨by simp, hδ⟩))
  have hmem3 : (3, a) ∈ s := by rw [hs]; exact Finset.mem_insert_self _ _
  have hmem1 : ∀ δ ∈ Δ, (1, δ) ∈ s := by
    intro δ hδ
    rw [hs]; rw [Finset.mem_insert]; refine Or.inr ?_
    simp only [Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_product.mpr ⟨by simp, hδ⟩))
  have hmem2 : ∀ δ ∈ Δa, (2, δ) ∈ s := by
    intro δ hδ
    rw [hs]; rw [Finset.mem_insert]; refine Or.inr ?_
    simp only [Finset.mem_union]
    exact Or.inr (Finset.mem_product.mpr ⟨by simp, hδ⟩)
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · -- w ∉ Δ
    intro hwΔ
    refine hw (0, w) (hmem0 w hwΔ) ?_
    show w ∈ gf (0, w) +ᵥ (Wf (0, w) : Set (Fin k → R))
    have h1 : gf (0, w) = w := by rw [hgf]; simp
    have h2 : Wf (0, w) = ⊥ := by rw [hWf]; simp
    rw [h1, h2]
    exact ⟨0, Submodule.zero_mem _, by simp⟩
  · -- w ≠ a
    intro hwa
    refine hw (3, a) hmem3 ?_
    show w ∈ gf (3, a) +ᵥ (Wf (3, a) : Set (Fin k → R))
    have h1 : gf (3, a) = a := by simp only [hgf]; norm_num [Fin.ext_iff]
    have h2 : Wf (3, a) = ⊥ := by simp only [hWf]; norm_num [Fin.ext_iff]
    rw [h1, h2, hwa]
    exact ⟨0, Submodule.zero_mem _, by simp⟩
  · -- [a,w] avoids Δ \ {a}
    rintro δ hδ hδa t ht heq
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp only [sub_zero, one_smul, zero_smul, add_zero] at heq
      exact hδa heq
    refine hw (1, δ) (hmem1 δ hδ) ?_
    show w ∈ gf (1, δ) +ᵥ (Wf (1, δ) : Set (Fin k → R))
    have h1 : gf (1, δ) = a := by simp only [hgf]; norm_num [Fin.ext_iff]
    have h2 : Wf (1, δ) = Submodule.span R {δ - a} := by simp only [hWf]; norm_num [Fin.ext_iff]
    rw [h1, h2]
    refine ⟨t⁻¹ • (δ - a), Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    have hwa : δ - a = t • (w - a) := by
      rw [heq]; ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    show a + t⁻¹ • (δ - a) = w
    rw [hwa, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    ext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  · -- [w,b] avoids insert a Δ
    rintro δ hδ t ht heq
    have ht1 : (1 - t) ≠ 0 := by
      intro h
      have ht1' : t = 1 := by linarith [sub_eq_zero.mp h]
      rw [ht1'] at heq
      simp only [sub_self, zero_smul, one_smul, zero_add] at heq
      -- δ = b, but δ ∈ insert a Δ contradicts (a ≠ b) and (b ∉ Δ)
      rw [hΔa, Finset.mem_insert] at hδ
      rcases hδ with hδa | hδΔ
      · exact hab (hδa.symm.trans heq)
      · exact hb (heq ▸ hδΔ)
    refine hw (2, δ) (hmem2 δ hδ) ?_
    show w ∈ gf (2, δ) +ᵥ (Wf (2, δ) : Set (Fin k → R))
    have h1 : gf (2, δ) = b := by simp only [hgf]; norm_num [Fin.ext_iff]
    have h2 : Wf (2, δ) = Submodule.span R {δ - b} := by simp only [hWf]; norm_num [Fin.ext_iff]
    rw [h1, h2]
    refine ⟨(1 - t)⁻¹ • (δ - b), Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    have hwb : δ - b = (1 - t) • (w - b) := by
      rw [heq]; ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    show b + (1 - t)⁻¹ • (δ - b) = w
    rw [hwb, smul_smul, inv_mul_cancel₀ ht1, one_smul]
    ext i; simp only [Pi.add_apply, Pi.sub_apply]; ring

/-! ### Half-open affine chart path -/

set_option linter.unusedSectionVars false in
/-- **Half-open affine chart path.** If `x, y ∈ 𝒰ᵢ` lie in the same chart, `y ∉ Δ`, and `x ≠ y`,
there is an affine path `ϕ : R¹ → R^{2k}` with semialgebraic graph, continuous on `[0,1]`, with
`ϕ 0 = realEquiv(chartInv i x)`, `ϕ 1 = realEquiv(chartInv i y)`, whose chart-`i` lift avoids `Δ` on
the half-open interval `(0,1]` (the start `x` may be in `Δ`). -/
theorem halfOpenChartPath_affine {k : ℕ} (hk : 1 ≤ k) (Δ : Finset (complexProjectiveSpace R k))
    (i : Fin (k + 1)) {x y : complexProjectiveSpace R k}
    (hxi : x ∈ (chartSet i : Set (complexProjectiveSpace R k)))
    (hyi : y ∈ (chartSet i : Set (complexProjectiveSpace R k)))
    (hyΔ : y ∉ (↑Δ : Set (complexProjectiveSpace R k)))
    (hxy : x ≠ y) :
    ∃ ϕ : (Fin 1 → R) → (Fin (k + k) → R),
      IsSemialgebraicSet (funGraph (Set.Icc 0 1) ϕ) ∧
      ContinuousOn ϕ (Set.Icc 0 1) ∧
      ϕ 0 = realEquiv (chartInv i x) ∧
      ϕ 1 = realEquiv (chartInv i y) ∧
      (∀ t ∈ Set.Icc (0 : Fin 1 → R) 1, 0 < t 0 →
        chartMap i (realEquiv.symm (ϕ t)) ∉ (↑Δ : Set (complexProjectiveSpace R k))) := by
  classical
  have hk2 : 2 ≤ k + k := by omega
  set a := realEquiv (chartInv i x) with ha
  set b := realEquiv (chartInv i y) with hb
  -- the chart obstacle in affine coordinates
  set Δ' : Finset (Fin (k + k) → R) :=
    (Δ.filter (fun δ => δ ∈ chartSet i)).image (fun δ => realEquiv (chartInv i δ)) with hΔ'
  -- realified chart coords of a point in `chartSet i ∩ Δ` land in `Δ'`
  have hkey : ∀ p : complexProjectiveSpace R k, p ∈ (chartSet i : Set (complexProjectiveSpace R k)) →
      realEquiv (chartInv i p) ∈ Δ' → p ∈ Δ := by
    intro p hpi hmem
    rw [hΔ', Finset.mem_image] at hmem
    obtain ⟨δ, hδf, hδe⟩ := hmem
    rw [Finset.mem_filter] at hδf
    have hci : chartInv i δ = chartInv i p := realEquiv.injective hδe
    have hδrep : δ.rep i ≠ 0 := by rw [chartSet_eq] at hδf; exact hδf.2
    have hprep : p.rep i ≠ 0 := by rw [chartSet_eq] at hpi; exact hpi
    have : δ = p := by
      have h1 := chartMap_chartInv i δ hδrep
      have h2 := chartMap_chartInv i p hprep
      rw [hci] at h1; rw [← h1, h2]
    rw [← this]; exact hδf.1
  have hbΔ : b ∉ Δ' := fun h => hyΔ (by rw [Finset.mem_coe]; exact hkey y hyi h)
  -- `a ≠ b` from `x ≠ y`
  have hab : a ≠ b := by
    intro h
    apply hxy
    have hci : chartInv i x = chartInv i y := realEquiv.injective h
    have hxrep : x.rep i ≠ 0 := by rw [chartSet_eq] at hxi; exact hxi
    have hyrep : y.rep i ≠ 0 := by rw [chartSet_eq] at hyi; exact hyi
    have h1 := chartMap_chartInv i x hxrep
    have h2 := chartMap_chartInv i y hyrep
    rw [hci] at h1; rw [← h1, h2]
  -- the half-open detour point
  obtain ⟨w, hwΔ, hwa, hxw, hwy⟩ := exists_detour_point_halfopen hk2 Δ' hbΔ hab
  -- piecewise affine path as polynomial maps in `X 0`
  set P₁ : Fin (k + k) → MvPolynomial (Fin 1) R :=
    fun j => (1 - 2 * X 0) * C (a j) + (2 * X 0) * C (w j) with hP₁
  set P₂ : Fin (k + k) → MvPolynomial (Fin 1) R :=
    fun j => (1 - (2 * X 0 - 1)) * C (w j) + (2 * X 0 - 1) * C (b j) with hP₂
  have hev₁ : ∀ u : Fin 1 → R,
      polynomialMap P₁ u = (1 - 2 * u 0) • a + (2 * u 0) • w := by
    intro u; funext j
    simp only [polynomialMap, hP₁, map_add, map_mul, map_sub, map_one, eval_X, eval_C,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_ofNat]
  have hev₂ : ∀ u : Fin 1 → R,
      polynomialMap P₂ u = (1 - (2 * u 0 - 1)) • w + (2 * u 0 - 1) • b := by
    intro u; funext j
    simp only [polynomialMap, hP₂, map_add, map_mul, map_sub, map_one, eval_X, eval_C,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_ofNat]
  set ϕ : (Fin 1 → R) → (Fin (k + k) → R) :=
    fun u => if u 0 ≤ 1 / 2 then polynomialMap P₁ u else polynomialMap P₂ u with hϕ
  set H₁ : Set (Fin 1 → R) := Set.Icc (constPt 0) (constPt (1 / 2)) with hH₁
  set H₂ : Set (Fin 1 → R) := Set.Icc (constPt (1 / 2)) (constPt 1) with hH₂
  have hH₁mem : ∀ u, u ∈ H₁ ↔ 0 ≤ u 0 ∧ u 0 ≤ 1 / 2 := fun u => mem_Icc_fin_one_local
  have hH₂mem : ∀ u, u ∈ H₂ ↔ 1 / 2 ≤ u 0 ∧ u 0 ≤ 1 := fun u => mem_Icc_fin_one_local
  have hunion : Set.Icc (0 : Fin 1 → R) 1 = H₁ ∪ H₂ := by
    ext u
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, show (1 : Fin 1 → R) = constPt 1 from rfl,
      mem_Icc_fin_one_local]
    simp only [Set.mem_union, hH₁mem, hH₂mem]
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_or_gt (u 0) (1 / 2) with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h.le, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨h0, by linarith⟩
      · exact ⟨by linarith, h1⟩
  have hϕ₁ : ∀ u ∈ H₁, ϕ u = polynomialMap P₁ u := by
    intro u hu
    simp only [hϕ]; exact if_pos ((hH₁mem u).mp hu).2
  have hϕ₂ : ∀ u ∈ H₂, ϕ u = polynomialMap P₂ u := by
    intro u hu
    simp only [hϕ]
    rcases le_or_gt (u 0) (1 / 2) with h | h
    · have hhalf : u 0 = 1 / 2 := le_antisymm h ((hH₂mem u).mp hu).1
      rw [if_pos h, hev₁, hev₂, hhalf]; norm_num
    · rw [if_neg (not_le.mpr h)]
  refine ⟨ϕ, ?_, ?_, ?_, ?_, ?_⟩
  · -- semialgebraic graph
    rw [hunion, funGraph_union]
    refine IsSemialgebraicSet.union ?_ ?_
    · rw [funGraph_congr hϕ₁]
      exact isSemialgebraicFunction_polynomialMap (isSemialgebraicSet_Icc_local _ _) P₁
    · rw [funGraph_congr hϕ₂]
      exact isSemialgebraicFunction_polynomialMap (isSemialgebraicSet_Icc_local _ _) P₂
  · -- continuous
    rw [hunion]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_Icc_local _ _) (isClosed_Icc_local _ _)
    · exact (continuous_polynomialMap P₁).continuousOn.congr hϕ₁
    · exact (continuous_polynomialMap P₂).continuousOn.congr hϕ₂
  · -- ϕ 0 = a
    have h0 : ((0 : Fin 1 → R)) ∈ H₁ := by rw [hH₁mem]; show 0 ≤ (0:R) ∧ (0:R) ≤ 1/2; norm_num
    rw [hϕ₁ _ h0, hev₁]
    show (1 - 2 * (0 : Fin 1 → R) 0) • a + (2 * (0 : Fin 1 → R) 0) • w = a
    simp only [Pi.zero_apply, mul_zero, sub_zero, one_smul, zero_smul, add_zero]
  · -- ϕ 1 = b
    have h1 : ((1 : Fin 1 → R)) ∈ H₂ := by rw [hH₂mem]; show 1/2 ≤ (1:R) ∧ (1:R) ≤ 1; norm_num
    rw [hϕ₂ _ h1, hev₂]
    show (1 - (2 * (1 : Fin 1 → R) 0 - 1)) • w + (2 * (1 : Fin 1 → R) 0 - 1) • b = b
    simp only [Pi.one_apply, mul_one]
    norm_num
  · -- avoid Δ on (0,1]
    intro t ht ht0 hmem
    rw [hunion] at ht
    -- the chart-i lift is in chartSet i, so its coords lie in Δ' if it lies in Δ
    have hγti : chartMap i (realEquiv.symm (ϕ t)) ∈ chartSet i := Set.mem_range_self _
    have hci : chartInv i (chartMap i (realEquiv.symm (ϕ t))) = realEquiv.symm (ϕ t) := by
      rw [chartInv_chartMap]
    have hγti' : (chartMap i (realEquiv.symm (ϕ t))).rep i ≠ 0 := by
      rw [chartSet_eq] at hγti; exact hγti
    have hΔ'mem : ϕ t ∈ Δ' := by
      rw [hΔ', Finset.mem_image]
      refine ⟨chartMap i (realEquiv.symm (ϕ t)),
        by rw [Finset.mem_filter]; exact ⟨hmem, by rw [chartSet_eq]; exact hγti'⟩, ?_⟩
      rw [hci, Equiv.apply_symm_apply]
    -- but ϕ t ∉ Δ' on (0,1]:  contradiction
    rcases ht with hu | hu
    · -- first half: parameter s = 2 t₀ ∈ (0,1]
      obtain ⟨h0, hhalf⟩ := (hH₁mem t).mp hu
      rw [hϕ₁ t hu, hev₁] at hΔ'mem
      -- ϕ t = (1 - 2t₀) a + 2t₀ w.  Since w ≠ a and 2t₀ > 0, this ≠ a; and [a,w] avoids Δ'\{a}.
      have hpt : (1 - 2 * t 0) • a + (2 * t 0) • w ≠ a := by
        intro he
        apply hwa
        have : (2 * t 0) • (w - a) = 0 := by
          have : (1 - 2 * t 0) • a + (2 * t 0) • w - a = (2 * t 0) • (w - a) := by
            ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [← this, he, sub_self]
        have hs : (2 * t 0) ≠ 0 := by positivity
        have := smul_eq_zero.mp this
        rcases this with h | h
        · exact absurd h hs
        · rw [sub_eq_zero] at h; exact h
      rcases eq_or_ne ((1 - 2 * t 0) • a + (2 * t 0) • w) a with heqa | hnea
      · exact hpt heqa
      · -- δ := ϕ t ∈ Δ', δ ≠ a, on segment [a,w] with s = 2t₀ ∈ [0,1]
        exact hxw _ hΔ'mem hnea (2 * t 0) ⟨by linarith, by linarith⟩ rfl
    · -- second half: parameter s = 2t₀ - 1 ∈ [0,1], [w,b] avoids insert a Δ' ⊇ Δ'
      obtain ⟨h1, h2⟩ := (hH₂mem t).mp hu
      rw [hϕ₂ t hu, hev₂] at hΔ'mem
      exact hwy _ (Finset.mem_insert_of_mem hΔ'mem) (2 * t 0 - 1)
        ⟨by linarith, by linarith⟩ rfl

/-! ### Chart memberships of the pencil endpoints -/

set_option linter.unusedSectionVars false in
/-- `(1:0) ∈ 𝒰₀` (its 0-th homogeneous coordinate is nonzero). -/
theorem pencilPt10_mem_chartSet0 :
    pencilPt10 (R := R) ∈ (chartSet 0 : Set (complexProjectiveSpace R 1)) := by
  obtain ⟨c, hc, hrep⟩ :=
    exists_rep_smul (![1, 0] : Fin 2 → Ri R) (vec1t_ne_zero 0)
  rw [chartSet_eq, Set.mem_setOf_eq]
  show (pencilPt10 (R := R)).rep 0 ≠ 0
  rw [pencilPt10, hrep]
  simpa using hc

set_option linter.unusedSectionVars false in
/-- `(0:1) ∈ 𝒰₁` (its 1-st homogeneous coordinate is nonzero). -/
theorem pencilPt01_mem_chartSet1 :
    pencilPt01 (R := R) ∈ (chartSet 1 : Set (complexProjectiveSpace R 1)) := by
  obtain ⟨c, hc, hrep⟩ :=
    exists_rep_smul (![0, 1] : Fin 2 → Ri R) vec01_ne_zero
  rw [chartSet_eq, Set.mem_setOf_eq]
  show (pencilPt01 (R := R)).rep 1 ≠ 0
  rw [pencilPt01, hrep]
  simpa using hc

/-! ### The half-open `γ`-path: BPR §4.7 endpoint deformation -/

set_option linter.unusedSectionVars false in
/-- **Half-open semialgebraic `γ`-path in `ℙ₁(C)`.** There is a continuous, semialgebraic-graph path
`γ : [0,1] → ℙ₁(C)` from `(1:0)` to `(0:1)` whose interior `(0,1]` avoids the singular-parameter set
`Δ` (the start `(1:0)` may itself be singular). The construction concatenates a half-open chart-`0`
path `(1:0) → z₀` (interior off `Δ`) with a full chart-`1` path `z₀ → (0:1)` (off `Δ`), through a
detour point `z₀ ∈ 𝒰₀ ∩ 𝒰₁ ∖ (Δ ∪ {(1:0)})`. -/
theorem exists_halfopen_gammaPath (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    ∃ γ : (Fin 1 → R) → complexProjectiveSpace R 1,
      ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1) ∧
      γ (0 : Fin 1 → R) = pencilPt10 (R := R) ∧
      γ (1 : Fin 1 → R) = pencilPt01 (R := R) ∧
      (∀ w ∈ intervalSet (R := R), γ w ∉ deltaSet P d) ∧
      IsSemialgebraicSetRP
        {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
          tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1} := by
  classical
  set Δ : Finset (complexProjectiveSpace R 1) := deltaFinset P d hd hP with hΔ
  have hΔcoe : (↑Δ : Set (complexProjectiveSpace R 1)) = deltaSet P d := by
    rw [hΔ]; exact coe_deltaFinset P d hd hP
  -- the two endpoints and their chart memberships
  have hx10 : pencilPt10 (R := R) ∈ (chartSet 0 : Set (complexProjectiveSpace R 1)) :=
    pencilPt10_mem_chartSet0
  have hy01 : pencilPt01 (R := R) ∈ (chartSet 1 : Set (complexProjectiveSpace R 1)) :=
    pencilPt01_mem_chartSet1
  have hy01Δ : pencilPt01 (R := R) ∉ (↑Δ : Set (complexProjectiveSpace R 1)) := by
    rw [hΔcoe]; exact pencilPt01_notMem_deltaSet P d hd
  -- detour point `z₀ ∈ 𝒰₀ ∩ 𝒰₁` off `Δ ∪ {(1:0)}`
  obtain ⟨z₀, hz0i, hz0j, hz0Δ'⟩ :=
    exists_detour_point_proj (R := R) (i := 0) (j := 1) (by decide)
      (insert (pencilPt10 (R := R)) Δ)
  have hz0Δ : z₀ ∉ (↑Δ : Set (complexProjectiveSpace R 1)) := by
    intro h; exact hz0Δ' (by rw [Finset.coe_insert]; exact Set.mem_insert_of_mem _ h)
  have hz0ne : z₀ ≠ pencilPt10 (R := R) := by
    intro h; exact hz0Δ' (by rw [Finset.coe_insert, h]; exact Set.mem_insert _ _)
  -- HALF-OPEN affine chart-`0` path  (1:0) → z₀, interior off Δ
  obtain ⟨ϕ₁, hg₁, hc₁, hs₁, ht₁, hav₁⟩ :=
    halfOpenChartPath_affine (k := 1) (le_refl 1) Δ 0 hx10 hz0i hz0Δ (Ne.symm hz0ne)
  -- FULL affine chart-`1` path  z₀ → (0:1)
  obtain ⟨ϕ₂, hg₂, hc₂, hs₂, ht₂, hav₂⟩ :=
    chartPath_affine (k := 1) (le_refl 1) Δ 1 hz0j hy01 hz0Δ hy01Δ
  -- reparametrized affine paths
  set ψ₁ : (Fin 1 → R) → (Fin (1 + 1) → R) := fun u => ϕ₁ (fun _ : Fin 1 => 2 * u 0 + 0) with hψ₁
  set ψ₂ : (Fin 1 → R) → (Fin (1 + 1) → R) := fun u => ϕ₂ (fun _ : Fin 1 => 2 * u 0 + (-1)) with hψ₂
  set γ₁ : (Fin 1 → R) → complexProjectiveSpace R 1 :=
    fun u => chartMap 0 (realEquiv.symm (ψ₁ u)) with hγ₁
  set γ₂ : (Fin 1 → R) → complexProjectiveSpace R 1 :=
    fun u => chartMap 1 (realEquiv.symm (ψ₂ u)) with hγ₂
  set γ : (Fin 1 → R) → complexProjectiveSpace R 1 :=
    fun u => if u 0 ≤ 1 / 2 then γ₁ u else γ₂ u with hγ
  set H₁ : Set (Fin 1 → R) := Set.Icc (constPt 0) (constPt (1 / 2)) with hH₁
  set H₂ : Set (Fin 1 → R) := Set.Icc (constPt (1 / 2)) (constPt 1) with hH₂
  have hH₁mem : ∀ u, u ∈ H₁ ↔ 0 ≤ u 0 ∧ u 0 ≤ 1 / 2 := fun u => mem_Icc_fin_one_local
  have hH₂mem : ∀ u, u ∈ H₂ ↔ 1 / 2 ≤ u 0 ∧ u 0 ≤ 1 := fun u => mem_Icc_fin_one_local
  have hunion : Set.Icc (0 : Fin 1 → R) 1 = H₁ ∪ H₂ := by
    ext u
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, show (1 : Fin 1 → R) = constPt 1 from rfl,
      mem_Icc_fin_one_local]
    simp only [Set.mem_union, hH₁mem, hH₂mem]
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_or_gt (u 0) (1 / 2) with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h.le, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨h0, by linarith⟩
      · exact ⟨by linarith, h1⟩
  have hr₁maps : ∀ u ∈ H₁, (fun _ : Fin 1 => 2 * u 0 + 0) ∈ Set.Icc (0 : Fin 1 → R) 1 := by
    intro u hu
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, show (1 : Fin 1 → R) = constPt 1 from rfl,
      mem_Icc_fin_one_local]
    obtain ⟨h0, h2⟩ := (hH₁mem u).mp hu
    constructor <;> simp <;> linarith
  have hr₂maps : ∀ u ∈ H₂,
      (fun _ : Fin 1 => 2 * u 0 + (-1)) ∈ Set.Icc (0 : Fin 1 → R) 1 := by
    intro u hu
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, show (1 : Fin 1 → R) = constPt 1 from rfl,
      mem_Icc_fin_one_local]
    obtain ⟨h1, h2⟩ := (hH₂mem u).mp hu
    constructor <;> simp <;> linarith
  -- gluing at `u 0 = 1/2`: both halves equal `z₀`
  have hψ₁half : ∀ u : Fin 1 → R, u 0 = 1 / 2 → ψ₁ u = ϕ₁ 1 := by
    intro u hu
    have : (fun _ : Fin 1 => 2 * u 0 + 0) = (1 : Fin 1 → R) := by
      funext s; simp only [Pi.one_apply]; rw [hu]; norm_num
    rw [hψ₁]; show ϕ₁ (fun _ : Fin 1 => 2 * u 0 + 0) = ϕ₁ 1; rw [this]
  have hψ₂half : ∀ u : Fin 1 → R, u 0 = 1 / 2 → ψ₂ u = ϕ₂ 0 := by
    intro u hu
    have : (fun _ : Fin 1 => 2 * u 0 + (-1)) = (0 : Fin 1 → R) := by
      funext s; simp only [Pi.zero_apply]; rw [hu]; norm_num
    rw [hψ₂]; show ϕ₂ (fun _ : Fin 1 => 2 * u 0 + (-1)) = ϕ₂ 0; rw [this]
  have hγ₁z : ∀ u : Fin 1 → R, u 0 = 1 / 2 → γ₁ u = z₀ := by
    intro u hu
    rw [hγ₁]; show chartMap 0 (realEquiv.symm (ψ₁ u)) = z₀
    rw [hψ₁half u hu, ht₁, Equiv.symm_apply_apply]
    exact chartMap_chartInv 0 z₀ (by rw [chartSet_eq] at hz0i; exact hz0i)
  have hγ₂z : ∀ u : Fin 1 → R, u 0 = 1 / 2 → γ₂ u = z₀ := by
    intro u hu
    rw [hγ₂]; show chartMap 1 (realEquiv.symm (ψ₂ u)) = z₀
    rw [hψ₂half u hu, hs₂, Equiv.symm_apply_apply]
    exact chartMap_chartInv 1 z₀ (by rw [chartSet_eq] at hz0j; exact hz0j)
  have hγeq₁ : ∀ u ∈ H₁, γ u = γ₁ u := by
    intro u hu
    show (if u 0 ≤ 1 / 2 then γ₁ u else γ₂ u) = γ₁ u
    exact if_pos ((hH₁mem u).mp hu).2
  have hγeq₂ : ∀ u ∈ H₂, γ u = γ₂ u := by
    intro u hu
    show (if u 0 ≤ 1 / 2 then γ₁ u else γ₂ u) = γ₂ u
    rcases le_or_gt (u 0) (1 / 2) with h | h
    · have hhalf : u 0 = 1 / 2 := le_antisymm h ((hH₂mem u).mp hu).1
      rw [if_pos h, hγ₁z u hhalf, ← hγ₂z u hhalf]
    · rw [if_neg (not_le.mpr h)]
  -- continuity machinery
  have hsymm : Continuous (realEquiv.symm : (Fin (1 + 1) → R) → (Fin 1 → Ri R)) :=
    realEquivₜ.symm.continuous
  have hcontr₁ : Continuous (fun u : Fin 1 → R => (fun _ : Fin 1 => 2 * u 0 + 0)) := by
    have heq : (fun u : Fin 1 → R => (fun _ : Fin 1 => 2 * u 0 + 0))
        = polynomialMap (fun _ : Fin 1 => 2 * MvPolynomial.X 0 + MvPolynomial.C 0) := by
      funext u s
      simp only [polynomialMap, map_add, map_mul, map_ofNat, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
    rw [heq]; exact continuous_polynomialMap _
  have hcontr₂ : Continuous (fun u : Fin 1 → R => (fun _ : Fin 1 => 2 * u 0 + (-1))) := by
    have heq : (fun u : Fin 1 → R => (fun _ : Fin 1 => 2 * u 0 + (-1)))
        = polynomialMap (fun _ : Fin 1 => 2 * MvPolynomial.X 0 + MvPolynomial.C (-1)) := by
      funext u s
      simp only [polynomialMap, map_add, map_mul, map_ofNat, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
    rw [heq]; exact continuous_polynomialMap _
  have hcontγ₁ : ContinuousOn γ₁ H₁ := by
    rw [hγ₁]
    refine (continuous_chartMap 0).comp_continuousOn (hsymm.comp_continuousOn ?_)
    rw [hψ₁]
    exact hc₁.comp hcontr₁.continuousOn hr₁maps
  have hcontγ₂ : ContinuousOn γ₂ H₂ := by
    rw [hγ₂]
    refine (continuous_chartMap 1).comp_continuousOn (hsymm.comp_continuousOn ?_)
    rw [hψ₂]
    exact hc₂.comp hcontr₂.continuousOn hr₂maps
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    rw [hunion]
    exact ContinuousOn.union_of_isClosed
      (hcontγ₁.congr hγeq₁) (hcontγ₂.congr hγeq₂)
      (isClosed_Icc_local _ _) (isClosed_Icc_local _ _)
  · -- γ 0 = (1:0)
    have h0 : ((0 : Fin 1 → R)) ∈ H₁ := by rw [hH₁mem]; show 0 ≤ (0:R) ∧ (0:R) ≤ 1/2; norm_num
    rw [hγeq₁ _ h0, hγ₁]
    show chartMap 0 (realEquiv.symm (ψ₁ 0)) = pencilPt10
    have hψ0 : ψ₁ (0 : Fin 1 → R) = ϕ₁ 0 := by
      have : (fun _ : Fin 1 => 2 * (0 : Fin 1 → R) 0 + 0) = (0 : Fin 1 → R) := by
        funext s; simp only [Pi.zero_apply]; norm_num
      rw [hψ₁]; show ϕ₁ (fun _ : Fin 1 => 2 * (0 : Fin 1 → R) 0 + 0) = ϕ₁ 0; rw [this]
    rw [hψ0, hs₁, Equiv.symm_apply_apply]
    exact chartMap_chartInv 0 _ (by rw [chartSet_eq] at hx10; exact hx10)
  · -- γ 1 = (0:1)
    have h1 : ((1 : Fin 1 → R)) ∈ H₂ := by rw [hH₂mem]; show 1/2 ≤ (1:R) ∧ (1:R) ≤ 1; norm_num
    rw [hγeq₂ _ h1, hγ₂]
    show chartMap 1 (realEquiv.symm (ψ₂ 1)) = pencilPt01
    have hψ1 : ψ₂ (1 : Fin 1 → R) = ϕ₂ 1 := by
      have : (fun _ : Fin 1 => 2 * (1 : Fin 1 → R) 0 + (-1)) = (1 : Fin 1 → R) := by
        funext s; simp only [Pi.one_apply]; norm_num
      rw [hψ₂]; show ϕ₂ (fun _ : Fin 1 => 2 * (1 : Fin 1 → R) 0 + (-1)) = ϕ₂ 1; rw [this]
    rw [hψ1, ht₂, Equiv.symm_apply_apply]
    exact chartMap_chartInv 1 _ (by rw [chartSet_eq] at hy01; exact hy01)
  · -- interior (0,1] avoids Δ
    intro w hw
    rw [mem_intervalSet] at hw
    obtain ⟨hw0, hw1⟩ := hw
    have hwIcc : w ∈ Set.Icc (0 : Fin 1 → R) 1 := by
      rw [show (0 : Fin 1 → R) = constPt 0 from rfl, show (1 : Fin 1 → R) = constPt 1 from rfl,
        mem_Icc_fin_one_local]
      exact ⟨hw0.le, hw1⟩
    rw [hunion] at hwIcc
    rw [← hΔcoe]
    rcases hwIcc with hu | hu
    · -- first (half-open) half
      rw [hγeq₁ w hu, hγ₁]
      have hmaps : (fun _ : Fin 1 => 2 * w 0 + 0) ∈ Set.Icc (0 : Fin 1 → R) 1 := hr₁maps w hu
      have hpos : 0 < ((fun _ : Fin 1 => 2 * w 0 + 0) : Fin 1 → R) 0 := by
        show 0 < 2 * w 0 + 0; linarith
      show chartMap 0 (realEquiv.symm (ψ₁ w)) ∉ (↑Δ : Set (complexProjectiveSpace R 1))
      rw [hψ₁]
      exact hav₁ (fun _ : Fin 1 => 2 * w 0 + 0) hmaps hpos
    · -- second (full) half
      rw [hγeq₂ w hu, hγ₂]
      show chartMap 1 (realEquiv.symm (ψ₂ w)) ∉ (↑Δ : Set (complexProjectiveSpace R 1))
      rw [hψ₂]
      exact hav₂ (fun _ : Fin 1 => 2 * w 0 + (-1)) (hr₂maps w hu)
  · -- semialgebraic graph
    set T : Set ((Fin 1 → R) × complexProjectiveSpace R 1) :=
      {tp | tp.1 ∈ Set.Icc 0 1 ∧ tp.2 = γ tp.1} with hT
    set T₁ : Set ((Fin 1 → R) × complexProjectiveSpace R 1) :=
      {tp | tp.1 ∈ H₁ ∧ tp.2 = chartMap 0 (realEquiv.symm (ψ₁ tp.1))} with hT₁
    set T₂ : Set ((Fin 1 → R) × complexProjectiveSpace R 1) :=
      {tp | tp.1 ∈ H₂ ∧ tp.2 = chartMap 1 (realEquiv.symm (ψ₂ tp.1))} with hT₂
    have hTeq : T = T₁ ∪ T₂ := by
      ext ⟨u, p⟩
      simp only [hT, hT₁, hT₂, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨huI, hp⟩
        rw [hunion, Set.mem_union] at huI
        rcases huI with hu | hu
        · exact Or.inl ⟨hu, by rw [hp]; exact hγeq₁ u hu⟩
        · exact Or.inr ⟨hu, by rw [hp]; exact hγeq₂ u hu⟩
      · rintro (⟨hu, hp⟩ | ⟨hu, hp⟩)
        · refine ⟨by rw [hunion]; exact Or.inl hu, ?_⟩
          rw [hp]; exact (hγeq₁ u hu).symm
        · refine ⟨by rw [hunion]; exact Or.inr hu, ?_⟩
          rw [hp]; exact (hγeq₂ u hu).symm
    rw [hTeq]
    refine IsSemialgebraicSetRP.union ?_ ?_
    · exact isSemialgebraicSetRP_chartMap_comp (D := H₁) 0
        (isSemialgebraicSet_funGraph_reparam hg₁ (isSemialgebraicSet_Icc_local _ _) 0 hr₁maps)
    · exact isSemialgebraicSetRP_chartMap_comp (D := H₂) 1
        (isSemialgebraicSet_funGraph_reparam hg₂ (isSemialgebraicSet_Icc_local _ _) (-1) hr₂maps)

/-! ### Gap (b): relative openness of `Pm m` in `(0,1]` -/

set_option linter.unusedSectionVars false in
/-- **Gap (b): `Pm m` is open in `(0,1]`.** At a parameter `w₀ ∈ Pm m` the value `γ(w₀)` lies off `Δ`,
so its `m` distinct common projective zeros `ys a` are each non-singular. The local implicit function
theorem (`homotopy_local_ift_chartV`) continues each `ys a` to a continuous map `ϕ_a` defined on a
chart-open neighborhood `U_a ∋ γ(w₀)`, with `ϕ_a(p)` a common zero of `S₍p₎` for `p ∈ U_a` and local
uniqueness. Shrinking the target neighborhoods `V_a` to be pairwise disjoint (Hausdorffness + the
injectivity of `ys`) keeps the continued zeros `ϕ_a(γ(w))` distinct. Pulling the `U_a` back along the
continuous `γ` produces a relatively open neighborhood of `w₀` on which `S₍γ(w)₎` retains `m` distinct
zeros, i.e. which lies in `Pm m`. -/
theorem pm_isOpenIn (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγcont : ContinuousOn γ (intervalSet (R := R)))
    (hγΔ : ∀ w ∈ intervalSet (R := R), γ w ∉ deltaSet P d) (m : ℕ) :
    IsOpenIn (intervalSet (R := R)) (Pm P d γ m) := by
  classical
  refine isOpenIn_of_forall_mem (Pm_subset_intervalSet P d γ m) (fun w₀ hw₀ => ?_)
  obtain ⟨hw₀I, ys, hysinj, hyszero⟩ := hw₀
  -- `γ w₀ ∉ Δ`
  have hw₀mem : w₀ ∈ intervalSet (R := R) := hw₀I
  have hγΔ₀ : γ w₀ ∉ deltaSet P d := hγΔ w₀ hw₀mem
  -- chart for `γ w₀`
  obtain ⟨i₀, hi₀⟩ := exists_mem_chartSet (γ w₀)
  -- for each `a`, apply the local IFT
  have hkey : ∀ a : Fin m, ∃ (U : Set (complexProjectiveSpace R 1))
      (V : Set (complexProjectiveSpace R k))
      (ϕ : complexProjectiveSpace R 1 → complexProjectiveSpace R k),
      IsOpen U ∧ γ w₀ ∈ U ∧ IsOpen V ∧ ys a ∈ V ∧ ϕ (γ w₀) = ys a ∧
      IsSClassMapP m U V ϕ ∧ (∀ q ∈ V, q ∈ chartSet (Classical.choose (exists_mem_chartSet (ys a)))) ∧
      (∀ p ∈ U, ∀ x ∈ V,
        ((∀ l, homotopyF P d i₀ (Classical.choose (exists_mem_chartSet (ys a))) l
            (Fin.append (realEquiv (chartInv i₀ p))
              (realEquiv (chartInv (Classical.choose (exists_mem_chartSet (ys a))) x))) = 0)
          ↔ x = ϕ p)) := by
    intro a
    set j₀ := Classical.choose (exists_mem_chartSet (ys a)) with hj₀
    have hxj₀ : ys a ∈ chartSet j₀ := Classical.choose_spec (exists_mem_chartSet (ys a))
    have hns : IsNonsingularProjectiveZero
        (homotopyPoly P d ((γ w₀).rep 0) ((γ w₀).rep 1)) (ys a) :=
      notMem_deltaSet_nonsingular P d (γ w₀) hγΔ₀ (ys a) (fun i => hyszero a i)
    obtain ⟨U, V, ϕ, hUopen, hw₀U, hVopen, hxV, hϕx₀, hϕclass, himpl, hVchart⟩ :=
      homotopy_local_ift_chartV m P d hP (γ w₀) (ys a) i₀ j₀ hi₀ hxj₀
        (fun i => hyszero a i) hns
    exact ⟨U, V, ϕ, hUopen, hw₀U, hVopen, hxV, hϕx₀, hϕclass, hVchart, himpl⟩
  choose U V ϕ hUopen hw₀U hVopen hxV hϕx₀ hϕclass hVchart himpl using hkey
  -- the chart index chosen for each `ys a`
  set j₀ : Fin m → Fin (k + 1) := fun a => Classical.choose (exists_mem_chartSet (ys a)) with hj₀
  -- `ϕ a` is continuous on `U a`
  have hϕcont : ∀ a, ContinuousOn (ϕ a) (U a) := fun a =>
    continuousOn_isSClassMapP (j₀ a) (hϕclass a) (hUopen a) (hVchart a)
  -- the continued zero `g a := ϕ a ∘ γ`, continuous within `intervalSet` at `w₀`
  set g : Fin m → (Fin 1 → R) → complexProjectiveSpace R k := fun a w => ϕ a (γ w) with hg
  have hgw₀ : ∀ a, g a w₀ = ys a := fun a => hϕx₀ a
  have hγU₀ : ∀ a, γ w₀ ∈ U a := hw₀U
  -- `g a` is `ContinuousWithinAt intervalSet w₀`
  have hgcont : ∀ a, ContinuousWithinAt (g a) (intervalSet (R := R)) w₀ := by
    intro a
    have hγcw : ContinuousWithinAt γ (intervalSet (R := R)) w₀ := hγcont w₀ hw₀mem
    have hϕcw : ContinuousWithinAt (ϕ a) (U a) (γ w₀) := (hϕcont a).continuousWithinAt (hγU₀ a)
    have hmaps : Set.MapsTo γ (intervalSet (R := R) ∩ γ ⁻¹' (U a)) (U a) :=
      fun w hw => hw.2
    have := hϕcw.comp (hγcw.mono (Set.inter_subset_left)) hmaps
    -- `this : ContinuousWithinAt (ϕ a ∘ γ) (intervalSet ∩ γ⁻¹ (U a)) w₀`; upgrade domain
    have hmem : intervalSet (R := R) ∩ γ ⁻¹' (U a) ∈ nhdsWithin w₀ (intervalSet (R := R)) := by
      refine Filter.inter_mem self_mem_nhdsWithin ?_
      exact hγcw.preimage_mem_nhdsWithin ((hUopen a).mem_nhds (hγU₀ a))
    exact (this.mono_of_mem_nhdsWithin hmem)
  -- Step 1: open neighborhood `O a` of `w₀` with `O a ∩ intervalSet ⊆ γ⁻¹ (U a)`
  have hO : ∀ a, ∃ O : Set (Fin 1 → R), IsOpen O ∧ w₀ ∈ O ∧
      O ∩ intervalSet (R := R) ⊆ γ ⁻¹' (U a) := by
    intro a
    have hpre : γ ⁻¹' (U a) ∈ nhdsWithin w₀ (intervalSet (R := R)) :=
      (hγcont w₀ hw₀mem).preimage_mem_nhdsWithin ((hUopen a).mem_nhds (hγU₀ a))
    rw [mem_nhdsWithin] at hpre
    obtain ⟨O, hOopen, hw₀O, hOsub⟩ := hpre
    exact ⟨O, hOopen, hw₀O, hOsub⟩
  choose O hOopen hw₀O hOsub using hO
  -- Step 2: open neighborhood `O' a b` of `w₀` with `g a ≠ g b` on `O' a b ∩ intervalSet` (a ≠ b)
  have hO' : ∀ a b : Fin m, a ≠ b → ∃ O' : Set (Fin 1 → R), IsOpen O' ∧ w₀ ∈ O' ∧
      O' ∩ intervalSet (R := R) ⊆ {w | g a w ≠ g b w} := by
    intro a b hab
    -- `g a w₀ = ys a ≠ ys b = g b w₀`; separate by disjoint opens and pull back
    obtain ⟨Wa, Wb, hWao, hWbo, hWam, hWbm, hWdisj⟩ := t2_separation (hysinj.ne hab)
    have hga : g a w₀ ∈ Wa := by rw [hgw₀]; exact hWam
    have hgb : g b w₀ ∈ Wb := by rw [hgw₀]; exact hWbm
    have hpa : g a ⁻¹' Wa ∈ nhdsWithin w₀ (intervalSet (R := R)) :=
      (hgcont a).preimage_mem_nhdsWithin (hWao.mem_nhds hga)
    have hpb : g b ⁻¹' Wb ∈ nhdsWithin w₀ (intervalSet (R := R)) :=
      (hgcont b).preimage_mem_nhdsWithin (hWbo.mem_nhds hgb)
    have hpab := Filter.inter_mem hpa hpb
    rw [mem_nhdsWithin] at hpab
    obtain ⟨O', hO'open, hw₀O', hO'sub⟩ := hpab
    refine ⟨O', hO'open, hw₀O', ?_⟩
    intro w hw
    have hwin : w ∈ O' ∩ intervalSet (R := R) := hw
    have := hO'sub hwin
    simp only [Set.mem_inter_iff, Set.mem_preimage] at this
    intro hcontra
    exact (hWdisj.ne_of_mem this.1 (hcontra ▸ this.2)) rfl
  -- assemble `V := (⋂_a O a) ∩ (⋂_{a≠b} O' a b)`
  -- choose the `O'` data
  set bad : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 ≠ p.2) with hbad
  have hO'data : ∀ p ∈ bad, ∃ O' : Set (Fin 1 → R), IsOpen O' ∧ w₀ ∈ O' ∧
      O' ∩ intervalSet (R := R) ⊆ {w | g p.1 w ≠ g p.2 w} := by
    intro p hp
    rw [hbad, Finset.mem_filter] at hp
    exact hO' p.1 p.2 hp.2
  choose! O' hO'open hw₀O' hO'sub using hO'data
  -- Step 3: open neighborhood `O0` of `w₀` with `γ w ∈ chartSet i₀` on `O0 ∩ intervalSet`
  obtain ⟨O0, hO0open, hw₀O0, hO0sub⟩ : ∃ O0 : Set (Fin 1 → R), IsOpen O0 ∧ w₀ ∈ O0 ∧
      O0 ∩ intervalSet (R := R) ⊆ γ ⁻¹' (chartSet i₀) := by
    have hpre : γ ⁻¹' (chartSet i₀) ∈ nhdsWithin w₀ (intervalSet (R := R)) :=
      (hγcont w₀ hw₀mem).preimage_mem_nhdsWithin ((isOpen_chartSet i₀).mem_nhds hi₀)
    rw [mem_nhdsWithin] at hpre
    obtain ⟨O0, hO0open, hw₀O0, hO0sub⟩ := hpre
    exact ⟨O0, hO0open, hw₀O0, hO0sub⟩
  set Vfin : Set (Fin 1 → R) :=
    O0 ∩ (⋂ a : Fin m, O a) ∩ (⋂ p ∈ bad, O' p) with hVfin
  have hVfinopen : IsOpen Vfin := by
    refine IsOpen.inter (IsOpen.inter hO0open (isOpen_iInter_of_finite hOopen)) ?_
    exact isOpen_biInter_finset (fun p hp => hO'open p hp)
  have hw₀Vfin : w₀ ∈ Vfin := by
    refine ⟨⟨hw₀O0, Set.mem_iInter.mpr (fun a => hw₀O a)⟩, ?_⟩
    rw [Set.mem_iInter₂]; exact fun p hp => hw₀O' p hp
  refine ⟨Vfin, hVfinopen, hw₀Vfin, ?_⟩
  -- show `Vfin ∩ intervalSet ⊆ Pm m`
  rintro w ⟨hwV, hwI⟩
  refine ⟨hwI, ?_⟩
  -- `γ w ∈ chartSet i₀`
  have hγwi₀ : γ w ∈ chartSet i₀ := hO0sub ⟨hwV.1.1, hwI⟩
  -- the continued zeros at `w`
  have hwU : ∀ a, γ w ∈ U a := by
    intro a
    have : w ∈ O a ∩ intervalSet (R := R) :=
      ⟨Set.mem_iInter.mp hwV.1.2 a, hwI⟩
    exact hOsub a this
  refine ⟨fun a => ϕ a (γ w), ?_, ?_⟩
  · -- injectivity from the `O'` distinctness constraints
    intro a b hab
    have hcontra : ϕ a (γ w) = ϕ b (γ w) := hab
    by_cases hab' : a = b
    · exact hab'
    · exfalso
      have hpbad : (a, b) ∈ bad := by
        rw [hbad, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hab'⟩
      have hwO' : w ∈ O' (a, b) ∩ intervalSet (R := R) :=
        ⟨(Set.mem_iInter₂.mp hwV.2) (a, b) hpbad, hwI⟩
      have := hO'sub (a, b) hpbad hwO'
      simp only [Set.mem_setOf_eq] at this
      exact this hcontra
  · -- each `ϕ a (γ w)` is a common zero of `S₍γ w₎`
    intro a i
    set j := j₀ a with hjdef
    have hxVa : ϕ a (γ w) ∈ V a := (hϕclass a).1 (hwU a)
    -- `ϕ a (γ w) ∈ chartSet j`
    have hxchart : ϕ a (γ w) ∈ chartSet j := hVchart a (ϕ a (γ w)) hxVa
    -- the iff gives the coordinate-vanishing; convert via the bridge
    have hiff := himpl a (γ w) (hwU a) (ϕ a (γ w)) hxVa
    have hcoord : ∀ l, homotopyF P d i₀ j l
        (Fin.append (realEquiv (chartInv i₀ (γ w)))
          (realEquiv (chartInv j (ϕ a (γ w))))) = 0 := hiff.mpr rfl
    -- convert coordinate-vanishing to `aeval`-vanishing via the chart bridge
    have := (homotopyF_eq_zero_iff P d hP i₀ j (γ w) (ϕ a (γ w)) hγwi₀ hxchart).mp hcoord
    exact this i

/-! ### Gap (step 6): the local injection of finitely many zeros near `(1:0)` -/

set_option linter.unusedSectionVars false in
/-- **Local injection at the `(1:0)` endpoint.** Every finite set `F` of non-singular projective zeros
of `P = S₍₁:₀₎` continues, by finitely many applications of the local implicit function theorem at the
endpoint `γ(0) = (1:0)`, to `F.card` distinct common projective zeros of the pencil `S₍γ(w)₎` for a
single parameter `w ∈ (0,1]` close to `0`. -/
theorem pm_local_inject (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγcont : ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1))
    (hγ0 : γ (0 : Fin 1 → R) = pencilPt10 (R := R)) (_hone : (1 : Fin 1 → R) 0 = 1)
    (F : Finset (complexProjectiveSpace R k))
    (hF : (↑F : Set (complexProjectiveSpace R k)) ⊆ {x | IsNonsingularProjectiveZero P x}) :
    ∃ w : Fin 1 → R, w ∈ intervalSet (R := R) ∧ AtLeastZeros P d (γ w) F.card := by
  classical
  -- index `F` by `Fin F.card`
  obtain ⟨e⟩ := (Fintype.truncEquivFinOfCardEq (Fintype.card_coe F)).nonempty
  set xs : Fin F.card → complexProjectiveSpace R k := fun a => (e.symm a : complexProjectiveSpace R k)
    with hxs
  have hxsinj : Function.Injective xs := by
    intro a b hab
    have : e.symm a = e.symm b := Subtype.ext hab
    exact e.symm.injective this
  have hxsns : ∀ a, IsNonsingularProjectiveZero P (xs a) := by
    intro a; exact hF (e.symm a).2
  -- `0 ∈ Icc 0 1` and `pencilPt10` chart
  have h0mem : (0 : Fin 1 → R) ∈ Set.Icc (0 : Fin 1 → R) 1 := by
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, one_eq_constPt, mem_Icc_fin_one_local]
    exact ⟨le_refl _, zero_le_one⟩
  obtain ⟨i₀, hi₀⟩ := exists_mem_chartSet (pencilPt10 (R := R))
  rw [← hγ0] at hi₀
  -- apply the local IFT to each `xs a`, viewing it as a non-singular zero of the pencil at `(1:0)`
  have hkey : ∀ a : Fin F.card, ∃ (U : Set (complexProjectiveSpace R 1))
      (V : Set (complexProjectiveSpace R k))
      (ϕ : complexProjectiveSpace R 1 → complexProjectiveSpace R k),
      IsOpen U ∧ γ (0 : Fin 1 → R) ∈ U ∧ IsOpen V ∧ xs a ∈ V ∧ ϕ (γ (0 : Fin 1 → R)) = xs a ∧
      IsSClassMapP F.card U V ϕ ∧
      (∀ q ∈ V, q ∈ chartSet (Classical.choose (exists_mem_chartSet (xs a)))) ∧
      (∀ p ∈ U, ∀ x ∈ V,
        ((∀ l, homotopyF P d i₀ (Classical.choose (exists_mem_chartSet (xs a))) l
            (Fin.append (realEquiv (chartInv i₀ p))
              (realEquiv (chartInv (Classical.choose (exists_mem_chartSet (xs a))) x))) = 0)
          ↔ x = ϕ p)) := by
    intro a
    set j₀ := Classical.choose (exists_mem_chartSet (xs a)) with hj₀
    have hxj₀ : xs a ∈ chartSet j₀ := Classical.choose_spec (exists_mem_chartSet (xs a))
    -- `xs a` is a non-singular zero of the pencil at `(1:0)`
    have hns0 : IsNonsingularProjectiveZero
        (homotopyPoly P d ((pencilPt10 (R := R)).rep 0) ((pencilPt10 (R := R)).rep 1)) (xs a) :=
      isNonsingular_pencilPt10_of_isNonsingular P d (xs a) (hxsns a)
    have hzero0 : ∀ i, aeval (xs a).rep
        (homotopyPoly P d ((pencilPt10 (R := R)).rep 0) ((pencilPt10 (R := R)).rep 1) i) = 0 :=
      hns0.1
    obtain ⟨U, V, ϕ, hUopen, hpU, hVopen, hxV, hϕx₀, hϕclass, himpl, hVchart⟩ :=
      homotopy_local_ift_chartV F.card P d hP (pencilPt10 (R := R)) (xs a) i₀ j₀
        (by rw [hγ0] at hi₀; exact hi₀) hxj₀ hzero0 hns0
    refine ⟨U, V, ϕ, hUopen, by rw [hγ0]; exact hpU, hVopen, hxV, by rw [hγ0]; exact hϕx₀,
      hϕclass, hVchart, himpl⟩
  choose U V ϕ hUopen hpU hVopen hxV hϕx₀ hϕclass hVchart himpl using hkey
  set j₀ : Fin F.card → Fin (k + 1) := fun a => Classical.choose (exists_mem_chartSet (xs a))
    with hj₀
  have hϕcont : ∀ a, ContinuousOn (ϕ a) (U a) := fun a =>
    continuousOn_isSClassMapP (j₀ a) (hϕclass a) (hUopen a) (hVchart a)
  set g : Fin F.card → (Fin 1 → R) → complexProjectiveSpace R k := fun a w => ϕ a (γ w) with hg
  have hgw₀ : ∀ a, g a (0 : Fin 1 → R) = xs a := fun a => hϕx₀ a
  -- `g a` is `ContinuousWithinAt (Icc 0 1) 0`
  have hgcont : ∀ a, ContinuousWithinAt (g a) (Set.Icc (0 : Fin 1 → R) 1) (0 : Fin 1 → R) := by
    intro a
    have hγcw : ContinuousWithinAt γ (Set.Icc (0 : Fin 1 → R) 1) (0 : Fin 1 → R) :=
      hγcont (0 : Fin 1 → R) h0mem
    have hϕcw : ContinuousWithinAt (ϕ a) (U a) (γ (0 : Fin 1 → R)) :=
      (hϕcont a).continuousWithinAt (hpU a)
    have hmaps : Set.MapsTo γ (Set.Icc (0 : Fin 1 → R) 1 ∩ γ ⁻¹' (U a)) (U a) :=
      fun w hw => hw.2
    have hcomp := hϕcw.comp (hγcw.mono (Set.inter_subset_left)) hmaps
    have hmem : Set.Icc (0 : Fin 1 → R) 1 ∩ γ ⁻¹' (U a)
        ∈ nhdsWithin (0 : Fin 1 → R) (Set.Icc (0 : Fin 1 → R) 1) := by
      refine Filter.inter_mem self_mem_nhdsWithin ?_
      exact hγcw.preimage_mem_nhdsWithin ((hUopen a).mem_nhds (hpU a))
    exact hcomp.mono_of_mem_nhdsWithin hmem
  -- Step 1: open `O a ∋ 0` with `O a ∩ Icc 0 1 ⊆ γ⁻¹ (U a)`
  have hO : ∀ a, ∃ O : Set (Fin 1 → R), IsOpen O ∧ (0 : Fin 1 → R) ∈ O ∧
      O ∩ Set.Icc (0 : Fin 1 → R) 1 ⊆ γ ⁻¹' (U a) := by
    intro a
    have hpre : γ ⁻¹' (U a) ∈ nhdsWithin (0 : Fin 1 → R) (Set.Icc (0 : Fin 1 → R) 1) :=
      (hγcont (0 : Fin 1 → R) h0mem).preimage_mem_nhdsWithin ((hUopen a).mem_nhds (hpU a))
    rw [mem_nhdsWithin] at hpre
    obtain ⟨O, hOopen, h0O, hOsub⟩ := hpre
    exact ⟨O, hOopen, h0O, hOsub⟩
  choose O hOopen h0O hOsub using hO
  -- Step 2: open `O' a b ∋ 0` with `g a ≠ g b` on `O' a b ∩ Icc 0 1` (a ≠ b)
  set bad : Finset (Fin F.card × Fin F.card) := Finset.univ.filter (fun p => p.1 ≠ p.2) with hbad
  have hO' : ∀ p ∈ bad, ∃ O' : Set (Fin 1 → R), IsOpen O' ∧ (0 : Fin 1 → R) ∈ O' ∧
      O' ∩ Set.Icc (0 : Fin 1 → R) 1 ⊆ {w | g p.1 w ≠ g p.2 w} := by
    intro p hp
    rw [hbad, Finset.mem_filter] at hp
    obtain ⟨_, hab⟩ := hp
    obtain ⟨Wa, Wb, hWao, hWbo, hWam, hWbm, hWdisj⟩ := t2_separation (hxsinj.ne hab)
    have hga : g p.1 (0 : Fin 1 → R) ∈ Wa := by rw [hgw₀]; exact hWam
    have hgb : g p.2 (0 : Fin 1 → R) ∈ Wb := by rw [hgw₀]; exact hWbm
    have hpa : g p.1 ⁻¹' Wa ∈ nhdsWithin (0 : Fin 1 → R) (Set.Icc (0 : Fin 1 → R) 1) :=
      (hgcont p.1).preimage_mem_nhdsWithin (hWao.mem_nhds hga)
    have hpb : g p.2 ⁻¹' Wb ∈ nhdsWithin (0 : Fin 1 → R) (Set.Icc (0 : Fin 1 → R) 1) :=
      (hgcont p.2).preimage_mem_nhdsWithin (hWbo.mem_nhds hgb)
    have hpab := Filter.inter_mem hpa hpb
    rw [mem_nhdsWithin] at hpab
    obtain ⟨O', hO'open, h0O', hO'sub⟩ := hpab
    refine ⟨O', hO'open, h0O', ?_⟩
    intro w hw
    have := hO'sub hw
    simp only [Set.mem_inter_iff, Set.mem_preimage] at this
    intro hcontra
    exact (hWdisj.ne_of_mem this.1 (hcontra ▸ this.2)) rfl
  choose! O' hO'open h0O' hO'sub using hO'
  -- Step 3: open `O0 ∋ 0` with `γ w ∈ chartSet i₀` on `O0 ∩ Icc 0 1`
  obtain ⟨O0, hO0open, h0O0, hO0sub⟩ : ∃ O0 : Set (Fin 1 → R), IsOpen O0 ∧ (0 : Fin 1 → R) ∈ O0 ∧
      O0 ∩ Set.Icc (0 : Fin 1 → R) 1 ⊆ γ ⁻¹' (chartSet i₀) := by
    have hpre : γ ⁻¹' (chartSet i₀) ∈ nhdsWithin (0 : Fin 1 → R) (Set.Icc (0 : Fin 1 → R) 1) :=
      (hγcont (0 : Fin 1 → R) h0mem).preimage_mem_nhdsWithin
        ((isOpen_chartSet i₀).mem_nhds (by rw [hγ0] at hi₀ ⊢; exact hi₀))
    rw [mem_nhdsWithin] at hpre
    obtain ⟨O0, hO0open, h0O0, hO0sub⟩ := hpre
    exact ⟨O0, hO0open, h0O0, hO0sub⟩
  -- assemble the open neighborhood `Ofin ∋ 0`
  set Ofin : Set (Fin 1 → R) :=
    O0 ∩ (⋂ a : Fin F.card, O a) ∩ (⋂ p ∈ bad, O' p) with hOfin
  have hOfinopen : IsOpen Ofin :=
    IsOpen.inter (IsOpen.inter hO0open (isOpen_iInter_of_finite hOopen))
      (isOpen_biInter_finset (fun p hp => hO'open p hp))
  have h0Ofin : (0 : Fin 1 → R) ∈ Ofin := by
    refine ⟨⟨h0O0, Set.mem_iInter.mpr (fun a => h0O a)⟩, ?_⟩
    rw [Set.mem_iInter₂]; exact fun p hp => h0O' p hp
  -- find a point `w ∈ Ofin ∩ intervalSet` (`0` is in the closure of `(0,1]`)
  obtain ⟨r, hr, hrsub⟩ := mem_nhds_iff_openBall.mp (hOfinopen.mem_nhds h0Ofin)
  set s := min r 1 / 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hsr : s < r := by
    rw [hsdef]; have : min r 1 ≤ r := min_le_left _ _; nlinarith [min_le_right r (1 : R), hr]
  have hs1 : s ≤ 1 := by
    rw [hsdef]; have h1 : min r 1 ≤ 1 := min_le_right _ _; nlinarith
  set w : Fin 1 → R := constPt s with hw
  have hwball : w ∈ openBall (0 : Fin 1 → R) r := by
    rw [mem_openBall_iff_norm hr]
    have : (w - 0 : Fin 1 → R) = constPt s := by rw [sub_zero]
    rw [this, euclideanNorm_fin_one]
    show |s| < r
    rw [abs_of_pos hs0]; exact hsr
  have hwOfin : w ∈ Ofin := hrsub hwball
  have hwI : w ∈ intervalSet (R := R) := by
    rw [mem_intervalSet]; exact ⟨hs0, hs1⟩
  have hw0 : w 0 = s := rfl
  have hwIcc : w ∈ Set.Icc (0 : Fin 1 → R) 1 := by
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, one_eq_constPt, mem_Icc_fin_one_local]
    exact ⟨by rw [hw0]; exact hs0.le, by rw [hw0]; exact hs1⟩
  -- `γ w ∈ chartSet i₀`
  have hγwi₀ : γ w ∈ chartSet i₀ := hO0sub ⟨hwOfin.1.1, hwIcc⟩
  -- `γ w ∈ U a`
  have hwU : ∀ a, γ w ∈ U a := by
    intro a
    exact hOsub a ⟨Set.mem_iInter.mp hwOfin.1.2 a, hwIcc⟩
  -- the witness
  refine ⟨w, hwI, fun a => ϕ a (γ w), ?_, fun a i => ?_⟩
  · -- injectivity
    intro a b hab
    have hcontra : ϕ a (γ w) = ϕ b (γ w) := hab
    by_cases hab' : a = b
    · exact hab'
    · exfalso
      have hpbad : (a, b) ∈ bad := by
        rw [hbad, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hab'⟩
      have := hO'sub (a, b) hpbad ⟨(Set.mem_iInter₂.mp hwOfin.2) (a, b) hpbad, hwIcc⟩
      simp only [Set.mem_setOf_eq] at this
      exact this hcontra
  · -- each `ϕ a (γ w)` is a common zero of `S₍γ w₎`
    set j := j₀ a with hjdef
    have hxVa : ϕ a (γ w) ∈ V a := (hϕclass a).1 (hwU a)
    have hxchart : ϕ a (γ w) ∈ chartSet j := hVchart a (ϕ a (γ w)) hxVa
    have hiff := himpl a (γ w) (hwU a) (ϕ a (γ w)) hxVa
    have hcoord : ∀ l, homotopyF P d i₀ j l
        (Fin.append (realEquiv (chartInv i₀ (γ w)))
          (realEquiv (chartInv j (ϕ a (γ w))))) = 0 := hiff.mpr rfl
    exact (homotopyF_eq_zero_iff P d hP i₀ j (γ w) (ϕ a (γ w)) hγwi₀ hxchart).mp hcoord i

/-! ### The graph hypothesis from the half-open path -/

set_option linter.unusedSectionVars false in
/-- The mixed real–projective graph hypothesis consumed by `isSemialgebraicSet_Pm_of_atLeastZerosRP`,
recast from a semialgebraic graph of `γ` over `[0,1]`. -/
theorem hgraph_of_path (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hgraphRP : IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1}) :
    IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1} :=
  hgraphRP

/-! ### Assembly modulo the path and closedness -/

set_option linter.unusedSectionVars false in
/-- **Weak Bézout modulo the deformation path and relative closedness.** Given a half-open deformation
path `γ` (continuous on `[0,1]`, landing at the endpoints `(1:0)` and `(0:1)`, with semialgebraic
graph and interior `(0,1]` avoiding `Δ`) together with the relative closedness of `Pm m` in `(0,1]`
(gap (c)), the weak Bézout bound follows by combining the openness gap (b), the local injection at
`(1:0)`, the semialgebraicity of `Pm m`, and the clopen-dichotomy connectedness core
`uniform_zero_bound_of_clopen` + `weakBezout_of_uniform_bound`. -/
theorem weakBezout_modulo_gamma_and_closed (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (hsaAZ : ∀ m, IsSemialgebraicSetRP (atLeastZerosRP P d m))
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγcont01 : ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1))
    (hγ0 : γ (0 : Fin 1 → R) = pencilPt10 (R := R))
    (hγ1 : γ (1 : Fin 1 → R) = pencilPt01 (R := R))
    (hγΔ : ∀ w ∈ intervalSet (R := R), γ w ∉ deltaSet P d)
    (hgraphRP : IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1})
    (hclosed : ∀ m, IsClosedIn (intervalSet (R := R)) (Pm P d γ m)) :
    {x : complexProjectiveSpace R k | IsNonsingularProjectiveZero P x}.ncard ≤ ∏ i, d i := by
  have hone : (1 : Fin 1 → R) 0 = 1 := rfl
  -- `γ` is continuous on `(0,1] ⊆ [0,1]`
  have hIsub : intervalSet (R := R) ⊆ Set.Icc (0 : Fin 1 → R) 1 := by
    intro w hw
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, one_eq_constPt, mem_Icc_fin_one_local]
    rw [mem_intervalSet] at hw
    exact ⟨hw.1.le, hw.2⟩
  have hγcontI : ContinuousOn γ (intervalSet (R := R)) := hγcont01.mono hIsub
  -- `Pm m` is semialgebraic
  have hsa : ∀ m, IsSemialgebraicSet (Pm P d γ m) := fun m =>
    isSemialgebraicSet_Pm_of_atLeastZerosRP P d γ m hgraphRP (hsaAZ m)
  -- `Pm m` is open in `(0,1]` (gap (b))
  have hopen : ∀ m, IsOpenIn (intervalSet (R := R)) (Pm P d γ m) := fun m =>
    pm_isOpenIn P d hP γ hγcontI hγΔ m
  -- uniform zero bound (steps 4+5)
  have huniform := uniform_zero_bound_of_clopen P d hd γ hγ1 hone hsa hopen hclosed
  -- local injection at `(1:0)` (step 6)
  refine weakBezout_of_uniform_bound P d γ huniform (fun F hF => ?_)
  exact pm_local_inject P d hP γ hγcont01 hγ0 hone F hF

set_option linter.unusedSectionVars false in
/-- **Finite-subset form of `weakBezout_modulo_gamma_and_closed`.** Under the same hypotheses, every
finite set `F` of non-singular projective zeros of `P` has cardinality at most `∏ dᵢ`. -/
theorem weakBezout_finsetCard_modulo_gamma_and_closed
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (hsaAZ : ∀ m, IsSemialgebraicSetRP (atLeastZerosRP P d m))
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγcont01 : ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1))
    (hγ0 : γ (0 : Fin 1 → R) = pencilPt10 (R := R))
    (hγ1 : γ (1 : Fin 1 → R) = pencilPt01 (R := R))
    (hγΔ : ∀ w ∈ intervalSet (R := R), γ w ∉ deltaSet P d)
    (hgraphRP : IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1})
    (hclosed : ∀ m, IsClosedIn (intervalSet (R := R)) (Pm P d γ m)) :
    ∀ F : Finset (complexProjectiveSpace R k),
      (↑F : Set (complexProjectiveSpace R k)) ⊆ {x | IsNonsingularProjectiveZero P x} →
      F.card ≤ ∏ i, d i := by
  have hone : (1 : Fin 1 → R) 0 = 1 := rfl
  have hIsub : intervalSet (R := R) ⊆ Set.Icc (0 : Fin 1 → R) 1 := by
    intro w hw
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, one_eq_constPt, mem_Icc_fin_one_local]
    rw [mem_intervalSet] at hw
    exact ⟨hw.1.le, hw.2⟩
  have hγcontI : ContinuousOn γ (intervalSet (R := R)) := hγcont01.mono hIsub
  have hsa : ∀ m, IsSemialgebraicSet (Pm P d γ m) := fun m =>
    isSemialgebraicSet_Pm_of_atLeastZerosRP P d γ m hgraphRP (hsaAZ m)
  have hopen : ∀ m, IsOpenIn (intervalSet (R := R)) (Pm P d γ m) := fun m =>
    pm_isOpenIn P d hP γ hγcontI hγΔ m
  have huniform := uniform_zero_bound_of_clopen P d hd γ hγ1 hone hsa hopen hclosed
  refine weakBezout_finsetCard_of_uniform_bound P d γ huniform (fun F hF => ?_)
  exact pm_local_inject P d hP γ hγcont01 hγ0 hone F hF

/-! ### Reduction to the single remaining analytic input (gap (c)) -/

set_option linter.unusedSectionVars false in
/-- **Weak Bézout, reduced to relative closedness of `Pm m` (gap (c)).** Combining the half-open
deformation path `γ` (gap (a), `exists_halfopen_gammaPath`) with the openness gap (b) and the local
injection at `(1:0)`, the weak Bézout bound follows from the single remaining analytic input: the
relative closedness, in `(0,1]`, of the parameter sets `Pm P d γ m` for the canonical path
`γ` produced by `exists_halfopen_gammaPath`. -/
theorem weakBezout_of_sa_of_closed (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (hsaAZ : ∀ m, IsSemialgebraicSetRP (atLeastZerosRP P d m))
    (hclosed : ∀ (γ : (Fin 1 → R) → complexProjectiveSpace R 1),
      ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1) →
      γ (0 : Fin 1 → R) = pencilPt10 (R := R) →
      γ (1 : Fin 1 → R) = pencilPt01 (R := R) →
      (∀ w ∈ intervalSet (R := R), γ w ∉ deltaSet P d) →
      IsSemialgebraicSetRP
        {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
          tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1} →
      ∀ m, IsClosedIn (intervalSet (R := R)) (Pm P d γ m)) :
    {x : complexProjectiveSpace R k | IsNonsingularProjectiveZero P x}.ncard ≤ ∏ i, d i := by
  obtain ⟨γ, hγcont01, hγ0, hγ1, hγΔ, hgraphRP⟩ := exists_halfopen_gammaPath P d hd hP
  exact weakBezout_modulo_gamma_and_closed P d hd hP hsaAZ γ hγcont01 hγ0 hγ1 hγΔ hgraphRP
    (hclosed γ hγcont01 hγ0 hγ1 hγΔ hgraphRP)

set_option linter.unusedSectionVars false in
/-- **Finite-subset form of `weakBezout_of_sa_of_closed`.** Under the same hypotheses, every finite
set `F` of non-singular projective zeros of `P` has cardinality at most `∏ dᵢ`. -/
theorem weakBezout_finsetCard_of_sa_of_closed (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (hsaAZ : ∀ m, IsSemialgebraicSetRP (atLeastZerosRP P d m))
    (hclosed : ∀ (γ : (Fin 1 → R) → complexProjectiveSpace R 1),
      ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1) →
      γ (0 : Fin 1 → R) = pencilPt10 (R := R) →
      γ (1 : Fin 1 → R) = pencilPt01 (R := R) →
      (∀ w ∈ intervalSet (R := R), γ w ∉ deltaSet P d) →
      IsSemialgebraicSetRP
        {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
          tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1} →
      ∀ m, IsClosedIn (intervalSet (R := R)) (Pm P d γ m)) :
    ∀ F : Finset (complexProjectiveSpace R k),
      (↑F : Set (complexProjectiveSpace R k)) ⊆ {x | IsNonsingularProjectiveZero P x} →
      F.card ≤ ∏ i, d i := by
  obtain ⟨γ, hγcont01, hγ0, hγ1, hγΔ, hgraphRP⟩ := exists_halfopen_gammaPath P d hd hP
  exact weakBezout_finsetCard_modulo_gamma_and_closed P d hd hP hsaAZ γ hγcont01 hγ0 hγ1 hγΔ
    hgraphRP (hclosed γ hγcont01 hγ0 hγ1 hγΔ hgraphRP)

end Azurite.BPR.Chapter4
