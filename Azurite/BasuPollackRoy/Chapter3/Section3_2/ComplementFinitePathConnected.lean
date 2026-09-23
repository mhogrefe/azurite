import Azurite.BasuPollackRoy.Chapter3.Section3_2.SemialgebraicallyPathConnected
import Azurite.BasuPollackRoy.Chapter3.Section3_2.Proposition_3_7
import Mathlib.GroupTheory.CosetCover

/-! # BPR §3.2 — the complement of a finite set is semialgebraically path connected

Over a real closed field `R`, for `k ≥ 2` the set `Rᵏ ∖ Δ` (with `Δ` finite) is
semialgebraically path connected. This is the affine building block for BPR Lemma 4.105.

Given `x, y ∉ Δ`, we produce a *detour point* `w ∉ Δ` such that the closed segments `[x, w]` and
`[w, y]` both avoid `Δ`, then route `x → w → y` by a piecewise-linear (hence continuous and
semialgebraic) path.

The genericity step is the crux: the set of *bad* detour points is contained in a finite union of
affine lines (the lines through `x` and a point of `Δ`, and through `y` and a point of `Δ`) together
with the finitely many points of `Δ`. Each affine line in `Rᵏ` (`k ≥ 2`) and each point is a coset
of a *proper* `R`-subspace, and over the infinite field `R` a finite union of cosets of proper
subspaces cannot be all of `Rᵏ` (`coset_cover_proper_ne_univ`, from Mathlib's coset–cover theory). -/

namespace Azurite.BPR

open scoped Pointwise

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### A finite union of cosets of proper subspaces is not the whole space -/

omit [IsRealClosed R] in
/-- A proper subspace of a module over an infinite field has infinite quotient, hence does not have
finite index. -/
theorem not_finiteIndex_toAddSubgroup_of_ne_top
    {E : Type*} [AddCommGroup E] [Module R E] {W : Submodule R E} (hW : W ≠ ⊤) :
    ¬ W.toAddSubgroup.FiniteIndex := by
  rw [AddSubgroup.finiteIndex_iff]
  rw [Ne, AddSubgroup.index_eq_zero_iff_infinite, not_not]
  -- `R` embeds into `E ⧸ W`: pick `v ∉ W`, then `c ↦ ⟦c • v⟧` is injective.
  obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
    by_contra h
    push Not at h
    exact hW (eq_top_iff.mpr fun x _ => h x)
  have hinj : Function.Injective (fun c : R => (Submodule.Quotient.mk (c • v) : E ⧸ W)) := by
    intro c₁ c₂ hc
    simp only at hc
    rw [Submodule.Quotient.eq] at hc
    have : (c₁ - c₂) • v ∈ W := by rw [sub_smul]; exact hc
    by_contra hne
    apply hv
    have hc12 : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
    have := W.smul_mem (c₁ - c₂)⁻¹ this
    rwa [smul_smul, inv_mul_cancel₀ hc12, one_smul] at this
  exact Infinite.of_injective _ hinj

set_option linter.unusedSectionVars false in
/-- **A finite union of cosets of proper subspaces is not the whole space.** Over the infinite field
`R`, if each subspace `W i` is proper (`≠ ⊤`), then `⋃ i ∈ s, (g i +ᵥ W i)` cannot equal `Set.univ`.
-/
theorem coset_cover_proper_ne_univ
    {E : Type*} [AddCommGroup E] [Module R E] {ι : Type*} {s : Finset ι}
    {W : ι → Submodule R E} {g : ι → E} (hproper : ∀ i ∈ s, W i ≠ ⊤) :
    ⋃ i ∈ s, (g i +ᵥ (W i : Set E)) ≠ Set.univ := by
  intro hcov
  have hcov' : ⋃ i ∈ s, g i +ᵥ ((W i).toAddSubgroup : Set E) = Set.univ := by
    rw [← hcov]
    rfl
  obtain ⟨i, hi, hfi⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcov'
  exact not_finiteIndex_toAddSubgroup_of_ne_top (hproper i hi) hfi

/-! ### Genericity: a finite set of detour-obstruction lines does not cover `Rᵏ` -/

set_option linter.unusedSectionVars false in
/-- For `k ≥ 2`, the span of a single vector in `Rᵏ` is a proper subspace. -/
theorem span_singleton_ne_top (hk : 2 ≤ k) (v : Fin k → R) :
    Submodule.span R ({v} : Set (Fin k → R)) ≠ (⊤ : Submodule R (Fin k → R)) := by
  intro h
  have hrank : Module.finrank R (Fin k → R) = k := Module.finrank_fin_fun R
  rcases eq_or_ne v 0 with hv | hv
  · -- `span {0} = ⊥`, which is `⊤` only if the space is trivial; but `k ≥ 2`.
    rw [hv, Submodule.span_singleton_eq_bot.mpr rfl] at h
    have hb : Module.finrank R (⊥ : Submodule R (Fin k → R)) = 0 := finrank_bot R _
    rw [h, finrank_top, hrank] at hb
    omega
  · have h1 : Module.finrank R (Submodule.span R ({v} : Set (Fin k → R))) = 1 :=
      finrank_span_singleton hv
    rw [h, finrank_top, hrank] at h1
    omega

set_option linter.unusedSectionVars false in
/-- For `k ≥ 2`, the trivial subspace `⊥` of `Rᵏ` is proper. -/
theorem bot_ne_top (hk : 2 ≤ k) :
    (⊥ : Submodule R (Fin k → R)) ≠ (⊤ : Submodule R (Fin k → R)) := by
  intro h
  have hrank : Module.finrank R (Fin k → R) = k := Module.finrank_fin_fun R
  have hb : Module.finrank R (⊥ : Submodule R (Fin k → R)) = 0 := finrank_bot R _
  rw [h, finrank_top, hrank] at hb
  omega

/-- **Detour point.** For `k ≥ 2`, `x, y ∉ Δ`, there is a point `w ∉ Δ` such that no point of `Δ`
lies on the closed segment from `x` to `w` nor on the closed segment from `w` to `y`. (Segments are
described explicitly as `(1 - t) • a + t • b` with `t ∈ [0, 1]`.) -/
theorem exists_detour_point (hk : 2 ≤ k) (Δ : Finset (Fin k → R)) {x y : Fin k → R}
    (hx : x ∉ Δ) (hy : y ∉ Δ) :
    ∃ w : Fin k → R, w ∉ Δ ∧
      (∀ δ ∈ Δ, ∀ t : R, t ∈ Set.Icc (0 : R) 1 → δ ≠ (1 - t) • x + t • w) ∧
      (∀ δ ∈ Δ, ∀ t : R, t ∈ Set.Icc (0 : R) 1 → δ ≠ (1 - t) • w + t • y) := by
  classical
  -- The index set: three labeled copies of `Δ`.
  set s : Finset (Fin 3 × (Fin k → R)) := (Finset.univ : Finset (Fin 3)) ×ˢ Δ with hs
  -- Coset data: label 0 ↦ point δ; label 1 ↦ line through `x`; label 2 ↦ line through `y`.
  set Wf : Fin 3 × (Fin k → R) → Submodule R (Fin k → R) := fun p =>
    if p.1 = 0 then ⊥
    else if p.1 = 1 then Submodule.span R {p.2 - x}
    else Submodule.span R {p.2 - y} with hWf
  set gf : Fin 3 × (Fin k → R) → (Fin k → R) := fun p =>
    if p.1 = 0 then p.2 else if p.1 = 1 then x else y with hgf
  have hproper : ∀ p ∈ s, Wf p ≠ ⊤ := by
    intro p _
    simp only [hWf]
    split_ifs with h0 h1
    · exact bot_ne_top hk
    · exact span_singleton_ne_top hk _
    · exact span_singleton_ne_top hk _
  have hne : ⋃ p ∈ s, (gf p +ᵥ (Wf p : Set (Fin k → R))) ≠ Set.univ :=
    coset_cover_proper_ne_univ hproper
  -- pick `w` outside the cover.
  obtain ⟨w, hw⟩ : ∃ w, w ∉ ⋃ p ∈ s, (gf p +ᵥ (Wf p : Set (Fin k → R))) := by
    by_contra h
    push Not at h
    exact hne (Set.eq_univ_of_forall h)
  simp only [Set.mem_iUnion, not_exists] at hw
  -- now `hw p hp : w ∉ (gf p +ᵥ Wf p)`.
  refine ⟨w, ?_, ?_, ?_⟩
  · -- `w ∉ Δ`: else `w ∈ {w} = gf (0, w) +ᵥ ⊥`.
    intro hwΔ
    refine hw (0, w) (by rw [hs]; exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hwΔ⟩) ?_
    show w ∈ gf (0, w) +ᵥ (Wf (0, w) : Set (Fin k → R))
    have h1 : gf (0, w) = w := by rw [hgf]; simp
    have h2 : Wf (0, w) = ⊥ := by rw [hWf]; simp
    rw [h1, h2]
    exact ⟨0, Submodule.zero_mem _, by simp⟩
  · -- `[x, w]` avoids `Δ`: `δ = (1-t)x + tw`, `t ≠ 0` (else `δ = x`), so `w ∈ x +ᵥ span(δ-x)`.
    rintro δ hδ t ht heq
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp only [sub_zero, one_smul, zero_smul, add_zero] at heq
      exact hx (heq ▸ hδ)
    refine hw (1, δ) (by rw [hs]; exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hδ⟩) ?_
    show w ∈ gf (1, δ) +ᵥ (Wf (1, δ) : Set (Fin k → R))
    have h1 : gf (1, δ) = x := by rw [hgf]; simp
    have h2 : Wf (1, δ) = Submodule.span R {δ - x} := by rw [hWf]; simp
    rw [h1, h2]
    refine ⟨t⁻¹ • (δ - x), Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    have hwx : δ - x = t • (w - x) := by
      rw [heq]; ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    show x + t⁻¹ • (δ - x) = w
    rw [hwx, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    ext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  · -- `[w, y]` avoids `Δ`: `δ = (1-t)w + ty`, `t ≠ 1` (else `δ = y`), so `w ∈ y +ᵥ span(δ-y)`.
    rintro δ hδ t ht heq
    have ht1 : (1 - t) ≠ 0 := by
      intro h
      have ht1' : t = 1 := by linarith [sub_eq_zero.mp h]
      rw [ht1'] at heq
      simp only [sub_self, zero_smul, one_smul, zero_add] at heq
      exact hy (heq ▸ hδ)
    refine hw (2, δ) (by rw [hs]; exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hδ⟩) ?_
    show w ∈ gf (2, δ) +ᵥ (Wf (2, δ) : Set (Fin k → R))
    have h1 : gf (2, δ) = y := by rw [hgf]; simp
    have h2 : Wf (2, δ) = Submodule.span R {δ - y} := by rw [hWf]; simp
    rw [h1, h2]
    refine ⟨(1 - t)⁻¹ • (δ - y), Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    have hwy : δ - y = (1 - t) • (w - y) := by
      rw [heq]; ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    show y + (1 - t)⁻¹ • (δ - y) = w
    rw [hwy, smul_smul, inv_mul_cancel₀ ht1, one_smul]
    ext i; simp only [Pi.add_apply, Pi.sub_apply]; ring

/-! ### Local interval and graph helpers -/

open MvPolynomial

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
private theorem euclideanNormSq_fin_one' (w : Fin 1 → R) : euclideanNormSq w = w 0 ^ 2 := by
  simp [euclideanNormSq]

omit [IsStrictOrderedRing R] [IsRealClosed R] in
set_option linter.unusedSectionVars false in
private theorem mem_Icc_fin_one' {a b : R} {y : Fin 1 → R} :
    y ∈ Set.Icc (constPt a) (constPt b) ↔ a ≤ y 0 ∧ y 0 ≤ b := by
  simp only [Set.mem_Icc, constPt, Pi.le_def]
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1 0, h2 0⟩, fun ⟨h1, h2⟩ => ⟨fun i => ?_, fun i => ?_⟩⟩
  · rwa [Subsingleton.elim i 0]
  · rwa [Subsingleton.elim i 0]

omit [IsRealClosed R] in
/-- The interval `[a, b] ⊆ R¹` is semialgebraic. -/
private theorem isSemialgebraicSet_Icc' (a b : R) :
    IsSemialgebraicSet (Set.Icc (constPt a) (constPt b)) := by
  have heq : Set.Icc (constPt a) (constPt b)
      = {y : Fin 1 → R | eval y (X 0 - C a) ≥ 0} ∩ {y | eval y (X 0 - C b) ≤ 0} := by
    ext y
    rw [mem_Icc_fin_one']
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, map_sub, eval_X, eval_C, ge_iff_le,
      sub_nonneg, sub_nonpos]
  rw [heq]
  exact (IsSemialgebraicSet.geZero _).inter (IsSemialgebraicSet.leZero _)

/-- The interval `[a, b] ⊆ R¹` is closed (euclidean topology). -/
private theorem isClosed_Icc_constPt' (a b : R) : IsClosed (Set.Icc (constPt a) (constPt b)) := by
  rw [isClosed_iff, isOpen_iff]
  intro y hy
  rw [Set.mem_compl_iff, mem_Icc_fin_one', not_and_or, not_le, not_le] at hy
  have hkey : ∀ s t r : R, 0 < r → (s - t) ^ 2 < r ^ 2 → |s - t| < r := by
    intro s t r hr hsq
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd hsq (not_lt.mpr (by nlinarith [abs_nonneg (s - t), sq_abs (s - t)]))
  rcases hy with hya | hyb
  · refine ⟨y, a - y 0, by linarith, mem_openBall_self y (by linarith), fun z hz => ?_⟩
    rw [mem_openBall, euclideanNormSq_fin_one', Pi.sub_apply] at hz
    rw [Set.mem_compl_iff, mem_Icc_fin_one', not_and_or]
    exact Or.inl (not_le.mpr (by
      have := abs_lt.mp (hkey _ _ _ (by linarith) hz)
      linarith [this.1]))
  · refine ⟨y, y 0 - b, by linarith, mem_openBall_self y (by linarith), fun z hz => ?_⟩
    rw [mem_openBall, euclideanNormSq_fin_one', Pi.sub_apply] at hz
    rw [Set.mem_compl_iff, mem_Icc_fin_one', not_and_or]
    exact Or.inr (not_le.mpr (by
      have := abs_lt.mp (hkey _ _ _ (by linarith) hz)
      linarith [this.2]))

set_option linter.unusedSectionVars false in
/-- `funGraph` splits along a union of the domain. -/
private theorem funGraph_union' {ℓ : ℕ} {S T : Set (Fin 1 → R)}
    (f : (Fin 1 → R) → (Fin ℓ → R)) :
    funGraph (S ∪ T) f = funGraph S f ∪ funGraph T f := by
  ext z
  simp only [funGraph, Set.mem_union, Set.mem_ofPred_eq]
  tauto

set_option linter.unusedSectionVars false in
/-- `funGraph` depends only on the values of `f` on the domain. -/
private theorem funGraph_congr' {ℓ : ℕ} {S : Set (Fin 1 → R)}
    {f g : (Fin 1 → R) → (Fin ℓ → R)} (h : ∀ u ∈ S, f u = g u) :
    funGraph S f = funGraph S g := by
  ext z
  simp only [funGraph, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1, h2⟩
  · exact ⟨h1, by rw [h2, h _ h1]⟩
  · exact ⟨h1, by rw [h2, ← h _ h1]⟩

/-! ### The main theorem -/

/-- **The complement of a finite set in `Rᵏ` (`k ≥ 2`) is semialgebraically path connected.**

The affine building block for BPR Lemma 4.105. Given `x, y ∉ Δ`, route `x → w → y` through a detour
point `w` (`exists_detour_point`) by a piecewise-linear path: the first half follows the segment
`[x, w]`, the second the segment `[w, y]`; both avoid `Δ` by the choice of `w`. -/
theorem isSemialgebraicallyPathConnected_compl_finite (hk : 2 ≤ k) (Δ : Finset (Fin k → R)) :
    IsSemialgebraicallyPathConnected ((↑Δ : Set (Fin k → R))ᶜ) := by
  classical
  intro x hx y hy
  rw [Set.mem_compl_iff, Finset.mem_coe] at hx hy
  obtain ⟨w, hwΔ, hxw, hwy⟩ := exists_detour_point hk Δ hx hy
  -- the two affine pieces, as polynomial maps in the single variable `X 0`.
  set P₁ : Fin k → MvPolynomial (Fin 1) R :=
    fun j => (1 - 2 * X 0) * C (x j) + (2 * X 0) * C (w j) with hP₁
  set P₂ : Fin k → MvPolynomial (Fin 1) R :=
    fun j => (1 - (2 * X 0 - 1)) * C (w j) + (2 * X 0 - 1) * C (y j) with hP₂
  have hev₁ : ∀ u : Fin 1 → R,
      polynomialMap P₁ u = (1 - 2 * u 0) • x + (2 * u 0) • w := by
    intro u; funext j
    simp only [polynomialMap, hP₁, map_add, map_mul, map_sub, map_one, eval_X, eval_C,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_ofNat]
  have hev₂ : ∀ u : Fin 1 → R,
      polynomialMap P₂ u = (1 - (2 * u 0 - 1)) • w + (2 * u 0 - 1) • y := by
    intro u; funext j
    simp only [polynomialMap, hP₂, map_add, map_mul, map_sub, map_one, eval_X, eval_C,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_ofNat]
  -- the piecewise path.
  set ϕ : (Fin 1 → R) → (Fin k → R) :=
    fun u => if u 0 ≤ 1 / 2 then polynomialMap P₁ u else polynomialMap P₂ u with hϕ
  -- the two closed halves of the interval.
  set H₁ : Set (Fin 1 → R) := Set.Icc (constPt 0) (constPt (1 / 2)) with hH₁
  set H₂ : Set (Fin 1 → R) := Set.Icc (constPt (1 / 2)) (constPt 1) with hH₂
  have hH₁mem : ∀ u, u ∈ H₁ ↔ 0 ≤ u 0 ∧ u 0 ≤ 1 / 2 := fun u => mem_Icc_fin_one'
  have hH₂mem : ∀ u, u ∈ H₂ ↔ 1 / 2 ≤ u 0 ∧ u 0 ≤ 1 := fun u => mem_Icc_fin_one'
  -- `unitIntervalPt = H₁ ∪ H₂`.
  have hunion : (unitIntervalPt : Set (Fin 1 → R)) = H₁ ∪ H₂ := by
    ext u
    simp only [unitIntervalPt, Set.mem_union, hH₁mem, hH₂mem, mem_Icc_fin_one']
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_or_gt (u 0) (1 / 2) with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h.le, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨h0, by linarith⟩
      · exact ⟨by linarith, h1⟩
  -- `ϕ` equals `polynomialMap P₁` on `H₁` and `polynomialMap P₂` on `H₂`.
  have hϕ₁ : ∀ u ∈ H₁, ϕ u = polynomialMap P₁ u := by
    intro u hu
    simp only [hϕ]; exact ite_eq_left ((hH₁mem u).mp hu).2
  have hϕ₂ : ∀ u ∈ H₂, ϕ u = polynomialMap P₂ u := by
    intro u hu
    simp only [hϕ]
    rcases le_or_gt (u 0) (1 / 2) with h | h
    · -- on the overlap `u 0 = 1/2`, both pieces coincide (value `w`).
      have hhalf : u 0 = 1 / 2 := le_antisymm h ((hH₂mem u).mp hu).1
      rw [ite_eq_left h]
      rw [hev₁, hev₂, hhalf]
      norm_num
    · rw [ite_eq_right (not_le.mpr h)]
  refine ⟨ϕ, ?_, ?_, ?_, ?_, ?_⟩
  · -- semialgebraic: split the graph along `unitIntervalPt = H₁ ∪ H₂`.
    show IsSemialgebraicSet (funGraph unitIntervalPt ϕ)
    rw [hunion, funGraph_union']
    refine IsSemialgebraicSet.union ?_ ?_
    · rw [funGraph_congr' hϕ₁]
      exact isSemialgebraicFunction_polynomialMap (isSemialgebraicSet_Icc' _ _) P₁
    · rw [funGraph_congr' hϕ₂]
      exact isSemialgebraicFunction_polynomialMap (isSemialgebraicSet_Icc' _ _) P₂
  · -- continuous: glue the two continuous pieces over the closed halves.
    rw [hunion]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_Icc_constPt' _ _)
      (isClosed_Icc_constPt' _ _)
    · exact (continuous_polynomialMap P₁).continuousOn.congr hϕ₁
    · exact (continuous_polynomialMap P₂).continuousOn.congr hϕ₂
  · -- maps the interval into the complement of `Δ`.
    intro u hu
    rw [Set.mem_compl_iff, Finset.mem_coe]
    rw [hunion] at hu
    rcases hu with hu | hu
    · rw [hϕ₁ u hu, hev₁]
      intro hmem
      obtain ⟨h0, h2⟩ := (hH₁mem u).mp hu
      -- the point is `(1 - 2u₀) • x + (2u₀) • w`, on `[x, w]` with parameter `2u₀ ∈ [0,1]`.
      exact hxw _ hmem (2 * u 0) ⟨by linarith, by linarith⟩ rfl
    · rw [hϕ₂ u hu, hev₂]
      intro hmem
      obtain ⟨h1, h2⟩ := (hH₂mem u).mp hu
      -- the point is `(1 - s) • w + s • y` with `s = 2u₀ - 1 ∈ [0,1]`.
      exact hwy _ hmem (2 * u 0 - 1) ⟨by linarith, by linarith⟩ rfl
  · -- source: `ϕ (constPt 0) = x`.
    have h0 : (constPt (0 : R)) 0 ≤ 1 / 2 := by show (0 : R) ≤ 1 / 2; norm_num
    simp only [hϕ, ite_eq_left h0]
    rw [hev₁]
    have : (constPt (0 : R)) 0 = 0 := rfl
    rw [this]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · -- target: `ϕ (constPt 1) = y`.
    have h1 : ¬ (constPt (1 : R)) 0 ≤ 1 / 2 := by show ¬ (1 : R) ≤ 1 / 2; norm_num
    simp only [hϕ, ite_eq_right h1]
    rw [hev₂]
    have : (constPt (1 : R)) 0 = 1 := rfl
    rw [this]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

end Azurite.BPR
