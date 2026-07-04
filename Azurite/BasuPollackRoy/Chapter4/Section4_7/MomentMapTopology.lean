import Azurite.BasuPollackRoy.Chapter4.Section4_7.MomentMap
import Azurite.BasuPollackRoy.Chapter4.Section4_7.Lemma_4_105

/-!
# BPR §4.7, Proposition 4.106: the moment-map embedding is continuous

The moment-map embedding `momentMap : ℙ_k(C) → R^N` sends a line to the real coordinates of the
Hermitian projector onto it. Here we show it is continuous, together with a reusable continuity
criterion for maps out of `ℙ_k(C)`: a map is continuous iff its composite with every affine chart
`φᵢ` is.

Since `R` carries only its order (the euclidean topology of §3.1 lives on the spaces `R^k = Fin k → R`,
not on `R`), the finite index set `((Fin (k+1) × Fin (k+1)) ⊕ (Fin (k+1) × Fin (k+1)))` of the moment
function is reindexed to `Fin N` and the codomain `R^N = Fin N → R` carries that euclidean topology;
the moment map's native `Sum`-indexed codomain is topologized as the induced topology along this
reindexing. Continuity of `momentMap ∘ φᵢ` then reduces, through the realification homeomorphism
`Cᵏ ≅ R^{2k}`, to the `ContinuousR` building blocks of §3.1 (coordinate projections, sums, products,
differences) together with continuity of reciprocals of an everywhere-positive denominator (the
Hermitian norm of the chart representative `(x₁ : ⋯ : 1 : ⋯ : x_k)`, which carries a `1`).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-! ### A continuity criterion for maps out of `ℙ_k(C)` -/

set_option linter.unusedSectionVars false in
/-- **Continuity criterion.** A map out of `ℙ_k(C)` is continuous iff its composite with every affine
chart `φᵢ` is continuous. -/
theorem continuous_projective_iff {Y : Type*} [TopologicalSpace Y]
    (f : complexProjectiveSpace R k → Y) :
    Continuous f ↔ ∀ i, Continuous (f ∘ chartMap i) := by
  constructor
  · intro hf i
    exact hf.comp (continuous_chartMap i)
  · intro hf
    rw [continuous_def]
    intro s hs
    rw [isOpenP_iff]
    intro i
    have hpre : chartMap i ⁻¹' (f ⁻¹' s ∩ chartSet i) = (f ∘ chartMap i) ⁻¹' s := by
      rw [Set.preimage_inter]
      have huniv : chartMap i ⁻¹' (chartSet i : Set (complexProjectiveSpace R k))
          = (Set.univ : Set (Fin k → Ri R)) := by
        rw [chartSet, Set.preimage_range]
      rw [huniv, Set.inter_univ, Set.preimage_comp]
    rw [hpre]
    exact (hf i).isOpen_preimage s hs

/-! ### `ContinuousR` building blocks: difference and reciprocal -/

set_option linter.unusedSectionVars false in
/-- The difference of two `ContinuousR` maps is `ContinuousR`. -/
theorem continuousR_sub {g h : (Fin k → R) → R} (hg : ContinuousR g) (hh : ContinuousR h) :
    ContinuousR (fun y => g y - h y) := by
  have hneg : ContinuousR (fun y => (-1 : R) * h y) :=
    ContinuousR.mul (continuousR_const (-1)) hh
  have := ContinuousR.add hg hneg
  simpa only [neg_one_mul, sub_eq_add_neg] using this

set_option linter.unusedSectionVars false in
/-- The reciprocal of an everywhere-nonzero `ContinuousR` map is `ContinuousR`. -/
theorem continuousR_inv {g : (Fin k → R) → R} (hg : ContinuousR g) (hne : ∀ y, g y ≠ 0) :
    ContinuousR (fun y => (g y)⁻¹) := by
  intro x ε hε
  have hgx : (0 : R) < |g x| := abs_pos.mpr (hne x)
  -- shrink so `|g y - g x| < |g x| / 2`, giving `|g y| > |g x| / 2`
  obtain ⟨δ1, hδ1, hb1⟩ := hg x (|g x| / 2) (by positivity)
  -- and so `|g y - g x| < ε * |g x|^2 / 2`
  obtain ⟨δ2, hδ2, hb2⟩ := hg x (ε * |g x| ^ 2 / 2) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hy => ?_⟩
  have hy1 := hb1 y (lt_of_lt_of_le hy (min_le_left _ _))
  have hy2 := hb2 y (lt_of_lt_of_le hy (min_le_right _ _))
  -- `|g y| ≥ |g x| - |g y - g x| > |g x| / 2`
  have hgy_lb : |g x| / 2 < |g y| := by
    have h := abs_sub_abs_le_abs_sub (g x) (g y)
    rw [abs_sub_comm (g x) (g y)] at h
    linarith [h, hy1]
  have hgy_pos : (0 : R) < |g y| := by linarith
  have hgyne : g y ≠ 0 := by
    intro hzero; rw [hzero, abs_zero] at hgy_pos; exact lt_irrefl _ hgy_pos
  -- the reciprocal difference
  have hkey : (g y)⁻¹ - (g x)⁻¹ = (g x - g y) / (g y * g x) :=
    inv_sub_inv hgyne (hne x)
  rw [hkey, abs_div, abs_mul, abs_sub_comm (g x) (g y)]
  have hden_pos : (0 : R) < |g y| * |g x| := mul_pos hgy_pos hgx
  rw [div_lt_iff₀ hden_pos]
  -- `|g y - g x| < ε * |g x|^2 / 2 ≤ ε * (|g y| * |g x|)`
  calc |g y - g x| < ε * |g x| ^ 2 / 2 := hy2
    _ = ε * (|g x| / 2 * |g x|) := by ring
    _ ≤ ε * (|g y| * |g x|) := by
        refine mul_le_mul_of_nonneg_left ?_ hε.le
        exact mul_le_mul_of_nonneg_right hgy_lb.le (abs_nonneg _)

set_option linter.unusedSectionVars false in
/-- The quotient of `ContinuousR` maps with an everywhere-nonzero denominator is `ContinuousR`. -/
theorem continuousR_div {g h : (Fin k → R) → R} (hg : ContinuousR g) (hh : ContinuousR h)
    (hne : ∀ y, h y ≠ 0) : ContinuousR (fun y => g y / h y) := by
  have := ContinuousR.mul hg (continuousR_inv hh hne)
  simpa only [div_eq_mul_inv] using this

/-! ### Coordinate continuity on `R^{2k}` through the realification -/

set_option linter.unusedSectionVars false in
/-- Through the realification, the real part of the `m`-th coordinate of `realEquiv.symm w` is just
the `castAdd`-coordinate of `w`. -/
theorem reL_realEquiv_symm (w : Fin (k + k) → R) (m : Fin k) :
    Ri.reL ((realEquiv.symm w) m) = w (Fin.castAdd k m) := by
  conv_rhs => rw [← realEquiv.apply_symm_apply w]
  rw [realEquiv_apply_castAdd]

set_option linter.unusedSectionVars false in
/-- Through the realification, the imaginary part of the `m`-th coordinate of `realEquiv.symm w` is
the `natAdd`-coordinate of `w`. -/
theorem imL_realEquiv_symm (w : Fin (k + k) → R) (m : Fin k) :
    Ri.imL ((realEquiv.symm w) m) = w (Fin.natAdd k m) := by
  conv_rhs => rw [← realEquiv.apply_symm_apply w]
  rw [realEquiv_apply_natAdd]

set_option linter.unusedSectionVars false in
/-- The real part of the `m`-th coordinate of the chart representative `Fin.insertNth i 1 (φᵢ⁻¹ data)`,
viewed through the realification as a function of `w : R^{2k}`, is `ContinuousR`. -/
theorem continuousR_reL_insertNth (i m : Fin (k + 1)) :
    ContinuousR
      (fun w : Fin (k + k) → R =>
        Ri.reL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) m)) := by
  refine Fin.succAboveCases i ?_ (fun j => ?_) m
  · have h : (fun w : Fin (k + k) → R =>
          Ri.reL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) i))
        = (fun _ : Fin (k + k) → R => Ri.reL (1 : Ri R)) := by
      funext w; rw [Fin.insertNth_apply_same]
    rw [h]; exact continuousR_const _
  · have h : (fun w : Fin (k + k) → R =>
          Ri.reL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R)
            (i.succAbove j)))
        = (fun w : Fin (k + k) → R => w (Fin.castAdd k j)) := by
      funext w; rw [Fin.insertNth_apply_succAbove, reL_realEquiv_symm]
    rw [h]; exact continuousR_coord _

set_option linter.unusedSectionVars false in
/-- The imaginary part of the `m`-th coordinate of the chart representative, viewed through the
realification, is `ContinuousR`. -/
theorem continuousR_imL_insertNth (i m : Fin (k + 1)) :
    ContinuousR
      (fun w : Fin (k + k) → R =>
        Ri.imL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) m)) := by
  refine Fin.succAboveCases i ?_ (fun j => ?_) m
  · have h : (fun w : Fin (k + k) → R =>
          Ri.imL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) i))
        = (fun _ : Fin (k + k) → R => Ri.imL (1 : Ri R)) := by
      funext w; rw [Fin.insertNth_apply_same]
    rw [h]; exact continuousR_const _
  · have h : (fun w : Fin (k + k) → R =>
          Ri.imL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R)
            (i.succAbove j)))
        = (fun w : Fin (k + k) → R => w (Fin.natAdd k j)) := by
      funext w; rw [Fin.insertNth_apply_succAbove, imL_realEquiv_symm]
    rw [h]; exact continuousR_coord _

set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
/-- `ContinuousR` is closed under finite sums over a `Finset`. -/
theorem continuousR_finsetSum {ι : Type*} (s : Finset ι) (g : ι → (Fin k → R) → R)
    (hg : ∀ m ∈ s, ContinuousR (g m)) :
    ContinuousR (fun w => ∑ m ∈ s, g m w) := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using continuousR_const (0 : R)
  | insert a t ha ih =>
    have hgt : ∀ m ∈ t, ContinuousR (g m) := fun m hm => hg m (Finset.mem_insert_of_mem hm)
    have hga : ContinuousR (g a) := hg a (Finset.mem_insert_self a t)
    have hsum : (fun w => ∑ m ∈ insert a t, g m w)
        = (fun w => g a w + ∑ m ∈ t, g m w) := by
      funext w; rw [Finset.sum_insert ha]
    rw [hsum]
    exact ContinuousR.add hga (ih hgt)

set_option linter.unusedSectionVars false in
/-- The square of a `ContinuousR` map is `ContinuousR`. -/
theorem continuousR_sq {g : (Fin k → R) → R} (hg : ContinuousR g) :
    ContinuousR (fun w => g w ^ 2) := by
  have h : ContinuousR (fun w => g w * g w) := ContinuousR.mul hg hg
  have heq : (fun w => g w ^ 2) = (fun w => g w * g w) := by funext w; rw [sq]
  rw [heq]; exact h

set_option linter.unusedSectionVars false in
/-- The Hermitian norm of the chart representative, viewed through the realification, is
`ContinuousR`. -/
theorem continuousR_hermNormSq_insertNth (i : Fin (k + 1)) :
    ContinuousR
      (fun w : Fin (k + k) → R => hermNormSq (Fin.insertNth i (1 : Ri R) (realEquiv.symm w))) := by
  -- expand the sum and reduce to a finite sum of squares of the coordinate parts
  have heq : (fun w : Fin (k + k) → R =>
        hermNormSq (Fin.insertNth i (1 : Ri R) (realEquiv.symm w)))
      = (fun w => ∑ m : Fin (k + 1),
          (Ri.reL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) m) ^ 2
            + Ri.imL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) m) ^ 2)) := by
    funext w; rw [hermNormSq]
  rw [heq]
  refine continuousR_finsetSum Finset.univ _ (fun m _ => ?_)
  exact ContinuousR.add (continuousR_sq (continuousR_reL_insertNth i m))
    (continuousR_sq (continuousR_imL_insertNth i m))

/-! ### The reindexed codomain and its euclidean topology -/

/-- The finite index set of the moment function. -/
abbrev MomentIndex (k : ℕ) :=
  (Fin (k + 1) × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin (k + 1))

/-- The reindexing equivalence `MomentIndex k ≃ Fin N`, with `N = Fintype.card`. -/
noncomputable def momentReindex (k : ℕ) : MomentIndex k ≃ Fin (Fintype.card (MomentIndex k)) :=
  Fintype.equivFin (MomentIndex k)

/-- The codomain `R^{MomentIndex}` of the moment map carries the euclidean topology of
`R^N = Fin N → R`, transported along the reindexing `momentReindex`. -/
noncomputable instance momentCodomainTopology :
    TopologicalSpace (MomentIndex k → R) :=
  TopologicalSpace.induced
    (fun f : MomentIndex k → R => f ∘ (momentReindex k).symm)
    (inferInstance : TopologicalSpace (Fin (Fintype.card (MomentIndex k)) → R))

set_option linter.unusedSectionVars false in
/-- Reindexing `f ↦ f ∘ (momentReindex k).symm : R^{MomentIndex} → R^N` is, by construction, the
inducing map of the codomain topology, hence continuous. -/
theorem continuous_momentReindex_codomain :
    Continuous (fun f : MomentIndex k → R => f ∘ (momentReindex k).symm) :=
  continuous_induced_dom

/-! ### Continuity of the moment map -/

set_option linter.unusedSectionVars false in
/-- **BPR Proposition 4.106 (continuity).** The moment-map embedding `momentMap : ℙ_k(C) → R^N` is
continuous (the codomain carrying the euclidean topology along the reindexing `momentReindex`). -/
theorem continuous_momentMap :
    Continuous (momentMap : complexProjectiveSpace R k → MomentIndex k → R) := by
  -- It suffices to be continuous after reindexing into `R^N`.
  rw [show (momentCodomainTopology : TopologicalSpace (MomentIndex k → R))
      = TopologicalSpace.induced
          (fun f : MomentIndex k → R => f ∘ (momentReindex k).symm) inferInstance from rfl]
  rw [continuous_induced_rng]
  -- reduce to each chart via the projective criterion
  rw [continuous_projective_iff]
  intro i
  -- compose with the realification homeomorphism: continuity is preserved
  rw [← Homeomorph.comp_continuous_iff' (realEquivₜ (R := R) (k := k)).symm]
  -- the resulting map `R^{2k} → R^N` is continuous componentwise
  set F : (Fin (k + k) → R) → (Fin (Fintype.card (MomentIndex k)) → R) :=
    (fun f : MomentIndex k → R => f ∘ (momentReindex k).symm)
      ∘ (momentMap : complexProjectiveSpace R k → MomentIndex k → R)
      ∘ chartMap i ∘ (realEquivₜ (R := R) (k := k)).symm with hF
  show Continuous F
  rw [continuous_iff_components]
  intro c
  -- the `c`-th component, as a function of `w : R^{2k}`, evaluated on the chart representative
  set s := (momentReindex k).symm c with hs
  have hval : ∀ w : Fin (k + k) → R,
      F w c = momentFn (Fin.insertNth i (1 : Ri R) (realEquiv.symm w)) s := by
    intro w
    simp only [hF, Function.comp_apply, hs]
    show momentMap (chartMap i (realEquiv.symm w)) ((momentReindex k).symm c)
      = momentFn (Fin.insertNth i (1 : Ri R) (realEquiv.symm w)) ((momentReindex k).symm c)
    rw [chartMap, momentMap_mkLine _ (insertNth_one_ne_zero i (realEquiv.symm w))]
  -- it suffices to prove `ContinuousR` of `w ↦ momentFn (...) s`
  have hcong : (fun w => F w c)
      = (fun w : Fin (k + k) → R => momentFn (Fin.insertNth i (1 : Ri R) (realEquiv.symm w)) s) := by
    funext w; exact hval w
  rw [hcong]
  -- the denominator is everywhere positive, hence nonzero
  have hden_ne : ∀ w : Fin (k + k) → R,
      hermNormSq (Fin.insertNth i (1 : Ri R) (realEquiv.symm w)) ≠ 0 :=
    fun w => ne_of_gt (hermNormSq_pos (insertNth_one_ne_zero i (realEquiv.symm w)))
  -- case on whether `s` is a real-part or imaginary-part entry
  obtain ⟨p⟩ | ⟨p⟩ := s
  · -- real-part entry
    have he : (fun w : Fin (k + k) → R =>
          momentFn (Fin.insertNth i (1 : Ri R) (realEquiv.symm w)) (Sum.inl p))
        = fun w => (Ri.reL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) p.1)
              * Ri.reL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) p.2)
            + Ri.imL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) p.1)
              * Ri.imL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) p.2))
          / hermNormSq (Fin.insertNth i (1 : Ri R) (realEquiv.symm w)) := by
      funext w; rw [momentFn_inl, projReV]
    rw [he]
    exact continuousR_div
      (ContinuousR.add
        (ContinuousR.mul (continuousR_reL_insertNth i p.1) (continuousR_reL_insertNth i p.2))
        (ContinuousR.mul (continuousR_imL_insertNth i p.1) (continuousR_imL_insertNth i p.2)))
      (continuousR_hermNormSq_insertNth i) hden_ne
  · -- imaginary-part entry
    have he : (fun w : Fin (k + k) → R =>
          momentFn (Fin.insertNth i (1 : Ri R) (realEquiv.symm w)) (Sum.inr p))
        = fun w => (Ri.imL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) p.1)
              * Ri.reL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) p.2)
            - Ri.reL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) p.1)
              * Ri.imL ((Fin.insertNth i (1 : Ri R) (realEquiv.symm w) : Fin (k + 1) → Ri R) p.2))
          / hermNormSq (Fin.insertNth i (1 : Ri R) (realEquiv.symm w)) := by
      funext w; rw [momentFn_inr, projImV]
    rw [he]
    exact continuousR_div
      (continuousR_sub
        (ContinuousR.mul (continuousR_imL_insertNth i p.1) (continuousR_reL_insertNth i p.2))
        (ContinuousR.mul (continuousR_reL_insertNth i p.1) (continuousR_imL_insertNth i p.2)))
      (continuousR_hermNormSq_insertNth i) hden_ne

end Azurite.BPR.Chapter4
