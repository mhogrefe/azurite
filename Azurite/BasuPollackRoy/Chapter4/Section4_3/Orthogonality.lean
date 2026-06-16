import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Azurite.BasuPollackRoy.Chapter4.Section4_3.QuadraticForm

/-!
# BPR §4.3.1: Euclidean structure for quadratic forms

The inner product on `Rⁿ` is the dot product `u · u' = ∑ₖ uₖ u'ₖ` (Mathlib's
`dotProduct`, written `u ⬝ᵥ u'`). The norm `‖u‖ = √(u · u)` is the real-closed
euclidean norm `Azurite.BPR.euclideanNorm` of §3.1 (note `euclideanNormSq u = u ⬝ᵥ u`).
Two vectors are *orthogonal* when their inner product vanishes.

This file collects orthogonality/Gram–Schmidt material and the matrix forms of §4.3.1:
orthogonal/orthonormal bases, orthogonal linear forms, Gram–Schmidt (Proposition 4.41),
and the bilinear/quadratic forms `B_M`/`Φ_M` of a symmetric matrix. (These are
quadratic-form preliminaries, *not* Hermite's quadratic form, which is §4.3.2.)
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Orthogonal vectors.** `u` and `u'` in `Rⁿ` are orthogonal when their inner
product `u · u' = ∑ₖ uₖ u'ₖ` (Mathlib's `dotProduct`) vanishes. -/
def IsOrthogonal (u u' : Fin n → R) : Prop := dotProduct u u' = 0

/-- An **orthogonal basis** of `Rⁿ`: a basis whose distinct vectors are pairwise
orthogonal, `vᵢ · vⱼ = 0` for `i ≠ j`. -/
def IsOrthogonalBasis (v : Module.Basis (Fin n) R (Fin n → R)) : Prop :=
  ∀ i j, i ≠ j → IsOrthogonal (v i) (v j)

/-- An **orthonormal basis** of `Rⁿ`: an orthogonal basis in which every vector has
norm `1`, i.e. `‖vᵢ‖ = 1`, equivalently `vᵢ · vᵢ = 1`. -/
def IsOrthonormalBasis (v : Module.Basis (Fin n) R (Fin n → R)) : Prop :=
  IsOrthogonalBasis v ∧ ∀ i, dotProduct (v i) (v i) = 1

/-- The coefficient vector `u = (u₁, …, uₙ)` of a linear form `L = ∑ᵢ uᵢ fᵢ` on
`Rⁿ`, where `fᵢ` is the `i`-th coordinate; `uᵢ = L(eᵢ)`. -/
def linearFormCoeffs (L : (Fin n → R) →ₗ[R] R) : Fin n → R := fun i => L (Pi.single i 1)

/-- Two **linear forms are orthogonal** when their coefficient vectors are
orthogonal, `u · u' = 0`. -/
def IsOrthogonalForms (L L' : (Fin n → R) →ₗ[R] R) : Prop :=
  IsOrthogonal (linearFormCoeffs L) (linearFormCoeffs L')

/-! ### Proposition 4.41: Gram–Schmidt orthogonalization -/

section GramSchmidt

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ}

open Matrix Submodule Set

/-- The Gram–Schmidt recursion `w₁ = v₁`, `wᵢ = vᵢ − ∑_{j<i} μ_{i,j} wⱼ` with
`μ_{i,j} = (vᵢ · wⱼ)/(wⱼ · wⱼ)`, written with the dot product as inner product. -/
private noncomputable def gs (v : Fin n → (Fin n → R)) : Fin n → (Fin n → R)
  | i => v i - ∑ j : Finset.Iio i,
            ((v i ⬝ᵥ gs v j) / (gs v j ⬝ᵥ gs v j)) • gs v j
  termination_by i => i
  decreasing_by exact Fin.lt_def.1 (Finset.mem_Iio.1 j.2)

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem gs_def (v : Fin n → (Fin n → R)) (i : Fin n) :
    gs v i = v i - ∑ j ∈ Finset.Iio i,
      ((v i ⬝ᵥ gs v j) / (gs v j ⬝ᵥ gs v j)) • gs v j := by
  rw [← Finset.sum_attach (Finset.Iio i), Finset.attach_eq_univ, gs]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The triangular (change-of-basis) property: `gs v j` lies in the span of the
original vectors indexed by `≤ i` whenever `j ≤ i`. -/
private theorem gs_mem_span (v : Fin n → (Fin n → R)) (j : Fin n) :
    gs v j ∈ span R (v '' {k | k ≤ j}) := by
  apply wellFounded_lt.induction j
  intro j ih
  rw [gs_def v j]
  refine Submodule.sub_mem _ (subset_span (mem_image_of_mem _ (Set.mem_setOf_eq.mpr le_rfl)))
    (Submodule.sum_mem _ fun k hk => ?_)
  have hkj : k < j := Finset.mem_Iio.1 hk
  refine smul_mem _ _ ?_
  exact span_mono (image_mono fun a (ha : a ≤ k) => ha.trans hkj.le) (ih k hkj)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The triangular property in the form required by the statement. -/
private theorem gs_sub_mem_span (v : Fin n → (Fin n → R)) (i : Fin n) :
    gs v i - v i ∈ span R (v '' {j | j < i}) := by
  rw [gs_def v i]
  have : v i - ∑ j ∈ Finset.Iio i,
      ((v i ⬝ᵥ gs v j) / (gs v j ⬝ᵥ gs v j)) • gs v j - v i
      = - ∑ j ∈ Finset.Iio i,
          ((v i ⬝ᵥ gs v j) / (gs v j ⬝ᵥ gs v j)) • gs v j := by ring
  rw [this]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk => ?_)
  have hki : k < i := Finset.mem_Iio.1 hk
  refine smul_mem _ _ ?_
  refine span_mono (image_mono fun a (ha : a ≤ k) => lt_of_le_of_lt ha hki) ?_
  exact gs_mem_span v k

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Gram–Schmidt produces nonzero vectors from independent input. -/
private theorem gs_ne_zero (v : Fin n → (Fin n → R)) (hv : LinearIndependent R v)
    (i : Fin n) : gs v i ≠ 0 := by
  intro h
  have hvi : v i ∈ span R (v '' {j | j < i}) := by
    have := gs_sub_mem_span v i
    rw [h, zero_sub] at this
    have hmem : -v i ∈ span R (v '' {j | j < i}) := this
    simpa using (Submodule.neg_mem _ hmem)
  exact hv.notMem_span_image (s := {j | j < i}) (lt_irrefl i) hvi

/-- Gram–Schmidt orthogonality: distinct output vectors have vanishing dot product. -/
private theorem gs_orthogonal (v : Fin n → (Fin n → R)) {a b : Fin n} (h₀ : a ≠ b) :
    gs v a ⬝ᵥ gs v b = 0 := by
  suffices h : ∀ a b : Fin n, a < b → gs v b ⬝ᵥ gs v a = 0 by
    rcases h₀.lt_or_gt with hab | hba
    · rw [dotProduct_comm]; exact h _ _ hab
    · exact h _ _ hba
  clear h₀ a b
  intro a b hab
  revert a
  apply wellFounded_lt.induction b
  intro b ih a hab
  rw [gs_def v b, sub_dotProduct, sum_dotProduct]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_Iio.mpr hab)]
  · by_cases hga : gs v a = 0
    · simp [hga]
    · rw [smul_dotProduct, smul_eq_mul, div_mul_cancel₀, sub_self]
      rw [Ne, dotProduct_self_eq_zero]; exact hga
  · intro k hk hka
    rw [smul_dotProduct, smul_eq_mul]
    have hki : k < b := Finset.mem_Iio.1 hk
    have : gs v k ⬝ᵥ gs v a = 0 := by
      rcases hka.lt_or_gt with hka₁ | hka₂
      · rw [dotProduct_comm]; exact ih a hab k hka₁
      · exact ih k hki a hka₂
    rw [this, mul_zero]

/-- Gram–Schmidt produces linearly independent vectors. -/
private theorem gs_linearIndependent (v : Fin n → (Fin n → R))
    (hv : LinearIndependent R v) : LinearIndependent R (gs v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have hdot : (∑ i, g i • gs v i) ⬝ᵥ gs v k = 0 := by rw [hg]; simp
  rw [sum_dotProduct] at hdot
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)] at hdot
  · rw [smul_dotProduct, smul_eq_mul] at hdot
    rcases mul_eq_zero.1 hdot with h | h
    · exact h
    · exact absurd ((dotProduct_self_eq_zero).1 h) (gs_ne_zero v hv k)
  · intro i _ hik
    rw [smul_dotProduct, smul_eq_mul, gs_orthogonal v hik, mul_zero]

/-- **BPR Proposition 4.41 (Gram–Schmidt orthogonalization).** Linearly independent
vectors `v₁, …, vₙ` of `Rⁿ` can be orthogonalized: there is a family of linearly
independent, pairwise orthogonal vectors `w₁, …, wₙ` with `wᵢ − vᵢ` in the span of
`v₁, …, v_{i-1}` for every `i`. The construction is the Gram–Schmidt recursion
`w₁ = v₁`, `wᵢ = vᵢ − ∑_{j<i} μ_{i,j} wⱼ` with `μ_{i,j} = (vᵢ · wⱼ)/‖wⱼ‖²`
(well-defined since `‖wⱼ‖² = wⱼ · wⱼ > 0` for `wⱼ ≠ 0` over an ordered field). -/
theorem proposition_4_41 (v : Fin n → (Fin n → R)) (hv : LinearIndependent R v) :
    ∃ w : Fin n → (Fin n → R),
      LinearIndependent R w ∧
      (∀ i j, i ≠ j → IsOrthogonal (w i) (w j)) ∧
      (∀ i, w i - v i ∈ Submodule.span R (v '' {j | j < i})) := by
  refine ⟨gs v, gs_linearIndependent v hv, ?_, ?_⟩
  · intro i j hij
    exact gs_orthogonal v hij
  · intro i
    exact gs_sub_mem_span v i

end GramSchmidt

/-! ### Forms associated to a symmetric matrix -/

section MatrixForms

open scoped Matrix

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ}

/-- **The bilinear form `B_M`** of a symmetric matrix `M`: `B_M(f, g) = g · M · fᵗ`.
(The quadratic form is `Φ_M(f) = f · M · fᵗ = `\ `quadraticForm M`, and the linear
map is `u_M(f) = M · f = `\ `Matrix.mulVec M f`.) -/
def bilinFormM (M : Matrix (Fin n) (Fin n) R) (f g : Fin n → R) : R := g ⬝ᵥ M *ᵥ f

/-- **The quadratic form `Φ_M` is non-negative** if `Φ_M(f) ≥ 0` for every `f ∈ Rⁿ`. -/
def IsNonNeg (M : Matrix (Fin n) (Fin n) R) : Prop := ∀ f, 0 ≤ quadraticForm M f

end MatrixForms

end Azurite.BPR.Chapter4
