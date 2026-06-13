import Azurite.BasuPollackRoy.Chapter3.Section3_5.OpNorm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projection

/-! # BPR §3.5 — orthogonal projection onto a subspace of `R^k`

Over a real closed field `R` the standard euclidean form `⟨a, b⟩ = ∑ aᵢ bᵢ`
(`euclideanInner`) is symmetric and **anisotropic**: `∑ vᵢ² = 0 ⟹ v = 0`. Anisotropy makes
the restriction of the form to *any* subspace `W ⊆ R^k` nondegenerate, so Mathlib's
`isCompl_orthogonal_of_restrict_nondegenerate` gives the orthogonal decomposition
`R^k = W ⊕ W^⊥` for every `W`. The orthogonal projection `orthProj W` is then the linear
projection onto `W` along `W^⊥`, and its defining geometric property — `orthProj W y` is the
point of `W` closest to `y` — follows from Pythagoras (`euclideanNormSq_add`). This is the
projection used in Proposition 3.26. -/

namespace Azurite.BPR

open LinearMap (BilinForm)

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-! ### Anisotropy of the euclidean form -/

omit [IsRealClosed R] in
/-- The euclidean form is **anisotropic**: `∑ vᵢ² = 0` only for `v = 0`. -/
theorem euclideanNormSq_eq_zero {z : Fin k → R} : euclideanNormSq z = 0 ↔ z = 0 := by
  rw [euclideanNormSq, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  constructor
  · intro h
    funext i
    exact pow_eq_zero_iff (by norm_num) |>.mp (h i (Finset.mem_univ i))
  · intro h _ _
    rw [h]
    simp

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The euclidean inner product is symmetric. -/
theorem euclideanInner_comm (a b : Fin k → R) :
    euclideanInner a b = euclideanInner b a :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-! ### The euclidean bilinear form -/

/-- The standard euclidean inner product as a `BilinForm`. -/
noncomputable def euclideanBilin : BilinForm R (Fin k → R) :=
  LinearMap.mk₂ R euclideanInner
    (fun a b c => by simp only [euclideanInner, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun s a c => by
      simp only [euclideanInner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun a b c => by simp only [euclideanInner, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a s c => by
      simp only [euclideanInner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem euclideanBilin_apply (a b : Fin k → R) :
    euclideanBilin a b = euclideanInner a b := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem euclideanBilin_isSymm : (euclideanBilin (R := R) (k := k)).IsSymm :=
  ⟨fun a b => by
    simp only [euclideanBilin_apply, euclideanInner]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem euclideanBilin_self (z : Fin k → R) :
    euclideanBilin z z = euclideanNormSq z := by
  simp only [euclideanBilin_apply, euclideanInner, euclideanNormSq]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The orthogonal decomposition `R^k = W ⊕ W^⊥` -/

omit [IsRealClosed R] in
/-- Anisotropy makes the form's restriction to any subspace nondegenerate. -/
theorem euclideanBilin_restrict_nondegenerate (W : Submodule R (Fin k → R)) :
    ((euclideanBilin (R := R)).restrict W).Nondegenerate := by
  -- `(euclideanBilin.restrict W) v w` is defeq `euclideanBilin ↑v ↑w`
  have key : ∀ v : W, (∀ w : W, euclideanBilin (v : Fin k → R) (w : Fin k → R) = 0) →
      v = 0 := by
    intro v hv
    have hvv := hv v
    rw [euclideanBilin_self] at hvv
    exact Subtype.ext (euclideanNormSq_eq_zero.mp hvv)
  refine ⟨fun v hv => key v fun w => hv w, fun v hv => key v fun w => ?_⟩
  show euclideanBilin (v : Fin k → R) (w : Fin k → R) = 0
  rw [euclideanBilin_apply, euclideanInner_comm, ← euclideanBilin_apply]
  exact hv w

omit [IsRealClosed R] in
/-- **The orthogonal decomposition.** Every subspace `W ⊆ R^k` is complemented by its
orthogonal complement. -/
theorem euclideanBilin_isCompl_orthogonal (W : Submodule R (Fin k → R)) :
    IsCompl W ((euclideanBilin (R := R)).orthogonal W) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    euclideanBilin_isSymm.isRefl (euclideanBilin_restrict_nondegenerate W)

/-! ### Orthogonal projection onto a subspace -/

/-- **Orthogonal projection** onto a subspace `W ⊆ R^k`, the linear projection onto `W`
along `W^⊥`. -/
noncomputable def orthProj (W : Submodule R (Fin k → R)) :
    (Fin k → R) →ₗ[R] (Fin k → R) :=
  W.projection (euclideanBilin.orthogonal W) (euclideanBilin_isCompl_orthogonal W)

omit [IsRealClosed R] in
theorem orthProj_mem (W : Submodule R (Fin k → R)) (y : Fin k → R) : orthProj W y ∈ W :=
  Submodule.projection_apply_mem _ _

omit [IsRealClosed R] in
theorem sub_orthProj_mem_orthogonal (W : Submodule R (Fin k → R)) (y : Fin k → R) :
    y - orthProj W y ∈ (euclideanBilin (R := R)).orthogonal W :=
  Submodule.sub_projection_mem _ y

omit [IsRealClosed R] in
/-- The displacement `y − orthProj W y` is orthogonal to every vector of `W`. -/
theorem euclideanInner_sub_orthProj (W : Submodule R (Fin k → R)) (y : Fin k → R)
    {w : Fin k → R} (hw : w ∈ W) : euclideanInner (y - orthProj W y) w = 0 := by
  have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp (sub_orthProj_mem_orthogonal W y)) w hw
  rw [LinearMap.BilinForm.isOrtho_def, euclideanBilin_apply] at h
  rw [euclideanInner_comm]
  exact h

omit [IsRealClosed R] in
/-- **Closest-point property (squared).** `orthProj W y` is the point of `W` nearest `y`. -/
theorem euclideanNormSq_sub_orthProj_le (W : Submodule R (Fin k → R)) (y : Fin k → R)
    {w : Fin k → R} (hw : w ∈ W) :
    euclideanNormSq (y - orthProj W y) ≤ euclideanNormSq (y - w) := by
  have hsplit : y - w = (y - orthProj W y) + (orthProj W y - w) := by abel
  have hpw : orthProj W y - w ∈ W := W.sub_mem (orthProj_mem W y) hw
  have hortho : euclideanInner (y - orthProj W y) (orthProj W y - w) = 0 :=
    euclideanInner_sub_orthProj W y hpw
  rw [hsplit, euclideanNormSq_add, hortho]
  nlinarith [euclideanNormSq_nonneg (orthProj W y - w)]

/-- **Closest-point property.** -/
theorem euclideanNorm_sub_orthProj_le (W : Submodule R (Fin k → R)) (y : Fin k → R)
    {w : Fin k → R} (hw : w ∈ W) :
    euclideanNorm (y - orthProj W y) ≤ euclideanNorm (y - w) :=
  euclideanNorm_le_of_normSq_le (euclideanNormSq_sub_orthProj_le W y hw)

/-- **Closest-point property for the affine flat `x + W`.** -/
theorem euclideanNorm_sub_affineProj_le (W : Submodule R (Fin k → R)) (x y : Fin k → R)
    {w : Fin k → R} (hw : w ∈ W) :
    euclideanNorm (y - (x + orthProj W (y - x))) ≤ euclideanNorm (y - (x + w)) := by
  have h := euclideanNorm_sub_orthProj_le W (y - x) hw
  have e1 : (y - x) - orthProj W (y - x) = y - (x + orthProj W (y - x)) := by abel
  have e2 : (y - x) - w = y - (x + w) := by abel
  rwa [e1, e2] at h

end Azurite.BPR
