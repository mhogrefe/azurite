import Azurite.BasuPollackRoy.Chapter4.Section4_6.MultiplicationMap
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_88
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# BPR §4.6, Remark 4.99: field of definition of `tr`, `det`, `χ` of `L_f`

For `f ∈ A`, the multiplication map `L_f` on `A` is `K`-linear, so its trace, determinant and
characteristic polynomial lie in `K`, `K`, `K[T]`. Concretely they are the base-changes of the
corresponding quantities for `L_f` on `Ā` (Part 1). Moreover, in a basis `ℬ` of `A` whose
multiplication table has entries in a subring `D ⊆ K`, if `f`'s coordinates are in `D`, then trace,
det are in `D` and `χ ∈ D[T]` (Part 2).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical TensorProduct

variable {k : ℕ} {K : Type*} [Field K]

section Part1

variable (C : Type*) [Field C] [Algebra K C]

/-- Bridge A: the `C`-algebra equivalence `C ⊗_K A ≅ Ā` sends `1 ⊗ a` to the image of `a` in `Ā`. -/
theorem algEquivExt_one_tmul (Ps : Finset (MvPolynomial (Fin k) K)) (a : quotPolys Ps) :
    algEquivExt C Ps (1 ⊗ₜ[K] a) = inclExt C Ps a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [inclExt_mk]
  show (Algebra.TensorProduct.tensorQuotientEquiv (R := K) C (MvPolynomial (Fin k) K) C
      (idealOfPolys Ps)).trans
    (Ideal.quotientEquivAlg (Ideal.map (Algebra.TensorProduct.includeRight) (idealOfPolys Ps))
      (idealOfPolysExt C Ps) (algebraTensorAlgEquiv K C) _)
      (1 ⊗ₜ[K] (Ideal.Quotient.mk _ p)) = _
  rw [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk]
  congr 1
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-- For a finite-dimensional `A`, the base change `Ā` is finite-dimensional over `C`
(Lemma 4.88). -/
instance moduleFinite_quotPolysExt (Ps : Finset (MvPolynomial (Fin k) K))
    [Module.Finite K (quotPolys Ps)] : Module.Finite C (quotPolysExt C Ps) :=
  (lemma_4_88 C Ps).2.mp inferInstance

/-- Bridge B: base change of `L_f` (over `K`) is `L_{1 ⊗ f}` (over `C`) on `C ⊗_K A`. -/
theorem baseChange_mulMap (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps) :
    (mulMap Ps f).baseChange C = LinearMap.mulLeft C ((1 : C) ⊗ₜ[K] f) := by
  refine LinearMap.ext fun z => z.induction_on ?_ (fun c a => ?_) (fun x y hx hy => ?_)
  · rw [map_zero, map_zero]
  · rw [LinearMap.baseChange_tmul, mulMap_apply, LinearMap.mulLeft_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · rw [map_add, hx, hy, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
      mul_add]

/-- Bridge C: conjugating `baseChange C (L_f)` by `algEquivExt` gives `L_f` on `Ā` (`mulMapBaseExt`). -/
theorem conj_baseChange_mulMap (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps) :
    (algEquivExt C Ps).toLinearEquiv.conj ((mulMap Ps f).baseChange C) = mulMapBaseExt C Ps f := by
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply, mulMapBaseExt_apply]
  show (algEquivExt C Ps) ((mulMap Ps f).baseChange C
      ((algEquivExt C Ps).toLinearEquiv.symm z)) = inclExt C Ps f * z
  rw [baseChange_mulMap, LinearMap.mulLeft_apply, map_mul, algEquivExt_one_tmul]
  congr 1
  exact (algEquivExt C Ps).apply_symm_apply z

theorem remark_4_99_trace (Ps : Finset (MvPolynomial (Fin k) K))
    [Module.Finite K (quotPolys Ps)] (f : quotPolys Ps) :
    LinearMap.trace C (quotPolysExt C Ps) (mulMapBaseExt C Ps f)
      = algebraMap K C (LinearMap.trace K (quotPolys Ps) (mulMap Ps f)) := by
  rw [← conj_baseChange_mulMap C Ps f, LinearMap.trace_conj',
    LinearMap.trace_baseChange (mulMap Ps f) C]

theorem remark_4_99_det (Ps : Finset (MvPolynomial (Fin k) K))
    [Module.Finite K (quotPolys Ps)] (f : quotPolys Ps) :
    LinearMap.det (mulMapBaseExt C Ps f) = algebraMap K C (LinearMap.det (mulMap Ps f)) := by
  rw [← conj_baseChange_mulMap C Ps f, LinearEquiv.conj_apply, LinearMap.comp_assoc,
    LinearMap.det_conj, LinearMap.det_baseChange]

theorem remark_4_99_charpoly (Ps : Finset (MvPolynomial (Fin k) K))
    [Module.Finite K (quotPolys Ps)] (f : quotPolys Ps) :
    LinearMap.charpoly (mulMapBaseExt C Ps f)
      = (LinearMap.charpoly (mulMap Ps f)).map (algebraMap K C) := by
  rw [← conj_baseChange_mulMap C Ps f, LinearEquiv.charpoly_conj,
    LinearMap.charpoly_baseChange]

end Part1

section Part2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every entry of the matrix of `L_f` in the basis `B` lies in `D`, given the multiplication
table and the coordinates of `f` lie in `D`. -/
theorem toMatrix_mulMap_mem (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps)
    (B : Module.Basis ι K (quotPolys Ps)) (D : Subring K)
    (hmul : ∀ i j l, B.repr (B i * B j) l ∈ D) (hf : ∀ i, B.repr f i ∈ D) (l j : ι) :
    (LinearMap.toMatrix B B (mulMap Ps f)) l j ∈ D := by
  rw [LinearMap.toMatrix_apply, mulMap_apply]
  have hfj : f * B j = ∑ i, B.repr f i • (B i * B j) := by
    conv_lhs => rw [← B.sum_repr f, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _)
  rw [hfj, map_sum, Finsupp.finsetSum_apply]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ (hf i) (hmul i j l)

theorem remark_4_99_trace_mem (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps)
    (B : Module.Basis ι K (quotPolys Ps)) (D : Subring K)
    (hmul : ∀ i j l, B.repr (B i * B j) l ∈ D) (hf : ∀ i, B.repr f i ∈ D) :
    LinearMap.trace K (quotPolys Ps) (mulMap Ps f) ∈ D := by
  rw [LinearMap.trace_eq_matrix_trace K B, Matrix.trace]
  refine Subring.sum_mem _ fun i _ => ?_
  exact toMatrix_mulMap_mem Ps f B D hmul hf i i

theorem remark_4_99_det_mem (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps)
    (B : Module.Basis ι K (quotPolys Ps)) (D : Subring K)
    (hmul : ∀ i j l, B.repr (B i * B j) l ∈ D) (hf : ∀ i, B.repr f i ∈ D) :
    LinearMap.det (mulMap Ps f) ∈ D := by
  set M := LinearMap.toMatrix B B (mulMap Ps f) with hMdef
  have hM : ∀ l j, M l j ∈ D := fun l j => toMatrix_mulMap_mem Ps f B D hmul hf l j
  set MD : Matrix ι ι D := fun l j => ⟨M l j, hM l j⟩ with hMD
  have hmap : M = MD.map (D.subtype) := by
    ext l j; rfl
  rw [← LinearMap.det_toMatrix B (mulMap Ps f), ← hMdef, hmap,
    show MD.map (D.subtype) = D.subtype.mapMatrix MD from rfl, ← RingHom.map_det]
  exact (MD.det).2

theorem remark_4_99_charpoly_mem (Ps : Finset (MvPolynomial (Fin k) K))
    [Module.Finite K (quotPolys Ps)] (f : quotPolys Ps)
    (B : Module.Basis ι K (quotPolys Ps)) (D : Subring K)
    (hmul : ∀ i j l, B.repr (B i * B j) l ∈ D) (hf : ∀ i, B.repr f i ∈ D) :
    ∀ n, (LinearMap.charpoly (mulMap Ps f)).coeff n ∈ D := by
  intro n
  set M := LinearMap.toMatrix B B (mulMap Ps f) with hMdef
  have hM : ∀ l j, M l j ∈ D := fun l j => toMatrix_mulMap_mem Ps f B D hmul hf l j
  set MD : Matrix ι ι D := fun l j => ⟨M l j, hM l j⟩ with hMD
  have hmap : M = MD.map (D.subtype) := by
    ext l j; rfl
  rw [← LinearMap.charpoly_toMatrix (f := mulMap Ps f) B, ← hMdef, hmap, Matrix.charpoly_map,
    Polynomial.coeff_map]
  exact (MD.charpoly.coeff n).2

end Part2

end Azurite.BPR.Chapter4
