import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# BPR §4.5, Lemma 4.88: `dim_K A = dim_C Ā`

Let `K` be a field, `C` an algebraically closed field containing `K`, and `𝒫` a finite set of
polynomials in `K[X₁, …, X_k]`. Then `A = K[X]/Ideal(𝒫,K)` is a finite-dimensional vector space
of dimension `m` over `K` if and only if `Ā = C[X]/Ideal(𝒫,C)` is a finite-dimensional vector
space of dimension `m` over `C`.

This is the base-change statement: `Ā ≅ C ⊗_K A` as `C`-algebras (`algEquivExt`), built from
`Algebra.TensorProduct.tensorQuotientEquiv` (tensor commutes with the quotient by an extended
ideal) and `MvPolynomial.algebraTensorAlgEquiv` (`C ⊗_K K[X] ≅ C[X]`). Dimension and finiteness
then transfer through `Module.finrank_baseChange` and `Algebra.TensorProduct.basis`. (BPR's
elementary proof — descent of a linear dependence from `C` to `K` — is the same fact specialized
to the rank of the relevant linear system; cf. the descent in Lemma 4.87.)
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical TensorProduct

variable {k : ℕ} {K : Type*} [Field K] (C : Type*) [Field C] [Algebra K C]

/-- **`Ā ≅ C ⊗_K A` as `C`-algebras.** Tensoring `A = K[X]/Ideal(𝒫,K)` up to `C` and identifying
`C ⊗_K K[X]` with `C[X]` (under which the extended ideal becomes `Ideal(𝒫,C)`) yields `Ā`. -/
theorem algebraTensorAlgEquiv_includeRight (P : MvPolynomial (Fin k) K) :
    (algebraTensorAlgEquiv K C) (Algebra.TensorProduct.includeRight P)
      = MvPolynomial.map (algebraMap K C) P := by
  rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-- The extended ideal is the image of the base-changed ideal under `C ⊗_K K[X] ≅ C[X]`. -/
theorem idealOfPolysExt_eq_map_tensor (Ps : Finset (MvPolynomial (Fin k) K)) :
    idealOfPolysExt C Ps
      = Ideal.map (algebraTensorAlgEquiv K C)
          (Ideal.map (Algebra.TensorProduct.includeRight) (idealOfPolys Ps)) := by
  rw [idealOfPolysExt, idealOfPolys, idealOfPolys, Ideal.map_span, Ideal.map_span,
    ← Set.image_comp, Finset.coe_image]
  congr 1
  exact Set.image_congr fun P _ => (algebraTensorAlgEquiv_includeRight C P).symm

noncomputable def algEquivExt (Ps : Finset (MvPolynomial (Fin k) K)) :
    C ⊗[K] quotPolys Ps ≃ₐ[C] quotPolysExt C Ps :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := K) C (MvPolynomial (Fin k) K) C
      (idealOfPolys Ps)).trans
    (Ideal.quotientEquivAlg (Ideal.map (Algebra.TensorProduct.includeRight) (idealOfPolys Ps))
      (idealOfPolysExt C Ps) (algebraTensorAlgEquiv K C) (idealOfPolysExt_eq_map_tensor C Ps))

/-- **BPR Lemma 4.88.** `A = K[X]/Ideal(𝒫,K)` is finite-dimensional of dimension `m` over `K` if
and only if `Ā = C[X]/Ideal(𝒫,C)` is finite-dimensional of dimension `m` over `C`: the dimensions
agree, and one is finite-dimensional exactly when the other is. -/
theorem lemma_4_88 (Ps : Finset (MvPolynomial (Fin k) K)) :
    Module.finrank K (quotPolys Ps) = Module.finrank C (quotPolysExt C Ps) ∧
      (FiniteDimensional K (quotPolys Ps) ↔ FiniteDimensional C (quotPolysExt C Ps)) := by
  have e : quotPolysExt C Ps ≃ₗ[C] C ⊗[K] quotPolys Ps :=
    (algEquivExt C Ps).symm.toLinearEquiv
  refine ⟨?_, ?_, ?_⟩
  · rw [e.finrank_eq, Module.finrank_baseChange]
  · intro hA
    have := hA
    have : Module.Finite C (C ⊗[K] quotPolys Ps) := inferInstance
    exact Module.Finite.equiv (algEquivExt C Ps).toLinearEquiv
  · intro hAbar
    have := hAbar
    have : Module.Finite C (C ⊗[K] quotPolys Ps) := Module.Finite.equiv e
    let b := Module.Free.chooseBasis K (quotPolys Ps)
    have : Fintype (Module.Free.ChooseBasisIndex K (quotPolys Ps)) :=
      FiniteDimensional.fintypeBasisIndex (Algebra.TensorProduct.basis C b)
    exact Module.Finite.of_basis b

end Azurite.BPR.Chapter4
