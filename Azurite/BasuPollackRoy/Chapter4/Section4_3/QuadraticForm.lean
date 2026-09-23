import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant

/-!
# BPR §4.3.1: Quadratic forms

A quadratic form with coefficients in a field `K` (of characteristic zero) is a
homogeneous degree-2 polynomial `Φ(f₁, …, fₙ) = ∑_{i,j} m_{i,j} fᵢ fⱼ` given by a
symmetric matrix `M = [m_{i,j}]`; writing `f = (f₁, …, fₙ)`, `Φ = f · M · fᵗ`.

Both the form and its rank are Mathlib notions; we expose BPR-facing names:

* `quadraticForm M` is `Matrix.toQuadraticForm' M`, the map `x ↦ x · M · xᵗ`;
* `quadraticFormRank M` is the rank `Matrix.rank M` of the matrix.
-/

namespace Azurite.BPR.Chapter4

variable {K : Type*} [Field K] {n : ℕ}

/-- **BPR quadratic form.** The quadratic form attached to a (symmetric) matrix
`M`, namely `Φ(f) = f · M · fᵗ = ∑_{i,j} m_{i,j} fᵢ fⱼ`. This is Mathlib's
`Matrix.toQuadraticForm'`. -/
noncomputable def quadraticForm (M : Matrix (Fin n) (Fin n) K) : QuadraticForm K (Fin n → K) :=
  M.toQuadraticForm'

/-- **Rank of a BPR quadratic form.** The rank of `Φ` is the rank of its matrix
`M` (Mathlib's `Matrix.rank`). -/
noncomputable def quadraticFormRank (M : Matrix (Fin n) (Fin n) K) : ℕ := M.rank

/-- **BPR diagonal expression of a quadratic form.** A *diagonal expression* of
`Φ` is an identity
`Φ(f₁, …, fₙ) = ∑_{i=1}^r cᵢ · Lᵢ(f₁, …, fₙ)²`
with `cᵢ ∈ K`, `cᵢ ≠ 0`, and the `Lᵢ` linearly independent linear forms with
coefficients in `K`. The elements `c₁, …, c_r` are the *coefficients* of the
diagonal expression. (One has `r = Rank(Φ)`; see the blueprint note.) -/
structure DiagonalExpression (Φ : QuadraticForm K (Fin n → K)) where
  /-- the number of terms (equal to the rank of `Φ`) -/
  r : ℕ
  /-- the coefficients `cᵢ` of the diagonal expression -/
  coeff : Fin r → K
  /-- the linear forms `Lᵢ` -/
  form : Fin r → ((Fin n → K) →ₗ[K] K)
  /-- each coefficient is nonzero -/
  coeff_ne_zero : ∀ i, coeff i ≠ 0
  /-- the linear forms are linearly independent -/
  form_indep : LinearIndependent K form
  /-- the diagonalizing identity `Φ(f) = ∑ᵢ cᵢ · Lᵢ(f)²` -/
  apply_eq : ∀ f, Φ f = ∑ i, coeff i * (form i f) ^ 2

/-! ### Theorem 4.39: Sylvester's law of inertia

Existence of a diagonal expression and well-definedness of the signature are
glued onto Mathlib's inertia machinery (`sigPos`/`sigNeg`,
`equivalent_weightedSumSquares`, `sigPos_of_equiv_weightedSumSquares`). -/

/-- The linear forms `f ↦ (e f) i` for a linear automorphism `e` of `Fin n → K`,
realized as `e.dualMap` applied to the standard dual basis (the projections). -/
private noncomputable def equivForm (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (i : Fin n) :
    (Fin n → K) →ₗ[K] K :=
  e.dualMap ((Pi.basisFun K (Fin n)).dualBasis i)

private theorem equivForm_apply (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (i : Fin n)
    (f : Fin n → K) : equivForm e i f = (e f) i := by
  rw [equivForm, LinearEquiv.dualMap_apply, Module.Basis.dualBasis_apply, Pi.basisFun_repr]

private theorem equivForm_indep (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    LinearIndependent K (equivForm e) := by
  have hb : LinearIndependent K (fun i => (Pi.basisFun K (Fin n)).dualBasis i) :=
    (Pi.basisFun K (Fin n)).dualBasis.linearIndependent
  have := hb.map' e.dualMap.toLinearMap (LinearEquiv.ker e.dualMap)
  exact this

/-- Core construction: from a diagonalizing identity `Φ f = ∑ i, w i * ((e f) i)^2`
with `e` a linear automorphism, produce a `DiagonalExpression` by dropping the
zero weights. -/
private theorem diagExpr_of_equiv (Φ : QuadraticForm K (Fin n → K))
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (w : Fin n → K)
    (hΦ : ∀ f, Φ f = ∑ i, w i * ((e f) i) ^ 2) :
    Nonempty (DiagonalExpression Φ) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => w i ≠ 0)
  have hmem : ∀ i, i ∈ s ↔ w i ≠ 0 := by
    intro i; simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨{
    r := s.card
    coeff := fun j => w (s.equivFin.symm j : Fin n)
    form := fun j => equivForm e (s.equivFin.symm j : Fin n)
    coeff_ne_zero := ?_
    form_indep := ?_
    apply_eq := ?_ }⟩
  · intro j
    exact (hmem _).mp (s.equivFin.symm j).2
  · have hinj : Function.Injective (fun j => (s.equivFin.symm j : Fin n)) := by
      intro a b hab
      exact s.equivFin.symm.injective (Subtype.ext hab)
    exact (equivForm_indep e).comp _ hinj
  · intro f
    rw [hΦ f]
    -- restrict the sum to nonzero weights
    have hrestrict : ∑ i, w i * ((e f) i) ^ 2 = ∑ i ∈ s, w i * ((e f) i) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      rw [not_imp_comm.mp (hmem i).mpr hi, zero_mul]
    rw [hrestrict, ← Finset.sum_coe_sort s (fun i => w i * ((e f) i) ^ 2),
      ← Equiv.sum_comp s.equivFin.symm (fun i => w (i : Fin n) * ((e f) (i : Fin n)) ^ 2)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [equivForm_apply]

/-- **Sylvester, existence part.** Every quadratic form on `Fin n → K` (over a
field where `2` is invertible) has a diagonal expression: extract the linear forms
from Mathlib's weighted-sum-of-squares diagonalization and drop the zero weights. -/
theorem exists_diagonalExpression [Invertible (2 : K)] (Φ : QuadraticForm K (Fin n → K)) :
    Nonempty (DiagonalExpression Φ) := by
  obtain ⟨w, ⟨e⟩⟩ := Φ.equivalent_weightedSumSquares
  have h : Module.finrank K (Fin n → K) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  set φ := finCongr h with hφ
  -- transport the weights and the equiv to be indexed by `Fin n`
  refine diagExpr_of_equiv Φ
    (e.toLinearEquiv.trans (LinearEquiv.funCongrLeft K K φ.symm))
    (fun i => w (φ.symm i)) (fun f => ?_)
  have hmap : (QuadraticMap.weightedSumSquares K w) (e f) = Φ f := e.map_app f
  rw [← hmap, QuadraticMap.weightedSumSquares_apply,
    ← Equiv.sum_comp φ.symm (fun j => w j • (e f j * e f j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    QuadraticMap.IsometryEquiv.coe_toLinearEquiv, smul_eq_mul, sq]

/-- `Module.Basis.sumExtend` keeps the original family on the left summand. -/
private theorem sumExtend_inl {V : Type*} [AddCommGroup V] [Module K V] {ι : Type*}
    {v : ι → V} (hs : LinearIndependent K v) (i : ι) :
    Module.Basis.sumExtend hs (Sum.inl i) = v i := by
  classical
  calc Module.Basis.sumExtend hs (Sum.inl i)
      = Module.Basis.extend hs.linearIndepOn_id
          (((Equiv.ofInjective v hs.injective).sumCongr (Equiv.refl _)).trans
            (Equiv.Set.sumDiffSubset
              (hs.linearIndepOn_id.subset_extend (Set.subset_univ _)))
            (Sum.inl i)) :=
        Module.Basis.reindex_apply _ _ _
    _ = v i := by
        rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
          Equiv.Set.sumDiffSubset_apply_inl, Module.Basis.coe_extend]
        rfl

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
  {Φ : QuadraticForm K (Fin n → K)}

/-- The number of positive coefficients of a diagonal expression. -/
noncomputable def DiagonalExpression.posCount (de : DiagonalExpression Φ) : ℕ :=
  (Finset.univ.filter (fun i => 0 < de.coeff i)).card

/-- The number of negative coefficients of a diagonal expression. -/
noncomputable def DiagonalExpression.negCount (de : DiagonalExpression Φ) : ℕ :=
  (Finset.univ.filter (fun i => de.coeff i < 0)).card

/-- The signature of a diagonal expression: positive minus negative coefficients. -/
noncomputable def DiagonalExpression.signature (de : DiagonalExpression Φ) : ℤ :=
  (de.posCount : ℤ) - de.negCount

/-- Negating the coefficients of a diagonal expression of `Φ` gives one of `-Φ`. -/
def DiagonalExpression.neg (de : DiagonalExpression Φ) : DiagonalExpression (-Φ) where
  r := de.r
  coeff i := - de.coeff i
  form := de.form
  coeff_ne_zero i := neg_ne_zero.mpr (de.coeff_ne_zero i)
  form_indep := de.form_indep
  apply_eq f := by
    simp only [neg_apply, de.apply_eq, neg_mul, Finset.sum_neg_distrib]

@[simp] theorem DiagonalExpression.neg_posCount (de : DiagonalExpression Φ) :
    de.neg.posCount = de.negCount := by
  unfold DiagonalExpression.posCount DiagonalExpression.negCount
  exact congrArg Finset.card
    (@Finset.filter_congr _ _ _
      (fun _ => LinearOrder.toDecidableLT _ _)
      (fun _ => LinearOrder.toDecidableLT _ _) _
      (fun i _ => neg_pos (a := de.coeff i)))

/-- **Sylvester, uniqueness part (positive).** The number of positive coefficients
of any diagonal expression of `Φ` equals the positive inertia index `sigPos Φ`.
Proved by realizing the diagonal expression as a weighted sum of squares (extending
the linear forms to a basis) and invoking `sigPos_of_equiv_weightedSumSquares`. -/
theorem DiagonalExpression.posCount_eq_sigPos (de : DiagonalExpression Φ) :
    de.posCount = sigPos Φ := by
  classical
  -- extend the linearly independent forms to a basis of the dual space
  set B := Module.Basis.sumExtend de.form_indep with hB
  have : FiniteDimensional K (Module.Dual K (Fin n → K)) := inferInstance
  have : Fintype ↥(Module.Basis.sumExtendIndex de.form_indep) := by
    haveI : Fintype (Fin de.r ⊕ ↥(Module.Basis.sumExtendIndex de.form_indep)) :=
      FiniteDimensional.fintypeBasisIndex B
    exact Fintype.ofInjective
      (Sum.inr : ↥(Module.Basis.sumExtendIndex de.form_indep) → Fin de.r ⊕ _)
      Sum.inr_injective
  -- the coordinate isomorphism `f ↦ (idx ↦ B idx f)`
  set e : (Fin n → K) ≃ₗ[K]
      (Fin de.r ⊕ ↥(Module.Basis.sumExtendIndex de.form_indep) → K) :=
    (Module.evalEquiv K (Fin n → K)).trans B.dualBasis.equivFun with he_def
  have he : ∀ f idx, e f idx = B idx f := by
    intro f idx
    rw [he_def]
    simp only [LinearEquiv.trans_apply, Module.Basis.equivFun_apply,
      Module.Basis.dualBasis_repr, Module.evalEquiv_apply, Module.Dual.eval_apply]
  -- the diagonal weights
  set w : (Fin de.r ⊕ ↥(Module.Basis.sumExtendIndex de.form_indep)) → K :=
    Sum.elim de.coeff (fun _ => 0) with hw
  -- build the isometry equivalence
  have hequiv : QuadraticMap.Equivalent Φ (QuadraticMap.weightedSumSquares K w) := by
    refine ⟨{ toLinearEquiv := e, map_app' := fun f => ?_ }⟩
    show QuadraticMap.weightedSumSquares K w (e f) = Φ f
    rw [QuadraticMap.weightedSumSquares_apply]
    simp only [he]
    rw [Fintype.sum_sum_type]
    simp only [hw, Sum.elim_inl, Sum.elim_inr, smul_eq_mul, zero_mul,
      Finset.sum_const_zero, add_zero]
    rw [de.apply_eq f]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hB, sumExtend_inl, sq]
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares hequiv]
  -- relate the `ncard` of positive weights to `posCount`
  have hset : {i | 0 < w i} = Sum.inl '' {j | 0 < de.coeff j} := by
    ext idx
    cases idx with
    | inl j => simp [hw]
    | inr c => simp [hw]
  rw [hset, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, DiagonalExpression.posCount]

theorem DiagonalExpression.negCount_eq_sigNeg (de : DiagonalExpression Φ) :
    de.negCount = sigNeg Φ := by
  rw [← de.neg_posCount, de.neg.posCount_eq_sigPos, sigPos_neg]

/-- **BPR Theorem 4.39 (Sylvester's law of inertia).** Over an ordered field of
characteristic zero: (1) every quadratic form on `Fin n → K` has a diagonal
expression; (2) the signature (number of positive minus number of negative
coefficients) is the same for any two diagonal expressions of the same form. -/
theorem theorem_4_39 :
    (∀ Ψ : QuadraticForm K (Fin n → K), Nonempty (DiagonalExpression Ψ)) ∧
    (∀ (Ψ : QuadraticForm K (Fin n → K)) (de₁ de₂ : DiagonalExpression Ψ),
      de₁.signature = de₂.signature) := by
  have h2 : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  refine ⟨fun Ψ => exists_diagonalExpression Ψ, fun Ψ de₁ de₂ => ?_⟩
  simp only [DiagonalExpression.signature, de₁.posCount_eq_sigPos, de₂.posCount_eq_sigPos,
    de₁.negCount_eq_sigNeg, de₂.negCount_eq_sigNeg]

/-- **BPR signature of a quadratic form.** When `K` is ordered, `Sign(Φ)` is the
difference between the number of positive and the number of negative coefficients
`cᵢ` in a diagonal expression of `Φ` — a well-defined quantity by Theorem 4.39
(`DiagonalExpression.signature_eq`). Intrinsically it is the difference of the
positive and negative inertia indices of `Φ`. -/
noncomputable def Sign (Φ : QuadraticForm K (Fin n → K)) : ℤ :=
  (sigPos Φ : ℤ) - sigNeg Φ

/-- The signature of any diagonal expression of `Φ` is `Sign(Φ)`: this is the
well-definedness of the signature (Theorem 4.39) made explicit. -/
theorem DiagonalExpression.signature_eq (de : DiagonalExpression Φ) :
    de.signature = Sign Φ := by
  rw [DiagonalExpression.signature, de.posCount_eq_sigPos, de.negCount_eq_sigNeg, Sign]

omit [IsStrictOrderedRing K] in
/-- Over an ordered field every coefficient is positive or negative, so the number
of terms splits as `r = (#positive) + (#negative)`. -/
theorem DiagonalExpression.r_eq_posCount_add_negCount (de : DiagonalExpression Φ) :
    de.r = de.posCount + de.negCount := by
  have key := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin de.r))) (p := fun i => 0 < de.coeff i)
  rw [Finset.card_univ, Fintype.card_fin] at key
  have hneg : (Finset.univ.filter (fun i => ¬ 0 < de.coeff i))
      = Finset.univ.filter (fun i => de.coeff i < 0) :=
    Finset.filter_congr fun i _ => by
      rw [not_lt]
      exact ⟨fun h => h.lt_of_ne (de.coeff_ne_zero i), le_of_lt⟩
  rw [DiagonalExpression.posCount, DiagonalExpression.negCount, ← hneg]
  exact key.symm

/-- **The number of terms of a diagonal expression equals the rank of the form**
(the intrinsic rank `sigPos Φ + sigNeg Φ = n − dim(radical)`). This is the
intrinsic form of BPR's note "`r = Rank(Φ)`". -/
theorem DiagonalExpression.r_eq_sigPos_add_sigNeg (de : DiagonalExpression Φ) :
    de.r = sigPos Φ + sigNeg Φ := by
  rw [de.r_eq_posCount_add_negCount, de.posCount_eq_sigPos, de.negCount_eq_sigNeg]

/-- For a symmetric matrix `M`, the bilinear form `x, y ↦ x · M · y` is symmetric. -/
private theorem toLinearMap₂'_symm {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : M.IsSymm) (x y : Fin n → K) :
    Matrix.toLinearMap₂' K M x y = Matrix.toLinearMap₂' K M y x := by
  rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply']
  conv_lhs => rw [show M = M.transpose from hM.symm]
  rw [Matrix.dotProduct_transpose_mulVec]

/-- **The matrix of `M.toQuadraticForm'` is `M`** when `M` is symmetric: the
associated bilinear map of `Matrix.toQuadraticForm' M` is `Matrix.toLinearMap₂' K M`
(by symmetry), whose `toMatrix₂'` is `M`. -/
private theorem toMatrix'_toQuadraticForm' {K : Type*} [Field K] [Invertible (2 : K)] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : M.IsSymm) :
    (Matrix.toQuadraticForm' M).toMatrix' = M := by
  rw [QuadraticForm.toMatrix']
  have hassoc : QuadraticMap.associated (Matrix.toQuadraticForm' M)
      = Matrix.toLinearMap₂' K M :=
    QuadraticMap.associated_left_inverse K (toLinearMap₂'_symm M hM)
  rw [hassoc, LinearMap.toMatrix'_toLinearMap₂']

/-- **The matrix of `weightedSumSquares K w` is `diagonal w`.** `weightedSumSquares K w`
is `(diagonal w).toQuadraticForm'`, and `diagonal w` is symmetric. -/
private theorem toMatrix'_weightedSumSquares {K : Type*} [Field K] [Invertible (2 : K)] {n : ℕ}
    (w : Fin n → K) :
    QuadraticForm.toMatrix' (QuadraticMap.weightedSumSquares K w) = Matrix.diagonal w := by
  have heq : QuadraticMap.weightedSumSquares K w = Matrix.toQuadraticForm' (Matrix.diagonal w) := by
    ext v
    rw [QuadraticMap.weightedSumSquares_apply]
    show _ = Matrix.toLinearMap₂' K (Matrix.diagonal w) v v
    rw [Matrix.toLinearMap₂'_apply]
    simp [Matrix.diagonal_apply, Finset.sum_ite_eq, smul_eq_mul, mul_comm, mul_left_comm]
  rw [heq, toMatrix'_toQuadraticForm' _ (Matrix.isSymm_diagonal w)]

/-- The isometry reindexing a weighted sum of squares by a bijection `φ : Fin n ≃ Fin m`,
giving `weightedSumSquares K w ≃ weightedSumSquares K (w ∘ φ)`. -/
private noncomputable def weightedSumSquaresReindex {K : Type*} [Field K] [Invertible (2 : K)]
    {n m : ℕ} (w : Fin m → K) (φ : Fin n ≃ Fin m) :
    QuadraticMap.IsometryEquiv (QuadraticMap.weightedSumSquares K w)
      (QuadraticMap.weightedSumSquares K (w ∘ φ)) where
  toLinearEquiv := LinearEquiv.funCongrLeft K K φ
  map_app' x := by
    show QuadraticMap.weightedSumSquares K (w ∘ φ) _ = QuadraticMap.weightedSumSquares K w x
    rw [QuadraticMap.weightedSumSquares_apply, QuadraticMap.weightedSumSquares_apply,
      ← Equiv.sum_comp φ (fun j => w j • (x j * x j))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

/-- **BPR Corollary 4.40.** Matrix form of Sylvester's law: a symmetric matrix `M`
is congruent to a diagonal one — there exist an invertible `B` and `D` with
`M = B · diagonal D · Bᵀ`, where `D` has `sigPos (quadraticForm M)` positive and
`sigNeg (quadraticForm M)` negative entries. Built from Mathlib's
`equivalent_weightedSumSquares` isometry via the congruence law `toMatrix'_comp`. -/
theorem corollary_4_40 (M : Matrix (Fin n) (Fin n) K) (hM : M.IsSymm) :
    ∃ (B : Matrix (Fin n) (Fin n) K) (D : Fin n → K),
      IsUnit B.det ∧ M = B * Matrix.diagonal D * B.transpose ∧
      (Finset.univ.filter (fun i => 0 < D i)).card = sigPos (quadraticForm M) ∧
      (Finset.univ.filter (fun i => D i < 0)).card = sigNeg (quadraticForm M) := by
  classical
  have h2 : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  -- Diagonalize `quadraticForm M` as a weighted sum of squares, reindexed by `Fin n`.
  obtain ⟨w, ⟨e₀⟩⟩ := (quadraticForm M).equivalent_weightedSumSquares
  have hfin : Module.finrank K (Fin n → K) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  set φ : Fin n ≃ Fin (Module.finrank K (Fin n → K)) := finCongr hfin.symm with hφ
  set D : Fin n → K := w ∘ φ with hD
  -- isometry `quadraticForm M ≃ weightedSumSquares K D`
  set e : QuadraticMap.IsometryEquiv (quadraticForm M) (QuadraticMap.weightedSumSquares K D) :=
    e₀.trans (weightedSumSquaresReindex w φ) with he
  -- the change-of-basis matrix and its invertibility
  set P : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap with hP
  have hPunit : IsUnit P.det := by
    rw [hP, ← LinearMap.toMatrix_eq_toMatrix']
    exact LinearEquiv.isUnit_det e.toLinearEquiv (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n))
  -- the congruence identity `M = Pᵀ * diagonal D * P`
  have hcongr : M = P.transpose * Matrix.diagonal D * P := by
    have hcomp : quadraticForm M
        = (QuadraticMap.weightedSumSquares K D).comp e.toLinearEquiv.toLinearMap := by
      ext x
      rw [QuadraticMap.comp_apply]
      exact (e.map_app x).symm
    have hmat := QuadraticForm.toMatrix'_comp (QuadraticMap.weightedSumSquares K D)
      e.toLinearEquiv.toLinearMap
    rw [← hcomp] at hmat
    rw [show (quadraticForm M).toMatrix' = M from toMatrix'_toQuadraticForm' M hM,
      toMatrix'_weightedSumSquares D] at hmat
    rw [hmat, ← hP]
  refine ⟨P.transpose, D, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_transpose]; exact hPunit
  · rw [hcongr, Matrix.transpose_transpose]
  · -- positive count = sigPos
    have := QuadraticForm.sigPos_of_equiv_weightedSumSquares (Q := quadraticForm M) (w := D) ⟨e⟩
    rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  · -- negative count = sigNeg
    have := QuadraticForm.sigNeg_of_equiv_weightedSumSquares (Q := quadraticForm M) (w := D) ⟨e⟩
    rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- **The matrix rank equals `r₊ + r₋`** (matrix form of `r = Rank(Φ)`): the rank of
a symmetric matrix is the sum of the positive and negative inertia indices of its
quadratic form. Follows from Corollary 4.40 (rank is congruence-invariant). -/
theorem quadraticFormRank_eq_sigPos_add_sigNeg
    (M : Matrix (Fin n) (Fin n) K) (hM : M.IsSymm) :
    quadraticFormRank M = sigPos (quadraticForm M) + sigNeg (quadraticForm M) := by
  classical
  obtain ⟨B, D, hBunit, hMeq, hpos, hneg⟩ := corollary_4_40 M hM
  have hBtunit : IsUnit B.transpose.det := by rw [Matrix.det_transpose]; exact hBunit
  -- rank is invariant under congruence with an invertible matrix
  have hrank : M.rank = (Matrix.diagonal D).rank := by
    rw [hMeq, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hBtunit,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hBunit]
  -- the rank of a diagonal matrix is the number of nonzero entries
  rw [quadraticFormRank, hrank, Matrix.rank_diagonal, ← hpos, ← hneg]
  -- count nonzero = positive + negative (over a linear order)
  rw [Fintype.card_subtype]
  have hne : (Finset.univ.filter (fun i => D i ≠ 0))
      = Finset.univ.filter (fun i => 0 < D i)
        ∪ Finset.univ.filter (fun i => D i < 0) := by
    rw [← Finset.filter_or]
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h; rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    · rintro (h | h)
      · exact ne_of_gt h
      · exact ne_of_lt h
  have hdisj : Disjoint (Finset.univ.filter (fun i => 0 < D i))
      (Finset.univ.filter (fun i => D i < 0)) := by
    rw [Finset.disjoint_filter]
    exact fun i _ h => (lt_asymm h)
  rw [hne, Finset.card_union_of_disjoint hdisj]

/-- **BPR's note `r = Rank(Φ)`, now proved.** The number of terms of any diagonal
expression of `quadraticForm M` equals the matrix rank `Rank(Φ) = M.rank`. -/
theorem DiagonalExpression.r_eq_quadraticFormRank {M : Matrix (Fin n) (Fin n) K}
    (hM : M.IsSymm) (de : DiagonalExpression (quadraticForm M)) :
    de.r = quadraticFormRank M := by
  rw [de.r_eq_sigPos_add_sigNeg, quadraticFormRank_eq_sigPos_add_sigNeg M hM]

end Ordered

end Azurite.BPR.Chapter4
