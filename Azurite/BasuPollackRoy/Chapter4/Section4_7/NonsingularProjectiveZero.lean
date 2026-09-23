import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveSpace
import Azurite.BasuPollackRoy.Chapter4.Section4_5.NonsingularZero
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# BPR §4.7: non-singular projective zeros

Let `R` be a real closed field and `C = R[i] = Ri R`. If `P₁, …, P_k` are homogeneous polynomials in
`C[X₀, …, X_k]` (so `k` polynomials in `k + 1` variables), a point
`x = (x₀ : x₁ : ⋯ : x_k) ∈ ℙ_k(C)` is a **non-singular projective zero** of `P₁, …, P_k` if

* `Pᵢ(x) = 0` for `i = 1, …, k`, and
* the `k × (k + 1)` Jacobian matrix `[∂Pᵢ/∂Xⱼ(x)]` (rows `i = 1, …, k`, columns `j = 0, …, k`) has
  rank `k`.

Both conditions are independent of the choice of homogeneous coordinates: scaling the coordinate
vector by `λ ≠ 0` scales each `Pᵢ` by `λ^{dᵢ}` (vanishing preserved) and each row `i` of the Jacobian
by `λ^{dᵢ - 1}` (rank preserved). We evaluate at the canonical representative `x.rep`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- The **projective Jacobian matrix** of `P : Fin k → C[X₀, …, X_k]` at a point
`x ∈ ℙ_k(C)`: the `k × (k + 1)` matrix whose `(i, j)` entry is `(∂Pᵢ/∂Xⱼ)(x)`, evaluated at the
representative `x.rep`. -/
noncomputable def projJacobian (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (x : complexProjectiveSpace R k) : Matrix (Fin k) (Fin (k + 1)) (Ri R) :=
  Matrix.of fun i j => aeval x.rep (pderiv j (P i))

/-- **BPR Definition (non-singular projective zero).** A point `x ∈ ℙ_k(C)` is a *non-singular
projective zero* of homogeneous polynomials `P₁, …, P_k` if it is a common zero (`Pᵢ(x) = 0` for all
`i`) and the `k × (k + 1)` projective Jacobian has rank `k`. -/
def IsNonsingularProjectiveZero (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (x : complexProjectiveSpace R k) : Prop :=
  (∀ i, aeval x.rep (P i) = 0) ∧ (projJacobian P x).rank = k

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- A nonzero first coordinate keeps the coordinate vector nonzero. -/
theorem cons_one_ne_zero (x : Fin k → Ri R) :
    (Fin.cons (1 : Ri R) x : Fin (k + 1) → Ri R) ≠ 0 := by
  intro h; have := congrFun h 0; simp [Fin.cons_zero] at this

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Evaluating a homogeneous polynomial of degree `n` at a scaled point `c • w` scales the value
by `c ^ n`. -/
theorem aeval_smul_isHomogeneous {φ : MvPolynomial (Fin (k + 1)) (Ri R)} {n : ℕ}
    (hφ : MvPolynomial.IsHomogeneous φ n) (c : Ri R) (w : Fin (k + 1) → Ri R) :
    aeval (c • w) φ = c ^ n * aeval w φ := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hdeg : (∑ i, u i) = n := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_apply]
    exact (hφ.degree_eq_sum_deg_support hu).symm
  have hsplit : (∏ s, ((c • w) s) ^ u s) = c ^ n * ∏ s, (w s) ^ u s := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  rw [hsplit]; ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Chain rule for the dehomogenizing substitution `X₀ ↦ 1`, `X_{a+1} ↦ X_a`: differentiating the
dehomogenization in the affine variable `a` equals dehomogenizing the partial derivative in
`X_{a+1}`. -/
theorem pderiv_aeval_cons_one
    (p : MvPolynomial (Fin (k + 1)) (Ri R)) (a : Fin k) :
    pderiv a (aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) p)
      = aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) (pderiv (Fin.succ a) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j h =>
    simp only [map_mul, Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, aeval_X, h]
    refine Fin.cases ?_ (fun b => ?_) j
    · simp [Fin.cons_zero, Fin.succ_ne_zero]
    · simp only [Fin.cons_succ, pderiv_X, Pi.single_apply, Fin.succ_inj]
      by_cases hab : b = a <;> simp [hab]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Evaluating the dehomogenization at `x` equals evaluating the original at `(1, x₁, …, x_k)`. -/
theorem aeval_aeval_cons_one (p : MvPolynomial (Fin (k + 1)) (Ri R)) (x : Fin k → Ri R) :
    aeval x (aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) p)
      = aeval (Fin.cons (1 : Ri R) x) p := by
  have h : (aeval x).comp (aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X))
      = aeval (Fin.cons (1 : Ri R) x) := by
    rw [comp_aeval]
    congr 1
    funext j
    refine Fin.cases ?_ (fun b => ?_) j
    · simp [Fin.cons_zero]
    · simp [Fin.cons_succ]
  exact DFunLike.congr_fun h p

/-- For a `k × (k+1)` matrix over a field whose `0`-th column lies in the span of the remaining
columns, full rank `k` is equivalent to nonvanishing of the determinant of the `k × k` block
obtained by deleting column `0`. -/
theorem rank_eq_iff_det_submatrix_succ_ne_zero {F : Type*} [Field F]
    (M : Matrix (Fin k) (Fin (k + 1)) F)
    (hcol : M.col 0 ∈ Submodule.span F (Set.range (M.submatrix id Fin.succ).col)) :
    M.rank = k ↔ (M.submatrix id Fin.succ).det ≠ 0 := by
  set Maff := M.submatrix id Fin.succ with hMaff
  -- The column ranges agree as spans, hence the ranks agree.
  have htail : Fin.tail M.col = Maff.col := rfl
  have hcols : Set.range M.col = insert (M.col 0) (Set.range Maff.col) := by
    rw [Fin.range_fin_succ M.col, htail]
  have hspan : Submodule.span F (Set.range M.col) = Submodule.span F (Set.range Maff.col) := by
    rw [hcols, Submodule.span_insert_eq_span hcol]
  have hrankeq : M.rank = Maff.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols, hspan]
  rw [hrankeq]
  constructor
  · intro hrank hdet
    -- det = 0 gives a nonzero kernel vector, contradicting full rank.
    obtain ⟨v, hv0, hvker⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Maff)).mpr hdet
    have : Maff.rank < k := by
      rw [Matrix.rank]
      have hle : LinearMap.range Maff.mulVecLin < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        have hinj : Function.Injective Maff.mulVecLin :=
          LinearMap.injective_iff_surjective.mpr (by rw [← LinearMap.range_eq_top]; exact htop)
        exact hv0 (hinj (by simpa using hvker))
      calc Module.finrank F (LinearMap.range Maff.mulVecLin)
          < Module.finrank F (⊤ : Submodule F (Fin k → F)) :=
            Submodule.finrank_lt_finrank_of_lt hle
        _ = Fintype.card (Fin k) := by
            rw [finrank_top, Module.finrank_fintype_fun_eq_card]
        _ = k := Fintype.card_fin k
    omega
  · intro hdet
    have : IsUnit Maff := (Matrix.isUnit_iff_isUnit_det Maff).mpr (isUnit_iff_ne_zero.mpr hdet)
    rw [Matrix.rank_of_isUnit Maff this, Fintype.card_fin]

/-- **BPR §4.7 (the Note).** `(x₁, …, x_k)` is a non-singular (affine) zero of the dehomogenizations
`Pᵢ(1, X₁, …, X_k)` iff `(1 : x₁ : ⋯ : x_k)` is a non-singular projective zero of `P₁, …, P_k`. -/
theorem isNonsingularZero_dehom_iff_isNonsingularProjectiveZero
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, MvPolynomial.IsHomogeneous (P i) (d i)) (x : Fin k → Ri R) :
    IsNonsingularZero (fun i => aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) (P i)) x ↔
      IsNonsingularProjectiveZero P (mkLine (Fin.cons (1 : Ri R) x) (cons_one_ne_zero x)) := by
  classical
  set v : Fin (k + 1) → Ri R := Fin.cons (1 : Ri R) x with hv
  set xp := mkLine v (cons_one_ne_zero x) with hxp
  -- (A) The representative `xp.rep` is a nonzero scalar multiple of `v`.
  obtain ⟨c, hc, hrep⟩ : ∃ c : Ri R, c ≠ 0 ∧ xp.rep = c • v := by
    have hmk : mkLine xp.rep (Projectivization.rep_nonzero xp) = mkLine v (cons_one_ne_zero x) := by
      rw [hxp, mkLine, Projectivization.mk_rep]
    exact (mkLine_eq_mkLine_iff _ _ _ _).mp hmk
  -- The `k × (k+1)` matrix `M` of partials evaluated at `v`.
  set M : Matrix (Fin k) (Fin (k + 1)) (Ri R) :=
    Matrix.of fun i j => aeval v (pderiv j (P i)) with hM
  -- (C) Common-zero equivalence.
  have hzero : (∀ i, aeval x (aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) (P i)) = 0) ↔
      (∀ i, aeval xp.rep (P i) = 0) := by
    apply forall_congr'
    intro i
    rw [aeval_aeval_cons_one, ← hv, hrep, aeval_smul_isHomogeneous (hP i)]
    constructor
    · intro h; rw [h, mul_zero]
    · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hc)
  -- (D) The affine Jacobian is the `k × k` block of `M` dropping column `0`.
  have hjac : jacobian (fun i => aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) (P i)) x
      = M.submatrix id Fin.succ := by
    ext i a
    simp only [jacobian, Matrix.of_apply, Matrix.submatrix_apply, id_eq, hM]
    rw [pderiv_aeval_cons_one, aeval_aeval_cons_one, ← hv]
  -- (E) The projective Jacobian at `xp.rep` is `M` with rows scaled by `c ^ (dᵢ - 1)`.
  have hproj : projJacobian P xp = Matrix.diagonal (fun i => c ^ (d i - 1)) * M := by
    ext i j
    rw [Matrix.diagonal_mul, projJacobian, Matrix.of_apply, hM, Matrix.of_apply, hrep,
      aeval_smul_isHomogeneous ((hP i).pderiv)]
  have hprojrank : (projJacobian P xp).rank = M.rank := by
    rw [hproj]
    apply Matrix.rank_mul_eq_right_of_isUnit_det
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hc)
  -- (F) Under the common zero, column `0` of `M` is a combination of the remaining columns (Euler).
  have hcol : (∀ i, aeval v (P i) = 0) →
      M.col 0 ∈ Submodule.span (Ri R) (Set.range (M.submatrix id Fin.succ).col) := by
    intro hcz
    -- Euler: `∑ j, v j * M i j = (d i) • aeval v (P i) = 0`.
    have heuler : ∀ i, ∑ j, v j * M i j = 0 := by
      intro i
      have := congrArg (aeval v) (hP i).sum_X_mul_pderiv
      rw [map_sum, map_nsmul, hcz i, nsmul_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, aeval_X, hM, Matrix.of_apply]
    -- Hence `M.col 0 = ∑ a, (-x a) • Maff.col a`.
    have hcoleq : M.col 0 = ∑ a : Fin k, (-x a) • (M.submatrix id Fin.succ).col a := by
      funext i
      have hi := heuler i
      rw [Fin.sum_univ_succ] at hi
      simp only [hv, Fin.cons_zero, Fin.cons_succ, one_mul] at hi
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, Matrix.submatrix_apply,
        id_eq, smul_eq_mul, Matrix.col_apply]
      simp only [neg_mul, Finset.sum_neg_distrib]
      linear_combination hi
    rw [hcoleq]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  -- Common zero at `xp.rep` is the same as common zero at `v` (scaling by `c ≠ 0`).
  have hvz : (∀ i, aeval xp.rep (P i) = 0) ↔ (∀ i, aeval v (P i) = 0) := by
    apply forall_congr'
    intro i
    rw [hrep, aeval_smul_isHomogeneous (hP i)]
    constructor
    · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hc)
    · intro h; rw [h, mul_zero]
  -- Assemble: unfold both sides and combine the pieces.
  rw [IsNonsingularZero, IsNonsingularProjectiveZero, hjac, hprojrank, hzero]
  refine and_congr_right fun hcz => ?_
  rw [rank_eq_iff_det_submatrix_succ_ne_zero M (hcol (hvz.mp hcz))]

end Azurite.BPR.Chapter4
