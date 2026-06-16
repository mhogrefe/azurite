import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_b_c
import Azurite.BasuPollackRoy.Chapter4.Section4_3.Orthogonality
import Azurite.BasuPollackRoy.Chapter3.Section3_1.EuclideanBall
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# BPR Theorem 4.43: Spectral theorem over a real closed field

Let `M` be a symmetric matrix with entries in a real closed field `R`. Then the
eigenvalues of `M` lie in `R`, and there is an orthonormal basis of eigenvectors
with coordinates in `R`. Equivalently, there is an orthogonal matrix `A` over `R`
and a diagonal matrix `D` over `R` with `Aᵀ M A = D`.

The proof is by induction on `n`. The crux (`symm_exists_real_eigenvalue`) is that a
symmetric matrix over `R` has a *real* eigenvalue: viewing `M` over the algebraically
closed field `R[i] = Ri R`, its characteristic polynomial has a root `λ ∈ R[i]`; since
`M` is Hermitian over `R[i]` (its entries are real, so fixed by conjugation, and it is
symmetric), the standard `λ ⟨v, v⟩ = conj(λ) ⟨v, v⟩` argument with the
positive-definite Hermitian form forces `conj λ = λ`, i.e. `λ ∈ R`. Having a real
eigenvalue, we extract a real unit eigenvector, complete it to an orthonormal basis
(Proposition 4.41), and reduce `M` to a block `μ ⊕ M'` with `M'` symmetric of
dimension `n - 1`, then induct.
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open Azurite.BPR.Theorem2_11

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  {n : ℕ}

omit [IsRealClosed R] in
/-- For a vector `v` over `Ri R`, each summand `Ri.conj (v i) * v i` is the image of a
nonnegative real, and it is the image of `0` exactly when `v i = 0`. -/
private theorem norm_summand_nonneg (vi : Ri R) :
    ∃ a : R, algebraMap R (Ri R) a = (Ri.conj R) vi * vi ∧ 0 ≤ a ∧ (a = 0 ↔ vi = 0) := by
  by_cases hc : (Ri.conj R) vi = vi
  · -- `vi` is real: `vi = algebraMap R x`, product is `x^2`.
    obtain ⟨x, hx⟩ := Ri.conj_fixed_mem_range_ordered vi hc
    have hvi_x : vi = 0 ↔ x = 0 := by
      rw [← hx]; constructor
      · intro h; exact algebraMap_Ri_injective (by rw [h, map_zero])
      · intro h; rw [h, map_zero]
    refine ⟨x ^ 2, ?_, sq_nonneg _, ?_⟩
    · rw [map_pow, hx, hc]; ring
    · rw [hvi_x, pow_eq_zero_iff (n := 2) (by norm_num)]
  · -- `vi` is not real: `Ri.norm_pos_of_not_real` gives a positive real, and `vi ≠ 0`.
    obtain ⟨a, ha, hpos⟩ := Ri.norm_pos_of_not_real vi hc
    have hvi : vi ≠ 0 := by
      rintro rfl; simp at hc
    refine ⟨a, ?_, le_of_lt hpos, ?_⟩
    · rw [ha, mul_comm]
    · constructor
      · intro h; rw [h] at hpos; exact absurd hpos (lt_irrefl 0)
      · intro h; exact absurd h hvi

/-- **Key lemma.** A symmetric matrix over a real closed field has a real eigenvalue:
there is `μ ∈ R` with `det (μ • 1 - M) = 0`. Proved by viewing `M` as a Hermitian
matrix over the algebraically closed field `R[i] = Ri R`. -/
theorem symm_exists_real_eigenvalue [Nonempty (Fin n)]
    (M : Matrix (Fin n) (Fin n) R) (hM : M.IsSymm) :
    ∃ μ : R, (Matrix.scalar (Fin n) μ - M).det = 0 := by
  classical
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  set φ : R →+* Ri R := algebraMap R (Ri R) with hφ
  set M' : Matrix (Fin n) (Fin n) (Ri R) := M.map φ with hM'
  -- entries of `M'` are real (fixed by conj)
  have hMreal : ∀ i j, (Ri.conj R) (M' i j) = M' i j := by
    intro i j; simp only [hM', Matrix.map_apply]; exact Ri.conj_algebraMap_ordered _
  -- `M'` is symmetric
  have hM'symm : ∀ i j, M' i j = M' j i := by
    intro i j; simp only [hM', Matrix.map_apply]; rw [hM.apply i j]
  -- charpoly of `M'` has a root
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hn1 : 1 ≤ n := Fin.pos_iff_nonempty.mpr ‹Nonempty (Fin n)›
  have hcp_map : M'.charpoly = M.charpoly.map φ := by rw [hM', Matrix.charpoly_map]
  have hdeg : M'.charpoly.natDegree = n := by
    rw [hcp_map, Polynomial.natDegree_map_eq_of_injective algebraMap_Ri_injective,
      Matrix.charpoly_natDegree_eq_dim, hcard]
  have hdeg_ne : M'.charpoly.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (by
      intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega), hdeg]
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn1
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root M'.charpoly hdeg_ne
  have hlamdet : (Matrix.scalar (Fin n) lam - M').det = 0 := by
    rw [← Matrix.eval_charpoly M' lam]; exact hlam
  -- eigenvector v ≠ 0 with M' *ᵥ v = lam • v
  obtain ⟨v, hv0, hveq⟩ := (Matrix.exists_mulVec_eq_zero_iff
    (M := Matrix.scalar (Fin n) lam - M')).mpr hlamdet
  have heig : M' *ᵥ v = lam • v := by
    have h1 : (Matrix.scalar (Fin n) lam - M') *ᵥ v = lam • v - M' *ᵥ v := by
      rw [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.diagonal_const_mulVec]
    rw [h1] at hveq
    exact (sub_eq_zero.mp hveq).symm
  -- S := ∑ conj(v i) * v i
  set S : Ri R := ∑ i, (Ri.conj R) (v i) * v i with hS
  -- self-adjointness: conj(λ) * S = λ * S
  have hself : (Ri.conj R) lam * S = lam * S := by
    have lhs : ∑ i, (Ri.conj R) ((M' *ᵥ v) i) * v i
             = ∑ i, (Ri.conj R) (v i) * (M' *ᵥ v) i := by
      simp only [Matrix.mulVec, dotProduct]
      simp only [map_sum, map_mul, hMreal, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [hM'symm j i]; ring
    have hL : ∑ i, (Ri.conj R) ((M' *ᵥ v) i) * v i = (Ri.conj R) lam * S := by
      rw [heig]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, hS]
      apply Finset.sum_congr rfl; intro i _; ring
    have hR : ∑ i, (Ri.conj R) (v i) * (M' *ᵥ v) i = lam * S := by
      rw [heig]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, hS]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [← hL, lhs, hR]
  -- S = φ N with 0 < N
  set aval : Fin n → R := fun i => (norm_summand_nonneg (v i)).choose with haval
  have haval_spec : ∀ i, algebraMap R (Ri R) (aval i) = (Ri.conj R) (v i) * v i ∧
      0 ≤ aval i ∧ (aval i = 0 ↔ v i = 0) := fun i => (norm_summand_nonneg (v i)).choose_spec
  set N : R := ∑ i, aval i with hN
  have hSN : φ N = S := by
    rw [hS, hN, map_sum]
    apply Finset.sum_congr rfl; intro i _
    exact (haval_spec i).1
  have hN_nonneg : 0 ≤ N := Finset.sum_nonneg (fun i _ => (haval_spec i).2.1)
  have hN_pos : 0 < N := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    have hai_pos : 0 < aval i := lt_of_le_of_ne (haval_spec i).2.1
      (fun h => hi ((haval_spec i).2.2.1 h.symm))
    exact Finset.sum_pos' (fun j _ => (haval_spec j).2.1) ⟨i, Finset.mem_univ i, hai_pos⟩
  have hS_ne : S ≠ 0 := by
    rw [← hSN]; intro h
    exact (ne_of_gt hN_pos).symm (algebraMap_Ri_injective (by rw [h, map_zero]))
  -- cancel S
  have hlam_fixed : (Ri.conj R) lam = lam :=
    mul_right_cancel₀ hS_ne hself
  obtain ⟨μ, hμ⟩ := Ri.conj_fixed_mem_range_ordered lam hlam_fixed
  -- transfer det = 0 to R
  refine ⟨μ, ?_⟩
  have hmap : (Matrix.scalar (Fin n) μ - M).map φ = Matrix.scalar (Fin n) lam - M' := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.scalar_apply, map_sub, hM']
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hφ, hμ]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, map_zero]
  have : φ ((Matrix.scalar (Fin n) μ - M).det) = (Matrix.scalar (Fin n) lam - M').det := by
    rw [RingHom.map_det, ← hmap]
    rfl
  rw [hlamdet] at this
  exact algebraMap_Ri_injective (by rw [this, map_zero])

/-- A symmetric matrix over a real closed field has a real *unit* eigenvector. -/
theorem symm_exists_unit_eigenvector [Nonempty (Fin n)]
    (M : Matrix (Fin n) (Fin n) R) (hM : M.IsSymm) :
    ∃ (μ : R) (u : Fin n → R), u ⬝ᵥ u = 1 ∧ M *ᵥ u = μ • u := by
  classical
  obtain ⟨μ, hμ⟩ := symm_exists_real_eigenvalue M hM
  obtain ⟨w, hw0, hweq⟩ := (Matrix.exists_mulVec_eq_zero_iff
    (M := Matrix.scalar (Fin n) μ - M)).mpr hμ
  have hMw : M *ᵥ w = μ • w := by
    have h1 : (Matrix.scalar (Fin n) μ - M) *ᵥ w = μ • w - M *ᵥ w := by
      rw [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.diagonal_const_mulVec]
    rw [h1] at hweq
    exact (sub_eq_zero.mp hweq).symm
  set N : R := w ⬝ᵥ w with hN
  have hN_nonneg : 0 ≤ N := by
    rw [hN, dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have hN_ne : N ≠ 0 := fun h => hw0 (dotProduct_self_eq_zero.mp h)
  have hN_pos : 0 < N := lt_of_le_of_ne hN_nonneg (Ne.symm hN_ne)
  set s : R := Azurite.BPR.sqrt N with hs
  have hs_sq : s ^ 2 = N := Azurite.BPR.sq_sqrt hN_nonneg
  have hs_ne : s ≠ 0 := by
    intro h; rw [h] at hs_sq; simp at hs_sq; exact hN_ne hs_sq.symm
  set c : R := s⁻¹ with hc
  refine ⟨μ, c • w, ?_, ?_⟩
  · -- (c • w) ⬝ᵥ (c • w) = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc]
    rw [← hN]
    rw [hc]
    have : s⁻¹ * s⁻¹ * N = (s ^ 2)⁻¹ * N := by rw [sq]; rw [mul_inv]
    rw [this, hs_sq, inv_mul_cancel₀ hN_ne]
  · -- M *ᵥ (c • w) = μ • (c • w)
    rw [Matrix.mulVec_smul, hMw, smul_comm]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Auxiliary: extend a linearly independent family of size `j = m - d` up to a linearly
independent family of size `m`, keeping the original vectors as a prefix. Induction on the
gap `d`. -/
private theorem exists_linearIndependent_extend_aux {m : ℕ} :
    ∀ (d j : ℕ) (hj : j + d = m) (v : Fin j → (Fin m → R)), LinearIndependent R v →
      ∃ w : Fin m → (Fin m → R), LinearIndependent R w ∧
        ∀ i : Fin j, w (Fin.castLE (hj ▸ Nat.le_add_right j d) i) = v i := by
  intro d
  induction d with
  | zero =>
    intro j hj v hv
    subst hj
    simp only [Nat.add_zero] at *
    refine ⟨v, hv, fun i => ?_⟩
    exact congrArg v (Fin.ext (by simp))
  | succ e ih =>
    intro j hj v hv
    -- j < m, so we can snoc one vector
    have hjm : j < m := by omega
    have hfr : Module.finrank R (Fin m → R) = m := Module.finrank_fin_fun R
    have hlt : j < Module.finrank R (Fin m → R) := by rw [hfr]; exact hjm
    obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hv hlt
    obtain ⟨w, hw, hwpre⟩ := ih (j + 1) (by omega) (Fin.snoc v x) hx
    refine ⟨w, hw, fun i => ?_⟩
    have := hwpre (Fin.castSucc i)
    rw [Fin.snoc_castSucc] at this
    rw [← this]
    exact congrArg w (Fin.ext (by simp))

private theorem exists_orthonormal_first_col {m : ℕ} [NeZero m] (u : Fin m → R)
    (hu : u ⬝ᵥ u = 1) :
    ∃ Q : Matrix (Fin m) (Fin m) R, Qᵀ * Q = 1 ∧ (fun i => Q i 0) = u := by
  classical
  -- `u ≠ 0`
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp [dotProduct] at hu
  -- linearly independent family `![u]` of size 1
  have h1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  set v0 : Fin 1 → (Fin m → R) := ![u] with hv0
  have hv0_li : LinearIndependent R v0 := by
    rw [linearIndependent_unique_iff]
    simpa [hv0] using hu_ne
  obtain ⟨v, hv_li, hvpre⟩ :=
    exists_linearIndependent_extend_aux (m - 1) 1 (by omega) v0 hv0_li
  -- `v 0 = u`
  have hv_zero : v 0 = u := by
    have := hvpre 0
    rw [hv0] at this
    simpa [Fin.castLE, Fin.ext_iff] using this
  -- Gram–Schmidt
  obtain ⟨w, hw_li, hw_orth, hw_span⟩ := proposition_4_41 v hv_li
  -- `w 0 = v 0 = u`
  have hw_zero : w 0 = u := by
    have hspan0 := hw_span 0
    have hempty : {j : Fin m | j < 0} = ∅ := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact Fin.zero_le j
    rw [hempty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot,
      sub_eq_zero] at hspan0
    rw [hspan0, hv_zero]
  -- normalization
  have hN_nonneg : ∀ i, 0 ≤ w i ⬝ᵥ w i := fun i => by
    rw [dotProduct]; exact Finset.sum_nonneg (fun k _ => mul_self_nonneg (w i k))
  have hN_ne : ∀ i, w i ⬝ᵥ w i ≠ 0 := fun i h =>
    (hw_li.ne_zero i) (dotProduct_self_eq_zero.mp h)
  have hN_pos : ∀ i, 0 < w i ⬝ᵥ w i := fun i => lt_of_le_of_ne (hN_nonneg i) (Ne.symm (hN_ne i))
  set s : Fin m → R := fun i => Azurite.BPR.sqrt (w i ⬝ᵥ w i) with hs
  have hs_sq : ∀ i, (s i) ^ 2 = w i ⬝ᵥ w i := fun i => Azurite.BPR.sq_sqrt (hN_nonneg i)
  have hs_ne : ∀ i, s i ≠ 0 := fun i h => by
    have := hs_sq i; rw [h] at this; simp at this; exact hN_ne i this.symm
  set q : Fin m → (Fin m → R) := fun i => (s i)⁻¹ • w i with hq
  -- `sqrt 1 = 1`
  have hsqrt_one : Azurite.BPR.sqrt (1 : R) = 1 := by
    have h := Azurite.BPR.sq_sqrt (le_of_lt (zero_lt_one (α := R)))
    have hnn := Azurite.BPR.sqrt_nonneg (1 : R)
    nlinarith [h, hnn]
  -- `q 0 = u`
  have hq_zero : q 0 = u := by
    rw [hq]
    simp only
    rw [hw_zero]
    have : w 0 ⬝ᵥ w 0 = 1 := by rw [hw_zero]; exact hu
    rw [hs]
    simp only [this, hsqrt_one, inv_one, one_smul]
  -- orthonormality of `q`
  have hq_dot : ∀ i j, q i ⬝ᵥ q j = if i = j then 1 else 0 := by
    intro i j
    rw [hq]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      have hww : w i ⬝ᵥ w i = (s i) ^ 2 := (hs_sq i).symm
      rw [hww, if_pos rfl]
      field_simp
      exact div_self (hs_ne i)
    · have horth : w i ⬝ᵥ w j = 0 := hw_orth i j hij
      rw [horth]
      simp [hij]
  -- assemble `Q` with columns `q`
  refine ⟨Matrix.of (fun i j => q j i), ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    have : (∑ k, q i k * q j k) = q i ⬝ᵥ q j := by rw [dotProduct]
    rw [this, hq_dot i j]
  · funext i
    simp only [Matrix.of_apply]
    rw [hq_zero]

/-- **Theorem 4.43 (Spectral theorem over a real closed field).** A symmetric matrix
`M` over a real closed field `R` is orthogonally diagonalizable: there is an orthogonal
matrix `A` (`Aᵀ A = 1`) and a diagonal matrix over `R` with `Aᵀ M A` diagonal. The
eigenvalues (the diagonal entries) lie in `R`, and the columns of `A` form an
orthonormal basis of eigenvectors with coordinates in `R`. -/
theorem theorem_4_43 (M : Matrix (Fin n) (Fin n) R) (hM : M.IsSymm) :
    ∃ A : Matrix (Fin n) (Fin n) R, Aᵀ * A = 1 ∧
      ∃ D : Fin n → R, Aᵀ * M * A = Matrix.diagonal D := by
  classical
  suffices H : ∀ m (M : Matrix (Fin m) (Fin m) R), M.IsSymm →
      ∃ A : Matrix (Fin m) (Fin m) R, Aᵀ * A = 1 ∧
        ∃ D : Fin m → R, Aᵀ * M * A = Matrix.diagonal D by
    exact H n M hM
  intro m
  induction m with
  | zero =>
    intro M _
    refine ⟨1, by simp, 0, ?_⟩
    ext i
    exact Fin.elim0 i
  | succ k ih =>
    intro M hM
    -- eigenvector
    obtain ⟨μ, u, hu_unit, hMu⟩ := symm_exists_unit_eigenvector M hM
    -- orthonormal `Q` with first column `u`
    obtain ⟨Q, hQ, hQ0⟩ := exists_orthonormal_first_col u hu_unit
    set B : Matrix (Fin (k+1)) (Fin (k+1)) R := Qᵀ * M * Q with hB
    -- `B` is symmetric
    have hBsymm : B.IsSymm := by
      unfold Matrix.IsSymm
      rw [hB, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        hM.eq, mul_assoc]
    -- column 0 of `Q` is `u`
    have hQcol0 : Q *ᵥ (Pi.single 0 1) = u := by
      funext i
      rw [Matrix.mulVec_single]
      simp only [MulOpposite.op_one, one_smul, Matrix.col_apply]
      have : Q i 0 = u i := by rw [← hQ0]
      exact this
    -- `Qᵀ *ᵥ u = single 0 1`
    have hQtu : Qᵀ *ᵥ u = Pi.single 0 1 := by
      rw [← hQcol0, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
    -- `B *ᵥ single 0 1 = μ • single 0 1`
    have hBcol : B *ᵥ (Pi.single 0 1) = μ • (Pi.single 0 1) := by
      rw [hB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQcol0, hMu,
        Matrix.mulVec_smul, hQtu]
    rw [Matrix.mulVec_single_one] at hBcol
    -- entry facts for column 0 / row 0 of `B`
    have hBcol_entry : ∀ i, B i 0 = μ * (Pi.single (0 : Fin (k+1)) (1 : R) : Fin (k+1) → R) i := by
      intro i
      have := congrFun hBcol i
      simpa [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] using this
    have hBrow_entry : ∀ j, B 0 j = μ * (Pi.single (0 : Fin (k+1)) (1 : R) : Fin (k+1) → R) j := by
      intro j
      rw [hBsymm.apply j 0]
      exact hBcol_entry j
    -- sub-block `M'`
    set M' : Matrix (Fin k) (Fin k) R := Matrix.of (fun i j => B i.succ j.succ) with hM'
    have hM'symm : M'.IsSymm := by
      unfold Matrix.IsSymm
      ext i j
      simp only [Matrix.transpose_apply, hM', Matrix.of_apply]
      exact hBsymm.apply _ _
    obtain ⟨A', hA', D', hD'⟩ := ih M' hM'symm
    -- block-diagonal `C := 1 ⊕ A'`
    set C : Matrix (Fin (k+1)) (Fin (k+1)) R :=
      Matrix.of (fun i j => Fin.cases (Fin.cases (1 : R) (fun _ => 0) j)
        (fun i' => Fin.cases 0 (fun j' => A' i' j') j) i) with hC
    have hC00 : C 0 0 = 1 := by simp [hC]
    have hC0s : ∀ j', C 0 (Fin.succ j') = 0 := by intro j'; simp [hC]
    have hCs0 : ∀ i', C (Fin.succ i') 0 = 0 := by intro i'; simp [hC]
    have hCss : ∀ i' j', C (Fin.succ i') (Fin.succ j') = A' i' j' := by
      intro i' j'; simp [hC]
    -- A generic block-multiplication entry formula:
    -- `(Xᵀ * Y) (a) (b) = X 0 a * Y 0 b + ∑ x, X x.succ a * Y x.succ b`.
    have hmul_entry : ∀ (X Y : Matrix (Fin (k+1)) (Fin (k+1)) R) (a b : Fin (k+1)),
        (Xᵀ * Y) a b = X 0 a * Y 0 b + ∑ x : Fin k, X x.succ a * Y x.succ b := by
      intro X Y a b
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [Matrix.transpose_apply]
    -- `Cᵀ * C = 1`
    have hCC : Cᵀ * C = 1 := by
      ext i j
      rw [hmul_entry]
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · -- i = 0, j = 0
          rw [hC00, Matrix.one_apply_eq]
          have : ∀ x : Fin k, C x.succ 0 * C x.succ 0 = 0 := fun x => by rw [hCs0]; ring
          simp only [this, Finset.sum_const_zero, add_zero, mul_one]
        · -- i = 0, j = succ j'
          rw [hC00, hC0s, Matrix.one_apply_ne (Fin.succ_ne_zero j').symm]
          have : ∀ x : Fin k, C x.succ 0 * C x.succ (Fin.succ j') = 0 :=
            fun x => by rw [hCs0]; ring
          simp only [this, Finset.sum_const_zero, one_mul, zero_add]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · -- i = succ i', j = 0
          rw [hC0s, Matrix.one_apply_ne (Fin.succ_ne_zero i')]
          have : ∀ x : Fin k, C x.succ (Fin.succ i') * C x.succ 0 = 0 :=
            fun x => by rw [hCs0]; ring
          simp only [this, Finset.sum_const_zero, zero_mul, zero_add]
        · -- i = succ i', j = succ j'
          rw [hC0s, hC0s]
          simp only [hCss, zero_mul, zero_add]
          have hsum : (∑ x : Fin k, A' x i' * A' x j') = (A'ᵀ * A') i' j' := by
            rw [Matrix.mul_apply]; simp only [Matrix.transpose_apply]
          rw [hsum, hA']
          by_cases hij : i' = j'
          · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
          · rw [Matrix.one_apply_ne hij,
              Matrix.one_apply_ne (fun h => hij (Fin.succ_injective _ h))]
    -- clean entry facts for `B`
    have hB00 : B 0 0 = μ := by
      have := hBcol_entry 0; simpa using this
    have hB0s : ∀ j', B 0 (Fin.succ j') = 0 := by
      intro j'; have := hBrow_entry (Fin.succ j'); simpa [Pi.single_eq_of_ne (Fin.succ_ne_zero j')] using this
    have hBs0 : ∀ i', B (Fin.succ i') 0 = 0 := by
      intro i'; have := hBcol_entry (Fin.succ i'); simpa [Pi.single_eq_of_ne (Fin.succ_ne_zero i')] using this
    have hBss : ∀ i' j', B (Fin.succ i') (Fin.succ j') = M' i' j' := by
      intro i' j'; rw [hM']; simp
    -- assemble `A := Q * C`
    refine ⟨Q * C, ?_, Fin.cons μ D', ?_⟩
    · -- orthogonality
      rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc Qᵀ, hQ, Matrix.one_mul, hCC]
    · -- diagonalization
      have hAMA : (Q * C)ᵀ * M * (Q * C) = Cᵀ * B * C := by
        rw [Matrix.transpose_mul, hB]
        simp only [Matrix.mul_assoc]
      rw [hAMA]
      -- entry of an ordinary product, split off the `0` index
      have hmul_entry' : ∀ (X Y : Matrix (Fin (k+1)) (Fin (k+1)) R) (a b : Fin (k+1)),
          (X * Y) a b = X a 0 * Y 0 b + ∑ x : Fin k, X a x.succ * Y x.succ b := by
        intro X Y a b
        rw [Matrix.mul_apply, Fin.sum_univ_succ]
      -- entries of `B * C`
      have hBC0 : (B * C) 0 0 = μ := by
        rw [hmul_entry', hB00, hC00]
        have : ∀ x : Fin k, B 0 x.succ * C x.succ 0 = 0 := fun x => by rw [hB0s]; ring
        simp only [this, Finset.sum_const_zero, add_zero, mul_one]
      have hBC0s : ∀ j', (B * C) 0 (Fin.succ j') = 0 := by
        intro j'
        rw [hmul_entry', hB00, hC0s]
        have : ∀ x : Fin k, B 0 x.succ * C x.succ (Fin.succ j') = 0 :=
          fun x => by rw [hB0s]; ring
        simp only [this, Finset.sum_const_zero, mul_zero, add_zero]
      have hBCs0 : ∀ i', (B * C) (Fin.succ i') 0 = 0 := by
        intro i'
        rw [hmul_entry', hBs0, hC00]
        have : ∀ x : Fin k, B (Fin.succ i') x.succ * C x.succ 0 = 0 :=
          fun x => by rw [hCs0]; ring
        simp only [this, Finset.sum_const_zero, add_zero, zero_mul]
      have hBCss : ∀ i' j', (B * C) (Fin.succ i') (Fin.succ j')
          = ∑ x : Fin k, M' i' x * A' x j' := by
        intro i' j'
        rw [hmul_entry', hBs0, hC0s]
        simp only [mul_zero, zero_add]
        apply Finset.sum_congr rfl; intro x _
        rw [hBss, hCss]
      -- now compute `Cᵀ * B * C = Cᵀ * (B * C)` entries
      rw [Matrix.mul_assoc]
      ext i j
      rw [hmul_entry C (B * C) i j, Matrix.diagonal_apply]
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · -- i = 0, j = 0
          rw [hC00, hBC0, if_pos rfl, Fin.cons_zero]
          have : ∀ x : Fin k, C x.succ 0 * (B * C) x.succ 0 = 0 :=
            fun x => by rw [hCs0]; ring
          simp only [this, Finset.sum_const_zero, add_zero, one_mul]
        · -- i = 0, j = succ j'
          rw [hC00, hBC0s, if_neg (Fin.succ_ne_zero j').symm]
          have : ∀ x : Fin k, C x.succ 0 * (B * C) x.succ (Fin.succ j') = 0 :=
            fun x => by rw [hCs0]; ring
          simp only [this, Finset.sum_const_zero, mul_zero, add_zero]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · -- i = succ i', j = 0
          rw [hC0s, if_neg (Fin.succ_ne_zero i')]
          have : ∀ x : Fin k, C x.succ (Fin.succ i') * (B * C) x.succ 0 = 0 :=
            fun x => by rw [hBCs0]; ring
          simp only [this, Finset.sum_const_zero, zero_mul, add_zero]
        · -- i = succ i', j = succ j'
          rw [hC0s, zero_mul, zero_add]
          -- ∑ a, C a.succ (succ i') * (B*C) a.succ (succ j')
          --   = ∑ a, A' a i' * (∑ x, M' a x * A' x j') = (A'ᵀ * M' * A') i' j'
          have heq : ∀ a : Fin k, C a.succ (Fin.succ i') * (B * C) a.succ (Fin.succ j')
              = A' a i' * ∑ x : Fin k, M' a x * A' x j' := by
            intro a; rw [hCss, hBCss]
          simp only [heq]
          have hval : (∑ a : Fin k, A' a i' * ∑ x : Fin k, M' a x * A' x j')
              = (A'ᵀ * M' * A') i' j' := by
            simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro x _; ring
          rw [hval, hD', Matrix.diagonal_apply]
          by_cases hij : i' = j'
          · subst hij; rw [if_pos rfl, if_pos rfl, Fin.cons_succ]
          · rw [if_neg hij, if_neg (fun h => hij (Fin.succ_injective _ h))]

/-- **Theorem 4.43, eigenbasis form.** The columns of the orthogonal matrix `A` from
`theorem_4_43` form an *orthonormal basis of eigenvectors* of `M`: a linearly independent
family `a : Fin n → Rⁿ` with `a i ⬝ᵥ a j = δᵢⱼ` (orthonormal) and `M *ᵥ a j = D j • a j`
(each `a j` is an eigenvector), where the eigenvalues `D j` lie in `R`. -/
theorem theorem_4_43_orthonormal_eigenbasis (M : Matrix (Fin n) (Fin n) R) (hM : M.IsSymm) :
    ∃ (a : Fin n → (Fin n → R)) (D : Fin n → R),
      LinearIndependent R a ∧
      (∀ i j, a i ⬝ᵥ a j = if i = j then 1 else 0) ∧
      (∀ j, M *ᵥ a j = D j • a j) := by
  classical
  obtain ⟨A, hAo, D, hAD⟩ := theorem_4_43 M hM
  set a : Fin n → (Fin n → R) := fun j i => A i j with ha
  -- Orthonormality: `a i ⬝ᵥ a j = (Aᵀ * A) i j = δᵢⱼ`.
  have hortho : ∀ i j, a i ⬝ᵥ a j = if i = j then 1 else 0 := by
    intro i j
    have h1 : a i ⬝ᵥ a j = (Aᵀ * A) i j := by
      rw [Matrix.mul_apply]
      simp only [ha, dotProduct, Matrix.transpose_apply]
    rw [h1, hAo, Matrix.one_apply]
  refine ⟨a, D, ?_, hortho, ?_⟩
  · -- Linear independence: dot `∑ⱼ cⱼ • aⱼ = 0` with `aᵢ` to get `cᵢ = 0`.
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hdot : (∑ j, c j • a j) ⬝ᵥ a i = 0 := by rw [hc]; simp
    rw [sum_dotProduct] at hdot
    have hstep : (∑ j, (c j • a j) ⬝ᵥ a i) = ∑ j, (if j = i then c j else 0) :=
      Finset.sum_congr rfl fun j _ => by
        rw [smul_dotProduct, smul_eq_mul, hortho]; split <;> simp
    rw [hstep, Finset.sum_ite_eq', if_pos (Finset.mem_univ i)] at hdot
    exact hdot
  · -- Eigenvectors: from `A Aᵀ = 1`, `M A = A · diagonal D`, so column `j` is `D j • a j`.
    have hAAt : A * Aᵀ = 1 := mul_eq_one_comm.mpr hAo
    have hMA : M * A = A * Matrix.diagonal D := by
      calc M * A = A * Aᵀ * M * A := by rw [hAAt, Matrix.one_mul]
        _ = A * (Aᵀ * M * A) := by simp only [mul_assoc]
        _ = A * Matrix.diagonal D := by rw [hAD]
    intro j
    funext i
    have hlhs : (M *ᵥ a j) i = (M * A) i j := by
      simp only [ha, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hlhs, hMA, Matrix.mul_apply, Pi.smul_apply, ha, smul_eq_mul]
    simp [Matrix.diagonal_apply, Finset.sum_ite_eq', mul_comm]

end Azurite.BPR.Chapter4
