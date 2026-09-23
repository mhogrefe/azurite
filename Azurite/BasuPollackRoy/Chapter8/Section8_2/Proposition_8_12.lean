import Azurite.BasuPollackRoy.Chapter4.Section4_3.Orthogonality
import Azurite.BasuPollackRoy.Chapter3.Section3_1.EuclideanBall
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Example_2_10
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# BPR §8.2.1 Proposition 8.12: Hadamard's inequality

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.2.

**Hadamard's inequality.** For an `n × n` integer matrix `M`, the absolute value
of `det(M)` is bounded by the product of the euclidean norms of the columns of `M`:

  `|det(M)| ≤ ∏ᵢ ‖cᵢ‖`,  where `cᵢ` is the `i`-th column.

Following BPR, the proof uses Gram–Schmidt orthogonalization (Proposition 4.41).
If the columns `v₁, …, vₙ` are linearly dependent then `det(M) = 0` and the bound
is trivial. Otherwise Gram–Schmidt yields pairwise-orthogonal `w₁, …, wₙ` with
`wᵢ − vᵢ ∈ span(w₁, …, w_{i-1})` and `wᵢ − vᵢ ∈ span(v₁, …, v_{i-1})`. The second
property makes the change-of-basis matrix from `v` to `w` triangular with unit
diagonal, so `det(M) = det(W)` where `W` has columns `wᵢ`; orthogonality gives
`WᵀW = diag(‖wᵢ‖²)`, hence `det(M)² = det(W)² = ∏ᵢ ‖wᵢ‖²`. The first property
(orthogonal decomposition `vᵢ = wᵢ − uᵢ` with `wᵢ ⊥ uᵢ`) gives `‖wᵢ‖ ≤ ‖vᵢ‖`,
so `det(M)² = ∏ᵢ ‖wᵢ‖² ≤ ∏ᵢ ‖vᵢ‖²`, i.e. `|det(M)| ≤ ∏ᵢ ‖vᵢ‖`.

We prove a squared, sqrt-free core (`det_sq_le_prod_dotProduct_col`) over any
ordered field, then the euclidean-norm form over a real closed field
(`abs_det_le_prod_euclideanNorm_col`), then specialize to integer matrices
(`proposition_8_12`). The euclidean norm is the §3.1 `Azurite.BPR.euclideanNorm`.
-/

namespace Azurite.BPR

open Matrix Module

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ}

/-- **Hadamard's inequality, squared form.** Over an ordered field, the square of
the determinant of `M` is bounded by the product of the squared euclidean norms of
its columns, `det(M)² ≤ ∏ᵢ (cᵢ · cᵢ)`. (No square roots, so this holds over any
ordered field.) -/
theorem det_sq_le_prod_dotProduct_col (M : Matrix (Fin n) (Fin n) R) :
    M.det ^ 2 ≤ ∏ i, (Mᵀ i ⬝ᵥ Mᵀ i) := by
  -- Each column has nonnegative squared norm.
  have hcol_nonneg : ∀ i, 0 ≤ Mᵀ i ⬝ᵥ Mᵀ i := fun i => by
    rw [dotProduct]; exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
  by_cases hLI : LinearIndependent R (fun i => Mᵀ i)
  · rcases isEmpty_or_nonempty (Fin n) with hE | hNE
    · -- Empty matrix: det = 1, empty product = 1.
      have := hE
      simp [Matrix.det_isEmpty]
    · -- Gram–Schmidt on the (independent) columns.
      obtain ⟨w, hw_li, hw_orth, hw_spanv, hw_spanw⟩ := Chapter4.proposition_4_41 _ hLI
      have hw_nonneg : ∀ i, 0 ≤ w i ⬝ᵥ w i := fun i => by
        rw [dotProduct]; exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
      -- The columns form a basis of `Fin n → R`.
      have hcard : Fintype.card (Fin n) = Module.finrank R (Fin n → R) := by
        simp
      let b : Basis (Fin n) R (Fin n → R) :=
        basisOfLinearIndependentOfCardEqFinrank hLI hcard
      have hb : ⇑b = fun i => Mᵀ i := coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard
      -- Change-of-basis matrix `C` and the matrix `W` of orthogonalized columns.
      set C : Matrix (Fin n) (Fin n) R := Matrix.of (fun i j => b.repr (w i) j) with hC
      set W : Matrix (Fin n) (Fin n) R := Matrix.of (fun k i => w i k) with hW
      -- `b.repr (w i)` splits along `w i = (w i - vᵢ) + vᵢ`.
      have hrepr : ∀ i j, b.repr (w i) j
          = b.repr (w i - Mᵀ i) j + b.repr (Mᵀ i) j := by
        intro i j
        have hwi : w i - Mᵀ i + Mᵀ i = w i := by abel
        rw [← Finsupp.add_apply, ← map_add, hwi]
      -- `wᵢ − vᵢ` has `b`-coordinates supported strictly below `i`.
      have hzero_above : ∀ i j : Fin n, ¬ (j < i) → b.repr (w i - Mᵀ i) j = 0 := by
        intro i j hj
        by_contra h
        have hmem : j ∈ (b.repr (w i - Mᵀ i)).support := Finsupp.mem_support_iff.mpr h
        have hsub := Module.Basis.repr_support_subset_of_mem_span b {k | k < i}
          (by rw [hb]; exact hw_spanv i)
        exact hj (hsub (Finset.mem_coe.mpr hmem))
      -- `C` is lower triangular with unit diagonal, hence `det C = 1`.
      have hbi : ∀ i, b i = Mᵀ i := fun i => congrFun hb i
      have hCdiag : ∀ i, C i i = 1 := by
        intro i
        simp only [hC, Matrix.of_apply]
        rw [hrepr i i, hzero_above i i (lt_irrefl i), zero_add, ← hbi i,
          Basis.repr_self, Finsupp.single_eq_same]
      have hCtri : C.BlockTriangular (⇑OrderDual.toDual) := by
        intro i j hij
        rw [OrderDual.toDual_lt_toDual] at hij
        simp only [hC, Matrix.of_apply]
        rw [hrepr i j, hzero_above i j (not_lt.mpr hij.le), zero_add, ← hbi i,
          Basis.repr_self, Finsupp.single_apply, ite_eq_right (ne_of_lt hij)]
      have hdetC : C.det = 1 := by
        rw [Matrix.det_of_isLowerTriangular C hCtri]
        exact Finset.prod_eq_one (fun i _ => hCdiag i)
      -- `W = M * Cᵀ`, hence `det W = det M`.
      have hWMC : W = M * Cᵀ := by
        ext k i
        simp only [hW, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hC]
        have hsum := congrFun (b.sum_repr (w i)) k
        rw [Finset.sum_apply] at hsum
        simp only [Pi.smul_apply, smul_eq_mul] at hsum
        rw [← hsum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hbjk : b j k = M k j := by rw [hbi j]; rfl
        rw [hbjk]; ring
      have hdetW : W.det = M.det := by
        rw [hWMC, Matrix.det_mul, Matrix.det_transpose, hdetC, mul_one]
      -- `WᵀW = diag(‖wᵢ‖²)`, hence `det(W)² = ∏ᵢ ‖wᵢ‖²`.
      have hWtW : Wᵀ * W = Matrix.diagonal (fun i => w i ⬝ᵥ w i) := by
        ext i j
        rw [Matrix.mul_apply]
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq, dotProduct]
          exact Finset.sum_congr rfl (fun k _ => by simp [hW, Matrix.transpose_apply])
        · rw [Matrix.diagonal_apply_ne _ hij]
          have horth : w i ⬝ᵥ w j = 0 := hw_orth i j hij
          rw [dotProduct] at horth
          rw [← horth]
          exact Finset.sum_congr rfl (fun k _ => by simp [hW, Matrix.transpose_apply])
      have hdetWsq : W.det ^ 2 = ∏ i, (w i ⬝ᵥ w i) := by
        have hdd : (Wᵀ * W).det = ∏ i, (w i ⬝ᵥ w i) := by
          rw [hWtW, Matrix.det_diagonal]
        rw [Matrix.det_mul, Matrix.det_transpose] at hdd
        rw [← hdd]; ring
      -- Pythagoras: `‖wᵢ‖² ≤ ‖vᵢ‖²`.
      have hpyth : ∀ i, w i ⬝ᵥ w i ≤ Mᵀ i ⬝ᵥ Mᵀ i := by
        intro i
        obtain ⟨u, hu⟩ : ∃ u, u = w i - Mᵀ i := ⟨_, rfl⟩
        have hwu : w i ⬝ᵥ u = 0 := by
          have hmem : u ∈ Submodule.span R (w '' {j | j < i}) := by rw [hu]; exact hw_spanw i
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
          · rintro x ⟨j, hj, rfl⟩
            exact hw_orth i j (Ne.symm (ne_of_lt hj))
          · simp [dotProduct]
          · intro x y _ _ hx hy; rw [dotProduct_add, hx, hy, add_zero]
          · intro a x _ hx; rw [dotProduct_smul, hx, smul_zero]
        have huu : 0 ≤ u ⬝ᵥ u := by
          rw [dotProduct]; exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
        have hsplit : Mᵀ i = w i - u := by rw [hu]; abel
        have key : Mᵀ i ⬝ᵥ Mᵀ i = w i ⬝ᵥ w i - 2 * (w i ⬝ᵥ u) + u ⬝ᵥ u := by
          rw [hsplit, sub_dotProduct, dotProduct_sub, dotProduct_sub,
            dotProduct_comm u (w i)]; ring
        rw [key, hwu]; linarith [huu]
      calc M.det ^ 2 = W.det ^ 2 := by rw [hdetW]
        _ = ∏ i, (w i ⬝ᵥ w i) := hdetWsq
        _ ≤ ∏ i, (Mᵀ i ⬝ᵥ Mᵀ i) :=
            Finset.prod_le_prod₀ (fun i _ => hw_nonneg i) (fun i _ => hpyth i)
  · -- Dependent columns: `det M = 0`.
    have hdet0 : M.det = 0 := by
      rw [Fintype.not_linearIndependent_iff] at hLI
      obtain ⟨g, hgsum, k, hgk⟩ := hLI
      apply Matrix.exists_mulVec_eq_zero_iff.mp
      refine ⟨g, fun hg0 => hgk (congrFun hg0 k), ?_⟩
      funext j
      have hj := congrFun hgsum j
      rw [Finset.sum_apply] at hj
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Pi.zero_apply] at hj
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← hj]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hdet0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact Finset.prod_nonneg (fun i _ => hcol_nonneg i)

/-- **Hadamard's inequality (BPR Proposition 8.12), euclidean-norm form over a real
closed field.** `|det(M)| ≤ ∏ᵢ ‖cᵢ‖`, where `cᵢ = Mᵀ i` is the `i`-th column and
`‖·‖` is the §3.1 euclidean norm. -/
theorem abs_det_le_prod_euclideanNorm_col [IsRealClosed R]
    (M : Matrix (Fin n) (Fin n) R) :
    |M.det| ≤ ∏ i, euclideanNorm (Mᵀ i) := by
  have hcore := det_sq_le_prod_dotProduct_col M
  have hnorm : ∀ i, Mᵀ i ⬝ᵥ Mᵀ i = euclideanNorm (Mᵀ i) ^ 2 := by
    intro i
    rw [euclideanNorm_sq, euclideanNormSq, dotProduct]
    exact Finset.sum_congr rfl (fun k _ => (sq (Mᵀ i k)).symm)
  have hprod : (∏ i, (Mᵀ i ⬝ᵥ Mᵀ i)) = (∏ i, euclideanNorm (Mᵀ i)) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ => hnorm i)
  rw [hprod] at hcore
  have hP_nonneg : 0 ≤ ∏ i, euclideanNorm (Mᵀ i) :=
    Finset.prod_nonneg (fun i _ => euclideanNorm_nonneg _)
  by_contra h
  rw [not_le] at h
  nlinarith [hcore, sq_abs M.det, abs_nonneg M.det, hP_nonneg, h]

/-- **BPR Proposition 8.12 (Hadamard's inequality).** For an `n × n` integer matrix
`M`, `|det(M)|` is bounded by the product of the euclidean norms of its columns. -/
theorem proposition_8_12 (M : Matrix (Fin n) (Fin n) ℤ) :
    |(M.det : ℝ)| ≤ ∏ i, euclideanNorm (fun k => (M k i : ℝ)) := by
  have h := abs_det_le_prod_euclideanNorm_col (M.map (Int.cast : ℤ → ℝ))
  have hdet : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
    have hm := RingHom.map_det (Int.castRingHom ℝ) M
    simpa [RingHom.mapMatrix_apply] using hm.symm
  have hcol : ∀ i, (M.map (Int.cast : ℤ → ℝ))ᵀ i = fun k => (M k i : ℝ) := by
    intro i; funext k; rw [Matrix.transpose_apply, Matrix.map_apply]
  rw [hdet] at h
  simp only [hcol] at h
  exact h

end Azurite.BPR
