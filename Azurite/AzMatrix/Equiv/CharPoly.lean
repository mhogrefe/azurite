import Azurite.AzMatrix.CharPoly
import Azurite.AzMatrix.Equiv.Pow
import Azurite.AzPolynomial.Equiv.NewtonSum
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Ring.GeomSum

/-!
# Correctness of `AzMatrix.charPoly`

The mathematical crux (`Module.End.trace_pow_eq_sum_roots_pow`) is that, over an
algebraically closed field, `trace(fᵏ)` equals the sum of the `k`-th powers of the
eigenvalues counted with multiplicity (the roots of the characteristic
polynomial), proved via the generalized-eigenspace decomposition.
-/

open LinearMap Set Polynomial Module Module.End

/-- In a ring, if `a - b` is nilpotent and `a, b` commute, then `aᵏ - bᵏ` is
nilpotent. -/
private theorem isNilpotent_pow_sub_pow {R : Type*} [Ring R] {a b : R}
    (hab : Commute a b) (h : IsNilpotent (a - b)) (k : ℕ) :
    IsNilpotent (a ^ k - b ^ k) := by
  rw [← hab.geom_sum₂_mul k]
  refine Commute.isNilpotent_mul_left ?_ h
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact Commute.sub_right
    (Commute.mul_left ((Commute.refl a).pow_left i) (hab.symm.pow_left _))
    (Commute.mul_left (hab.pow_left i) ((Commute.refl b).pow_left _))

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [IsAlgClosed K]

omit [IsAlgClosed K] in
/-- The trace of `fᵏ` restricted to the generalized `μ`-eigenspace is
`μᵏ · dim(genEigenspace μ)`. -/
private theorem trace_restrict_pow_maxGenEigenspace (f : End K V) (μ : K) (k : ℕ)
    (h : MapsTo (f ^ k) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ)) :
    LinearMap.trace K _ ((f ^ k).restrict h)
      = μ ^ k * (Module.finrank K (f.maxGenEigenspace μ) : K) := by
  set W := f.maxGenEigenspace μ with hW
  have hf : MapsTo f W W := mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  set g : End K W := f.restrict hf with hg
  -- `(fᵏ).restrict h = gᵏ`.
  have hgk : (f ^ k).restrict h = g ^ k := (Module.End.pow_restrict k hf).symm
  -- `g - μ` is nilpotent on `W`.
  have hnil1 : IsNilpotent (g - algebraMap K (End K W) μ) := by
    have heq : g - algebraMap K (End K W) μ
        = (f - algebraMap K (End K V) μ).restrict
            (mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) := by
      refine LinearMap.ext fun x => Subtype.ext ?_
      simp only [hg, LinearMap.sub_apply, AddSubgroupClass.coe_sub,
        Module.algebraMap_end_apply, SetLike.val_smul]
      rfl
    rw [heq]
    exact isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ
  have hnil : IsNilpotent (g ^ k - algebraMap K (End K W) (μ ^ k)) := by
    rw [map_pow]
    exact isNilpotent_pow_sub_pow (Algebra.commute_algebraMap_right μ g) hnil1 k
  rw [hgk]
  have ht := trace_comp_eq_mul_of_commute_of_isNilpotent (μ ^ k) (Commute.one_left (g ^ k)) hnil
  rw [← Module.End.mul_eq_comp, one_mul] at ht
  rw [ht, LinearMap.trace_one]

/-- **Crux (trace of powers = power sums of eigenvalues).** Over an algebraically
closed field, the trace of `fᵏ` is the sum of the `k`-th powers of the roots of
the characteristic polynomial (the eigenvalues counted with multiplicity). -/
theorem trace_pow_eq_sum_roots_pow (f : End K V) (k : ℕ) :
    LinearMap.trace K V (f ^ k) = (f.charpoly.roots.map (· ^ k)).sum := by
  classical
  have hInternal : DirectSum.IsInternal (f.maxGenEigenspace) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (f.independent_genEigenspace ⊤) (f.iSup_maxGenEigenspace_eq_top)
  have hmaps : ∀ μ, MapsTo (f ^ k) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) := fun μ =>
    mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right k) μ
  -- The support `{μ | maxGenEigenspace μ ≠ ⊥}` equals the (finite) set of roots.
  have hbot : ∀ μ : K, f.maxGenEigenspace μ ≠ ⊥ ↔ μ ∈ f.charpoly.roots.toFinset := by
    intro μ
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots,
      ← finrank_maxGenEigenspace_eq, Nat.pos_iff_ne_zero, ne_eq, ne_eq,
      not_iff_not, Submodule.finrank_eq_zero]
  have hfin : {μ : K | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    Set.Finite.subset f.charpoly.roots.toFinset.finite_toSet (fun μ hμ => (hbot μ).mp hμ)
  rw [LinearMap.trace_eq_sum_trace_restrict' hInternal hfin hmaps]
  simp_rw [trace_restrict_pow_maxGenEigenspace f _ k]
  rw [Finset.sum_multiset_map_count]
  have hset : hfin.toFinset = f.charpoly.roots.toFinset := by
    ext μ; rw [Set.Finite.mem_toFinset, mem_setOf_eq, hbot μ]
  rw [hset]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [finrank_maxGenEigenspace_eq, Polynomial.count_roots, nsmul_eq_mul]
  ring

end Module.End

/-! ## Matrix form of the crux -/

namespace Matrix

theorem trace_pow_eq_sum_roots_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] [IsAlgClosed K] (B : Matrix ι ι K) (k : ℕ) :
    (B ^ k).trace = (B.charpoly.roots.map (· ^ k)).sum := by
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow,
    Module.End.trace_pow_eq_sum_roots_pow, Matrix.charpoly_toLin']

end Matrix

/-! ## Correctness of `AzMatrix.charPoly` -/

namespace Azurite.AzMatrix

open Polynomial _root_.AzPolynomial Azurite.AzPolynomial Azurite.BPR.Chapter4

variable {A : Type*} [Field A] {n : ℕ}

/-- `traceMul X Y = Tr(toMat X · toMat Y)` (the Mathlib trace of the product). -/
theorem traceMul_eq_trace (X Y : AzMatrix A n n) :
    traceMul X Y = Matrix.trace (toMat X * toMat Y) := by
  simp only [traceMul, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rfl

/-- **Correctness of BPR Algorithm 8.17.** The computed characteristic polynomial
agrees with Mathlib's `Matrix.charpoly` of the underlying matrix. -/
theorem toPoly_charPoly [CharZero A] (M : AzMatrix A n n) :
    toPoly M.charPoly = (toMat M).charpoly := by
  classical
  set C := AlgebraicClosure A
  set r := n.sqrt + 1 with hr_def
  have hr : 0 < r := Nat.succ_pos _
  set P : Azurite.AzPolynomial A := ofPoly (toMat M).charpoly with hP
  have hPtoPoly : toPoly P = (toMat M).charpoly := by rw [hP, toPoly_ofPoly]
  have hPmonic : P.Monic := (Monic_toPoly P).mp (hPtoPoly ▸ (toMat M).charpoly_monic)
  have hPdeg : P.natDegree = n := by
    rw [hP, natDegree_ofPoly, (toMat M).charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- For `k ≤ n`, the `k`-th computed Newton sum is `P.newtonSumMonic k`.
  have hstep : ∀ k, k < n + 1 →
      traceMul ((Array.ofFn (n := r) (fun i : Fin r => M ^ (i : ℕ))).getD (k % r) 1)
        ((Array.ofFn (n := r) (fun j : Fin r => M ^ (r * (j : ℕ)))).getD (k / r) 1)
        = P.newtonSumMonic k := by
    intro k hk
    have hkr : k % r < r := Nat.mod_lt _ hr
    have hkdr : k / r < r := by
      have h1 : n < r * r := Nat.lt_succ_sqrt n
      have h2 : k / r ≤ n / r := Nat.div_le_div_right (by omega)
      have h3 : n / r < r := (Nat.div_lt_iff_lt_mul hr).mpr h1
      omega
    -- evaluate the baby/giant steps
    have hb : (Array.ofFn (n := r) (fun i : Fin r => M ^ (i : ℕ))).getD (k % r) 1 = M ^ (k % r) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]; simp [hkr]
    have hgi : (Array.ofFn (n := r) (fun j : Fin r => M ^ (r * (j : ℕ)))).getD (k / r) 1
        = M ^ (r * (k / r)) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]; simp [hkdr]
    rw [hb, hgi, traceMul_eq_trace, toMat_npow, toMat_npow, ← pow_add, Nat.mod_add_div]
    -- now: Tr(toMat M ^ k) = P.newtonSumMonic k, via algebraMap injectivity
    apply (algebraMap A C).injective
    rw [newtonSumMonic_toPoly P hPmonic k, hPtoPoly]
    -- algebraMap A C (Tr(toMat M ^ k)) = newtonSum (toMat M).charpoly k
    rw [AddMonoidHom.map_trace, Matrix.map_pow, Matrix.trace_pow_eq_sum_roots_pow,
      Matrix.charpoly_map, newtonSum, Polynomial.aroots]
  -- assemble
  have hcp : M.charPoly = P := by
    have hunfold : M.charPoly
        = polyFromNewtonSumsMonic ((Array.range (n + 1)).map
            (fun k => traceMul ((Array.ofFn (n := r) (fun i : Fin r => M ^ (i : ℕ))).getD (k % r) 1)
              ((Array.ofFn (n := r) (fun j : Fin r => M ^ (r * (j : ℕ)))).getD (k / r) 1))) := rfl
    rw [hunfold, ← polyFromNewtonSumsMonic_newtonSumsMonic P hPmonic]
    congr 1
    rw [newtonSumsMonic, hPdeg]
    apply Array.ext
    · simp
    · intro k hk1 _
      simp only [Array.getElem_map, Array.getElem_range]
      exact hstep k (by simpa using hk1)
  rw [hcp]; exact hPtoPoly
