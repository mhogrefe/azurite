import Azurite.BasuPollackRoy.Chapter8.Section8_3.PolynomialDeterminantRing

/-!
# BPR Lemma 8.29: the polynomial determinant as a classical determinant

For `𝒫 = P_1, …, P_m` (with `P_i ∈ 𝓕_n`), let `Mat(𝒫)*` be the `m × m` matrix
whose first `m-1` columns are the first `m-1` columns of `Mat(𝒫)` and whose last
column holds the polynomials `P_1, …, P_m`. Then

`pdet_{m,n}(𝒫) = det(Mat(𝒫)*)`.

Proof: `det(Mat(𝒫)*)` is linear in its last column; expanding `P_r` over the
monomial basis gives `Σ_i m_i X^i`, and for `i > n-m` the minor `m_i` has two
equal columns (or, for `i ≥ n`, a zero column since `deg P_r < n`), so vanishes.
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

variable {m n : ℕ} {D : Type*} [CommRing D]

/-- `Mat(𝒫)*`: the first `m-1` columns are the (constant) entries of `Mat(𝒫)`,
    the last column holds the polynomials `P_r`. -/
noncomputable def matStar (n : ℕ) (P : Fin m → D[X]) : Matrix (Fin m) (Fin m) D[X] :=
  fun r c => if (c : ℕ) + 1 < m then C ((P r).coeff (n - 1 - (c : ℕ))) else P r

/-- The determinant is linear in a fixed column over a finite sum of columns. -/
theorem det_updateCol_finsetSum {ι : Type*} (M : Matrix (Fin m) (Fin m) D[X]) (j : Fin m)
    (s : Finset ι) (f : ι → (Fin m → D[X])) :
    (M.updateCol j (∑ k ∈ s, f k)).det = ∑ k ∈ s, (M.updateCol j (f k)).det := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [← zero_smul (D[X]) (0 : Fin m → D[X]), Matrix.det_updateCol_smul, zero_mul]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Matrix.det_updateCol_add, ih, Finset.sum_insert ha]

private theorem matStar_aux_bound {m n k : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hkn : k < n)
    (hks : n - m + 1 ≤ k) :
    n - 1 - k < m ∧ n - 1 - k + 1 < m ∧ n - 1 - (n - 1 - k) = k ∧ n - 1 - k ≠ m - 1 :=
  ⟨by omega, by omega, by omega, by omega⟩

/-- **BPR Lemma 8.29.** `pdet_{m,n}(𝒫) = det(Mat(𝒫)*)`. -/
theorem pdetRing_eq_det_matStar (hm : 0 < m) (hmn : m ≤ n) (P : Fin m → degreeLT D n) :
    pdetRing n (fun r => (P r : D[X])) = (matStar n (fun r => (P r : D[X]))).det := by
  set Q : Fin m → D[X] := fun r => (P r : D[X]) with hQ
  set last : Fin m := ⟨m - 1, by omega⟩ with hlast
  have hlastval : (last : ℕ) = m - 1 := rfl
  have hnd : ∀ r, (Q r).natDegree < n := by
    intro r
    have h2 := (P r).2; rw [mem_degreeLT] at h2
    rcases eq_or_ne (Q r) 0 with hz | hz
    · rw [hz, natDegree_zero]; omega
    · exact (natDegree_lt_iff_degree_lt hz).mpr h2
  set colVec : ℕ → (Fin m → D[X]) := fun k r => C ((Q r).coeff k) with hcolVec
  -- The last column of `matStar` expands as `Σ_{k<n} X^k • colVec k`.
  have hQexp : (fun r => Q r) = ∑ k ∈ Finset.range n, (X : D[X]) ^ k • colVec k := by
    funext r
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, hcolVec, smul_eq_mul]
    symm
    conv_rhs => rw [as_sum_range' (Q r) n (hnd r)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← C_mul_X_pow_eq_monomial, mul_comm]
  -- `matStar` equals the column-updated form, ready for the sum expansion.
  have hms : matStar n Q = (matStar n Q).updateCol last (∑ k ∈ Finset.range n, (X : D[X]) ^ k • colVec k) := by
    rw [← hQexp]
    ext r c
    rw [Matrix.updateCol_apply]
    by_cases hc : c = last
    · subst hc
      rw [if_pos rfl, matStar, if_neg (by rw [hlastval]; omega)]
    · rw [if_neg hc]
  -- The `k`-th term is `X^k * C(m_k)`.
  have hterm : ∀ k, ((matStar n Q).updateCol last ((X : D[X]) ^ k • colVec k)).det
      = (X : D[X]) ^ k * C (pdetMinorRing n Q k) := by
    intro k
    rw [Matrix.det_updateCol_smul]
    congr 1
    have hmat : (matStar n Q).updateCol last (colVec k) = (pdetMinorMatRing n Q k).map C := by
      ext r c
      rw [Matrix.updateCol_apply, Matrix.map_apply, pdetMinorMatRing, pdetColIdx]
      by_cases hc : c = last
      · subst hc
        rw [if_pos rfl, hcolVec, if_neg (by rw [hlastval]; omega)]
      · rw [if_neg hc, matStar, if_pos (by
          have := c.isLt
          rw [Fin.ext_iff, hlastval] at hc; omega)]
        congr 2
        rw [if_pos (by have := c.isLt; rw [Fin.ext_iff, hlastval] at hc; omega)]
    rw [hmat, pdetMinorRing, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [hms, det_updateCol_finsetSum]
  simp only [hterm]
  -- `Σ_{k<n} X^k * C(m_k) = Σ_{k<n} m_k • X^k`, then restrict to `k ≤ n-m`.
  have hsmul : ∀ k, X ^ k * C (pdetMinorRing n Q k) = pdetMinorRing n Q k • X ^ k := by
    intro k; rw [mul_comm, smul_eq_C_mul]
  simp only [hsmul]
  rw [pdetRing, Fin.sum_univ_eq_sum_range (fun i => pdetMinorRing n Q i • X ^ i)]
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_range] at hk ⊢; omega
  · intro k hkn hks
    rw [Finset.mem_range] at hkn
    rw [Finset.mem_range, not_lt] at hks
    -- pdetMinorRing n Q k = 0 for n-m < k < n: columns `n-1-k` and `m-1` coincide.
    obtain ⟨hkm, hk1, hk2, hk3⟩ := matStar_aux_bound hm hmn hkn hks
    have hz : pdetMinorRing n Q k = 0 := by
      rw [pdetMinorRing]
      apply Matrix.det_zero_of_column_eq (i := (⟨n - 1 - k, hkm⟩ : Fin m)) (j := last)
        (Fin.ne_of_val_ne (by simp only [hlastval]; exact hk3))
      intro r
      simp only [pdetMinorMatRing, pdetColIdx, hlastval]
      rw [if_pos hk1, if_neg (show ¬ (m - 1 + 1 < m) by omega), hk2]
    rw [hz, zero_smul]

/-- **BPR Remark 8.30.** Expanding `det(Mat(𝒫)*)` along its last column shows that
    `pdet_{m,n}(𝒫)` is a `D`-linear combination of the `P_i`: the coefficients are
    (up to sign) the `(m-1) × (m-1)` minors extracted on the first `m-1` columns of
    `Mat(𝒫)`. Concretely, `pdet_{m,n}(𝒫) = Σ_i C(c_i) · P_i` with `c_i ∈ D`. -/
theorem pdetRing_eq_linear_combination (hm : 0 < m) (hmn : m ≤ n) (P : Fin m → degreeLT D n) :
    ∃ c : Fin m → D, pdetRing n (fun r => (P r : D[X]))
      = ∑ i, C (c i) * (P i : D[X]) := by
  set Q : Fin m → D[X] := fun r => (P r : D[X]) with hQ
  set last : Fin m := ⟨m - 1, by omega⟩ with hlast
  have hlastval : (last : ℕ) = m - 1 := rfl
  -- The `D`-valued cofactor matrices: first `m-1` columns of `Mat(𝒫)`, last column `e_{r₀}`.
  set N : Fin m → Matrix (Fin m) (Fin m) D :=
    fun r₀ r c => if (c : ℕ) + 1 < m then (Q r).coeff (n - 1 - (c : ℕ)) else if r = r₀ then 1 else 0
    with hN
  refine ⟨fun r₀ => (N r₀).det, ?_⟩
  rw [pdetRing_eq_det_matStar hm hmn P]
  -- decompose the last column over the standard basis
  have hcol : (fun r => Q r) = ∑ r₀ : Fin m, Q r₀ • Pi.single r₀ (1 : D[X]) := by
    funext r
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, Finset.sum_ite_eq]
  have hms : matStar n Q
      = (matStar n Q).updateCol last (∑ r₀ : Fin m, Q r₀ • Pi.single r₀ (1 : D[X])) := by
    rw [← hcol]
    ext r c
    rw [Matrix.updateCol_apply]
    by_cases hc : c = last
    · subst hc
      rw [if_pos rfl, matStar, if_neg (show ¬ ((last : ℕ) + 1 < m) by rw [hlastval]; omega)]
    · rw [if_neg hc]
  rw [hms, det_updateCol_finsetSum]
  refine Finset.sum_congr rfl (fun r₀ _ => ?_)
  rw [Matrix.det_updateCol_smul]
  have hmat : (matStar n Q).updateCol last (Pi.single r₀ (1 : D[X])) = (N r₀).map C := by
    ext r c
    rw [Matrix.updateCol_apply, Matrix.map_apply]
    by_cases hc : c = last
    · subst hc
      rw [if_pos rfl]
      simp only [hN]
      rw [if_neg (show ¬ ((last : ℕ) + 1 < m) by rw [hlastval]; omega),
        Pi.single_apply, apply_ite C, map_one, map_zero]
    · rw [if_neg hc]
      have hcm : (c : ℕ) + 1 < m := by
        have h1 := c.isLt
        have h2 : (c : ℕ) ≠ m - 1 := by rw [← hlastval]; exact Fin.val_ne_of_ne hc
        omega
      simp only [matStar, hN]
      rw [if_pos hcm, if_pos hcm]
  rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, mul_comm]

end Azurite.BPR.Chapter8
