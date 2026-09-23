import Azurite.BasuPollackRoy.Chapter8.Section8_3.Lemma_8_29
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# BPR Lemma 8.31: triangular reduction of the polynomial determinant

Let `𝒫 = P_1, …, P_ℓ, P_{ℓ+1}, …, P_m` with `deg P_i = n - i` for `i ≤ ℓ` and
`deg P_i ≤ n - 1 - ℓ` for `ℓ < i ≤ m`. Writing `p_{i,n-i}` for the leading
coefficient of `P_i` (`i ≤ ℓ`), one has

`pdet_{m,n}(𝒫) = (∏_{i=1}^ℓ p_{i,n-i}) · pdet_{m-ℓ,n-ℓ}(𝒬)`,  `𝒬 = P_{ℓ+1}, …, P_m`.

Proof (BPR): developing `det(Mat(𝒫)*)` (Lemma 8.29) by its first `ℓ` columns. In
matrix terms, `Mat(𝒫)*` is block triangular — the bottom-left `(m-ℓ) × ℓ` block
vanishes because `deg P_i ≤ n-1-ℓ` for `i > ℓ` — so its determinant is the product
of the determinants of the upper-triangular `ℓ × ℓ` leading block (whose diagonal
holds the leading coefficients) and of the bottom-right block, which is `Mat(𝒬)*`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

variable {D : Type*} [CommRing D]

private theorem sub_sub_add_aux (n ℓ j : ℕ) : n - 1 - (ℓ + j) = n - ℓ - 1 - j := by omega

/-- **BPR Lemma 8.31.** Triangular reduction of `pdet`. -/
theorem pdetRing_triangular {m n ℓ : ℕ} (hℓm : ℓ < m) (hmn : m ≤ n) (P : Fin m → D[X])
    (hdeg1 : ∀ r : Fin m, (r : ℕ) < ℓ → ∀ j, n - 1 - (r : ℕ) < j → (P r).coeff j = 0)
    (hdeg2 : ∀ r : Fin m, ℓ ≤ (r : ℕ) → ∀ j, n - 1 - ℓ < j → (P r).coeff j = 0) :
    pdetRing n P
      = C (∏ i : Fin ℓ, (P ⟨(i : ℕ), by omega⟩).coeff (n - 1 - (i : ℕ)))
        * pdetRing (n - ℓ) (fun r' : Fin (m - ℓ) => P ⟨ℓ + (r' : ℕ), by omega⟩) := by
  have hℓn : ℓ < n := by omega
  -- every `P r` has degree `< n`
  have hmemP : ∀ r : Fin m, P r ∈ degreeLT D n := by
    intro r
    rw [mem_degreeLT]
    by_cases hr : (r : ℕ) < ℓ
    · refine lt_of_le_of_lt ((degree_le_iff_coeff_zero (P r) (↑(n - 1 - (r : ℕ)))).2
        (fun j hj => hdeg1 r hr j (by exact_mod_cast hj))) ?_
      exact_mod_cast (show n - 1 - (r : ℕ) < n by omega)
    · refine lt_of_le_of_lt ((degree_le_iff_coeff_zero (P r) (↑(n - 1 - ℓ))).2
        (fun j hj => hdeg2 r (not_lt.mp hr) j (by exact_mod_cast hj))) ?_
      exact_mod_cast (show n - 1 - ℓ < n by omega)
  set Q : Fin (m - ℓ) → D[X] := fun r' => P ⟨ℓ + (r' : ℕ), by omega⟩ with hQ
  have hmemQ : ∀ r' : Fin (m - ℓ), Q r' ∈ degreeLT D (n - ℓ) := by
    intro r'
    rw [mem_degreeLT]
    refine lt_of_le_of_lt ((degree_le_iff_coeff_zero (Q r') (↑(n - 1 - ℓ))).2
      (fun j hj => hdeg2 ⟨ℓ + (r' : ℕ), by omega⟩ (by simp) j (by exact_mod_cast hj))) ?_
    exact_mod_cast (show n - 1 - ℓ < n - ℓ by omega)
  -- `pdet = det(matStar)` for `𝒫` and `𝒬`
  have hP : pdetRing n P = (matStar n P).det :=
    pdetRing_eq_det_matStar (by omega) hmn (fun r => ⟨P r, hmemP r⟩)
  have hQeq : pdetRing (n - ℓ) Q = (matStar (n - ℓ) Q).det :=
    pdetRing_eq_det_matStar (by omega) (by omega) (fun r' => ⟨Q r', hmemQ r'⟩)
  -- reindexing equiv `Fin ℓ ⊕ Fin (m-ℓ) ≃ Fin m`
  set e' : Fin ℓ ⊕ Fin (m - ℓ) ≃ Fin m :=
    finSumFinEquiv.trans (finCongr (by omega)) with he'
  have he_l : ∀ i : Fin ℓ, (e' (Sum.inl i) : ℕ) = (i : ℕ) := by
    intro i; simp [he', Equiv.trans_apply, finSumFinEquiv_apply_left]
  have he_r : ∀ i : Fin (m - ℓ), (e' (Sum.inr i) : ℕ) = ℓ + (i : ℕ) := by
    intro i; simp [he', Equiv.trans_apply, finSumFinEquiv_apply_right]
  have he_lf : ∀ i : Fin ℓ, e' (Sum.inl i) = ⟨(i : ℕ), by omega⟩ := fun i => Fin.ext (he_l i)
  have he_rf : ∀ i : Fin (m - ℓ), e' (Sum.inr i) = ⟨ℓ + (i : ℕ), by omega⟩ :=
    fun i => Fin.ext (he_r i)
  set Mb := (matStar n P).submatrix e' e' with hMb
  -- bottom-left block is zero
  have htb21 : Mb.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hMb, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.of_apply, Matrix.zero_apply,
      matStar]
    rw [he_l j, ite_eq_left (by have := j.isLt; omega)]
    rw [show (P (e' (Sum.inr i))).coeff (n - 1 - (j : ℕ)) = 0 from
      hdeg2 _ (by rw [he_r i]; omega) _ (by have := j.isLt; omega), map_zero]
  -- bottom-right block is `matStar (n-ℓ) Q`
  have htb22 : Mb.toBlocks₂₂ = matStar (n - ℓ) Q := by
    ext i j
    simp only [hMb, Matrix.toBlocks₂₂, Matrix.submatrix_apply, Matrix.of_apply, matStar]
    rw [he_rf i, he_r j, hQ]
    by_cases hc : (j : ℕ) + 1 < m - ℓ
    · rw [ite_eq_left (by omega), ite_eq_left hc, sub_sub_add_aux n ℓ (j : ℕ)]
    · rw [ite_eq_right (by omega), ite_eq_right hc]
  -- leading `ℓ × ℓ` block is upper triangular with leading coefficients on the diagonal
  have htri : Matrix.BlockTriangular Mb.toBlocks₁₁ id := by
    intro i j hji
    simp only [hMb, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply, matStar]
    have hji' : (j : ℕ) < (i : ℕ) := hji
    rw [he_l j, ite_eq_left (by have := j.isLt; omega)]
    rw [show (P (e' (Sum.inl i))).coeff (n - 1 - (j : ℕ)) = 0 from
      hdeg1 _ (by rw [he_l i]; exact i.isLt) _ (by rw [he_l i]; omega), map_zero]
  have hdiag : ∀ i : Fin ℓ,
      Mb.toBlocks₁₁ i i = C ((P ⟨(i : ℕ), by omega⟩).coeff (n - 1 - (i : ℕ))) := by
    intro i
    simp only [hMb, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply, matStar]
    rw [he_l i, ite_eq_left (by have := i.isLt; omega), he_lf i]
  calc pdetRing n P = Mb.det := by rw [hP, hMb, det_submatrix_equiv_self]
    _ = Mb.toBlocks₁₁.det * Mb.toBlocks₂₂.det := by
        conv_lhs => rw [← Matrix.fromBlocks_toBlocks Mb]
        rw [htb21, Matrix.det_fromBlocks_zero₂₁]
    _ = C (∏ i : Fin ℓ, (P ⟨(i : ℕ), by omega⟩).coeff (n - 1 - (i : ℕ)))
          * pdetRing (n - ℓ) Q := by
        rw [htb22, Matrix.det_of_isUpperTriangular htri,
          Finset.prod_congr rfl (fun i _ => hdiag i), ← map_prod, ← hQeq]

end Azurite.BPR.Chapter8
