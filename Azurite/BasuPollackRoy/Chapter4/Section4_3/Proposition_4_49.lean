import Azurite.BasuPollackRoy.Chapter4.Section4_3.Theorem_4_48
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# BPR Proposition 4.49: the sign pattern of subdiscriminants

Given a symmetric matrix `M` of size `p`, there is a threshold `k` (`0 ≤ k ≤ p-1`) such
that the subdiscriminants of its characteristic polynomial satisfy
`sDisc_i(M) > 0` for `k ≤ i ≤ p-1` and `sDisc_i(M) = 0` for `0 ≤ i < k`.

The proof: by Theorem 4.48 each `sDisc_i(M)` is a sum of squares, so `sDisc_i(M) ≥ 0`,
and `sDisc_i(M) = det(A_i A_iᵀ) = 0` iff the rows of `A_i` (the powers
`M^0, …, M^{p-i-1}` in coordinates) are linearly dependent (Gram determinant criterion
over an ordered field). The rows of `A_{i+1}` are a subfamily of those of `A_i`, so
`sDisc_{i+1}(M) = 0 ⟹ sDisc_i(M) = 0`: the zero locus is a downward-closed initial
segment `[0, k)`. Since `sDisc_{p-1}(M) = \mathrm{Tr}(M^0) = p > 0`, the threshold `k`
lies in `[0, p-1]`.
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open Matrix

section

variable {p : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- `sDisc_k(M)` as a Gram determinant of the reindexed matrix `AkFin k M`. -/
private lemma sDisc_eq_gram (k : ℕ) (M : Matrix (Fin p) (Fin p) R) (hM : M.IsSymm) :
    sDiscOfMatrix k M = (AkFin k M * (AkFin k M)ᵀ).det := by
  classical
  have hAk : Ak k M * (Ak k M)ᵀ = AkFin k M * (AkFin k M)ᵀ := by
    set e := Fintype.equivFin (STri p)
    have ht : (AkFin k M)ᵀ = (Ak k M)ᵀ.submatrix e.symm id := by
      rw [AkFin, Matrix.transpose_submatrix]
    rw [ht, AkFin, Matrix.submatrix_mul_equiv (Ak k M) ((Ak k M)ᵀ) id e.symm id,
      Matrix.submatrix_id_id]
  rw [sDiscOfMatrix, proposition_4_47 k M hM, hAk]

/-- Each subdiscriminant of a symmetric matrix is nonnegative (sum of squares). -/
private lemma sDisc_nonneg (k : ℕ) (M : Matrix (Fin p) (Fin p) R) (hM : M.IsSymm) :
    0 ≤ sDiscOfMatrix k M := by
  classical
  rw [theorem_4_48 k M hM]
  refine Finset.sum_nonneg (fun I _ => ?_)
  split
  · exact sq_nonneg _
  · exact le_refl 0

omit [IsRealClosed R] in
/-- **Gram determinant criterion** over an ordered field: the Gram determinant of the
rows of `A` vanishes iff those rows are linearly dependent. -/
private lemma gram_det_eq_zero_iff {m N : ℕ} (A : Matrix (Fin m) (Fin N) R) :
    (A * Aᵀ).det = 0 ↔ ¬ LinearIndependent R (fun i => A i) := by
  classical
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  -- `(A * Aᵀ) *ᵥ x = 0 ↔ Aᵀ *ᵥ x = 0`
  have hkey : ∀ x : Fin m → R, (A * Aᵀ) *ᵥ x = 0 ↔ Aᵀ *ᵥ x = 0 := by
    intro x
    constructor
    · intro h
      have hdot : x ⬝ᵥ ((A * Aᵀ) *ᵥ x) = 0 := by rw [h, dotProduct_zero]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose] at hdot
      exact dotProduct_self_eq_zero.mp hdot
    · intro h
      rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  -- `Aᵀ *ᵥ x = 0 ↔ ∑ i, x i • A i = 0`
  have hlin : ∀ x : Fin m → R, Aᵀ *ᵥ x = 0 ↔ ∑ i, x i • (A i) = 0 := by
    intro x
    rw [funext_iff, funext_iff]
    refine forall_congr' (fun c => ?_)
    rw [Matrix.mulVec, Finset.sum_apply]
    simp only [Matrix.transpose_apply, Pi.zero_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
    refine Eq.congr (Finset.sum_congr rfl (fun i _ => ?_)) rfl
    ring
  rw [Fintype.not_linearIndependent_iff]
  constructor
  · rintro ⟨x, hx, hxsum⟩
    refine ⟨x, (hlin x).mp ((hkey x).mp hxsum), ?_⟩
    rcases Function.ne_iff.mp hx with ⟨i, hi⟩
    exact ⟨i, by simpa using hi⟩
  · rintro ⟨x, hxsum, i, hi⟩
    refine ⟨x, ?_, (hkey x).mpr ((hlin x).mpr hxsum)⟩
    rw [Function.ne_iff]
    exact ⟨i, by simpa using hi⟩

/-- The rows of `AkFin (i+1) M` are a subfamily of those of `AkFin i M`. -/
private lemma akFin_succ_eq (i : ℕ) (M : Matrix (Fin p) (Fin p) R) (r : Fin (p - (i + 1))) :
    AkFin (i + 1) M r = AkFin i M (Fin.castLE (by omega) r) := by
  classical
  funext c
  simp only [AkFin, Ak, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Fin.val_castLE]

/-- **Monotonicity**: if `sDisc_{i+1}(M) = 0` then `sDisc_i(M) = 0`. -/
private lemma sDisc_succ_eq_zero (i : ℕ) (M : Matrix (Fin p) (Fin p) R) (hM : M.IsSymm) :
    sDiscOfMatrix (i + 1) M = 0 → sDiscOfMatrix i M = 0 := by
  intro h
  rw [sDisc_eq_gram (i + 1) M hM, gram_det_eq_zero_iff] at h
  rw [sDisc_eq_gram i M hM, gram_det_eq_zero_iff]
  intro hli
  apply h
  have hcomp : (fun r => AkFin (i + 1) M r)
      = (fun r => AkFin i M r) ∘ (Fin.castLE (by omega : p - (i + 1) ≤ p - i)) := by
    funext r
    exact akFin_succ_eq i M r
  rw [hcomp]
  exact hli.comp _ (Fin.castLE_injective _)

omit [IsRealClosed R] in
/-- **Top positivity**: `sDisc_{p-1}(M) = p > 0`. -/
private lemma sDisc_pred_pos [NeZero p] (M : Matrix (Fin p) (Fin p) R) :
    0 < sDiscOfMatrix (p - 1) M := by
  have hp : p - (p - 1) = 1 := by
    have := Nat.pos_of_ne_zero (NeZero.ne p); omega
  have hval : sDiscOfMatrix (p - 1) M = (p : R) := by
    rw [sDiscOfMatrix]
    rw [show (traceNewtMatrix (p - 1) M)
        = (Matrix.of fun (_ : Fin (p - (p - 1))) (_ : Fin (p - (p - 1))) =>
            Matrix.trace (M ^ (0 : ℕ))) from ?_]
    · rw [hp] at *
      rw [Matrix.det_unique, Matrix.of_apply, pow_zero, Matrix.trace_one, Fintype.card_fin]
    · funext i j
      have hi : (i : ℕ) = 0 := by omega
      have hj : (j : ℕ) = 0 := by omega
      simp only [traceNewtMatrix, Matrix.of_apply, hi, hj]
  rw [hval]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)

/-- **Proposition 4.49.** For a symmetric matrix `M`, there is `k ≤ p-1` such that the
subdiscriminants of the characteristic polynomial of `M` are positive for `k ≤ i ≤ p-1`
and zero for `i < k`. -/
theorem proposition_4_49 [NeZero p] (M : Matrix (Fin p) (Fin p) R) (hM : M.IsSymm) :
    ∃ k, k ≤ p - 1 ∧
      (∀ i, k ≤ i → i ≤ p - 1 → 0 < sDiscOfMatrix i M) ∧
      (∀ i, i < k → sDiscOfMatrix i M = 0) := by
  classical
  -- Downward closure of the zero locus.
  have hdown : ∀ d j, sDiscOfMatrix (j + d) M = 0 → sDiscOfMatrix j M = 0 := by
    intro d
    induction d with
    | zero => intro j h; simpa using h
    | succ n ih =>
        intro j h
        have hj1 : sDiscOfMatrix (j + 1) M = 0 := by
          apply ih (j + 1)
          rwa [show j + 1 + n = j + (n + 1) from by ring]
        exact sDisc_succ_eq_zero j M hM hj1
  have hdown' : ∀ i j, j ≤ i → sDiscOfMatrix i M = 0 → sDiscOfMatrix j M = 0 := by
    intro i j hji h
    have := hdown (i - j) j
    rw [show j + (i - j) = i from by omega] at this
    exact this h
  -- There is a nonzero subdiscriminant (the top one).
  have hex : ∃ i, sDiscOfMatrix i M ≠ 0 := ⟨p - 1, ne_of_gt (sDisc_pred_pos M)⟩
  set k := Nat.find hex with hk
  refine ⟨k, ?_, ?_, ?_⟩
  · exact Nat.find_le (ne_of_gt (sDisc_pred_pos M))
  · intro i hki _
    have hne : sDiscOfMatrix i M ≠ 0 := by
      intro h0
      exact Nat.find_spec hex (hdown' i k hki h0)
    exact lt_of_le_of_ne (sDisc_nonneg i M hM) (Ne.symm hne)
  · intro i hik
    have := Nat.find_min hex hik
    exact not_not.mp this
end

end Azurite.BPR.Chapter4
