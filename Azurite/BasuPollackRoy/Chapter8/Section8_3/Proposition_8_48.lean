import Azurite.BasuPollackRoy.Chapter8.Section8_2.Corollary_8_13
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_42

/-!
# BPR §8.3.4 Proposition 8.48: size of signed subresultants

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, Springer 2006, §8.3.4.

**Proposition 8.48.** If `P, Q ∈ ℤ[X]` have degrees `p, q` and coefficients of bitsize at most
`τ` (with `1 ≤ τ`), then the coefficients of `sResP_j(P,Q)`, `sResU_j(P,Q)`, `sResV_j(P,Q)` have
bitsize at most `(τ + bit(p+q-2j))·(p+q-2j)`.

Proof (BPR): each such coefficient is a determinant (or minor) of a `(p+q-2j) × (p+q-2j)` integer
matrix whose entries are coefficients of `P, Q` (bitsize `≤ τ`), so Corollary 8.13 bounds it.
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

/-- The bitsize of an `n × n` integer determinant whose entries have bitsize `≤ τ` is at most
    `n·(τ + bit n)`.  (A clean integer reading of Corollary 8.13, derived from its square form.) -/
theorem int_size_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) {τ : ℕ} (hn : 0 < n)
    (hτ : ∀ i j, Int.size (M i j) ≤ τ) : Int.size M.det ≤ n * (τ + Nat.size n) := by
  have hsq := corollary_8_13_sq M hn hτ
  have hle : M.det.natAbs ^ 2 < (2 ^ (n * (τ + Nat.size n))) ^ 2 := by
    rw [← pow_mul]
    refine lt_of_lt_of_le hsq (Nat.pow_le_pow_right (by norm_num) ?_)
    nlinarith [Nat.zero_le (n * Nat.size n)]
  have hlt : M.det.natAbs < 2 ^ (n * (τ + Nat.size n)) :=
    lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hle
  rw [Int.size]
  exact Nat.size_le.mpr hlt

/-- A coefficient of `X^s · P` is either a coefficient of `P` or `0`, hence has bitsize `≤ τ`
    when `P`'s coefficients do. -/
theorem int_size_coeff_X_pow_mul {P : ℤ[X]} {τ : ℕ} (hP : ∀ i, Int.size (P.coeff i) ≤ τ)
    (s c : ℕ) : Int.size ((X ^ s * P).coeff c) ≤ τ := by
  rw [mul_comm, Polynomial.coeff_mul_X_pow']
  split_ifs
  · exact hP _
  · simp [Int.size]

/-- **BPR Proposition 8.48, `sResP` part.**  Each coefficient of `sResP_j(P,Q)` has bitsize at
    most `(p+q-2j)·(τ + bit(p+q-2j))`: for `a ≤ j` it is the `(p+q-2j)×(p+q-2j)` minor
    `pdetMinorRing`, whose entries are coefficients of `P, Q` (bitsize `≤ τ`); for `a > j` it
    vanishes. -/
theorem sResP_coeff_size_le (P Q : ℤ[X]) {τ : ℕ}
    (hP : ∀ i, Int.size (P.coeff i) ≤ τ) (hQ : ∀ i, Int.size (Q.coeff i) ≤ τ)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hjq : j ≤ Q.natDegree) (a : ℕ) :
    Int.size ((sResP P Q j).coeff a)
      ≤ (P.natDegree + Q.natDegree - 2 * j)
          * (τ + Nat.size (P.natDegree + Q.natDegree - 2 * j)) := by
  by_cases ha : a ≤ j
  · rw [sResP, if_pos hjq,
      pdetRing_coeff _ (show a ≤ P.natDegree + Q.natDegree - j - (P.natDegree + Q.natDegree - 2 * j)
        by omega), pdetMinorRing]
    refine int_size_det_le _ (show 0 < P.natDegree + Q.natDegree - 2 * j by omega) (fun r c => ?_)
    rw [pdetMinorMatRing]
    by_cases hr : (r : ℕ) < Q.natDegree - j
    · simp only [hr, if_true]; exact int_size_coeff_X_pow_mul hP _ _
    · simp only [hr, if_false]; exact int_size_coeff_X_pow_mul hQ _ _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hjq)) (by omega))]
    simp [Int.size]

/-- **Coefficient of a determinant with a single polynomial column.**  If the only `X`-dependent
    column of `M` is the last (the others are constants `C(A r c)`), the `X^a`-coefficient of
    `det M` is the determinant of the integer matrix `A` with its last column replaced by the
    `X^a`-coefficients of that polynomial column. -/
theorem coeff_det_lastCol {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℤ)
    (V : Fin N → ℤ[X]) (M : Matrix (Fin N) (Fin N) ℤ[X])
    (hM : ∀ r c, M r c = if (c : ℕ) + 1 < N then C (A r c) else V r) (a : ℕ) :
    (M.det).coeff a = (A.updateCol ⟨N - 1, by omega⟩ (fun r => (V r).coeff a)).det := by
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Units.smul_def, zsmul_eq_mul, Polynomial.coeff_intCast_mul]
  congr 1
  set last : Fin N := ⟨N - 1, by omega⟩ with hlast
  have hrest : ∀ i ∈ Finset.univ.erase last, M (σ i) i = C (A (σ i) i) := by
    intro i hi
    rw [hM, if_pos]
    have hine : i ≠ last := (Finset.mem_erase.mp hi).1
    have : (i : ℕ) ≠ N - 1 := fun h => hine (Fin.ext (by simp [hlast, h]))
    have := i.isLt; omega
  have hUrest : ∀ i ∈ Finset.univ.erase last,
      (A.updateCol last (fun r => (V r).coeff a)) (σ i) i = A (σ i) i :=
    fun i hi => Matrix.updateCol_ne (Finset.mem_erase.mp hi).1
  rw [← Finset.mul_prod_erase Finset.univ (fun i => M (σ i) i) (Finset.mem_univ last),
    hM (σ last) last, if_neg (show ¬ (last : ℕ) + 1 < N by simp [hlast]; omega),
    Finset.prod_congr rfl hrest, ← map_prod Polynomial.C, Polynomial.coeff_mul_C,
    ← Finset.mul_prod_erase Finset.univ
      (fun i => (A.updateCol last (fun r => (V r).coeff a)) (σ i) i) (Finset.mem_univ last),
    Matrix.updateCol_self, Finset.prod_congr rfl hUrest]

/-- A coefficient of the monomial `X^e` has bitsize `≤ 1 ≤ τ`. -/
theorem int_size_coeff_X_pow {τ : ℕ} (hτ1 : 1 ≤ τ) (e a : ℕ) :
    Int.size ((X ^ e : ℤ[X]).coeff a) ≤ τ := by
  rw [Polynomial.coeff_X_pow]
  split_ifs
  · exact le_trans (by decide) hτ1
  · simp [Int.size]

/-- The Sylvester–Habicht entries have bitsize `≤ τ`. -/
theorem int_size_SyHa_le {P Q : ℤ[X]} {τ : ℕ}
    (hP : ∀ i, Int.size (P.coeff i) ≤ τ) (hQ : ∀ i, Int.size (Q.coeff i) ≤ τ) (j : ℕ)
    (i : Fin (P.natDegree + Q.natDegree - 2 * j))
    (k : Fin (P.natDegree + Q.natDegree - j)) :
    Int.size (Chapter4.SyHa P Q j i k) ≤ τ := by
  rw [Chapter4.SyHa, Matrix.of_apply]
  split_ifs
  · exact int_size_coeff_X_pow_mul hP _ _
  · exact int_size_coeff_X_pow_mul hQ _ _

/-- **BPR Proposition 8.48, `sResU` part.** -/
theorem sResU_coeff_size_le (P Q : ℤ[X]) {τ : ℕ} (hτ1 : 1 ≤ τ)
    (hP : ∀ i, Int.size (P.coeff i) ≤ τ) (hQ : ∀ i, Int.size (Q.coeff i) ≤ τ)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hjq : j ≤ Q.natDegree) (a : ℕ) :
    Int.size ((sResU P Q j).coeff a)
      ≤ (P.natDegree + Q.natDegree - 2 * j)
          * (τ + Nat.size (P.natDegree + Q.natDegree - 2 * j)) := by
  rw [sResU, coeff_det_lastCol (show 0 < P.natDegree + Q.natDegree - 2 * j by omega)
    (Matrix.of fun i k => Chapter4.SyHa P Q j i (Fin.castLE (by omega) k))
    (fun i => if (i : ℕ) < Q.natDegree - j then X ^ (Q.natDegree - 1 - j - (i : ℕ)) else 0)
    (sResUMat P Q j) (fun r c => by rw [sResUMat, Matrix.of_apply, Matrix.of_apply]) a]
  refine int_size_det_le _ (show 0 < P.natDegree + Q.natDegree - 2 * j by omega) (fun i k => ?_)
  show Int.size
      (Matrix.updateCol
        (Matrix.of fun i k => Chapter4.SyHa P Q j i (Fin.castLE (by omega) k))
        ⟨P.natDegree + Q.natDegree - 2 * j - 1, by omega⟩
        (fun r => (if (r : ℕ) < Q.natDegree - j
          then X ^ (Q.natDegree - 1 - j - (r : ℕ)) else 0).coeff a) i k) ≤ τ
  rw [Matrix.updateCol_apply]
  by_cases hk : k = ⟨P.natDegree + Q.natDegree - 2 * j - 1, by omega⟩
  · rw [if_pos hk]
    split_ifs
    · exact int_size_coeff_X_pow hτ1 _ _
    · simp [Int.size]
  · rw [if_neg hk]
    exact int_size_SyHa_le hP hQ j i _

/-- **BPR Proposition 8.48, `sResV` part.** -/
theorem sResV_coeff_size_le (P Q : ℤ[X]) {τ : ℕ} (hτ1 : 1 ≤ τ)
    (hP : ∀ i, Int.size (P.coeff i) ≤ τ) (hQ : ∀ i, Int.size (Q.coeff i) ≤ τ)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hjq : j ≤ Q.natDegree) (a : ℕ) :
    Int.size ((sResV P Q j).coeff a)
      ≤ (P.natDegree + Q.natDegree - 2 * j)
          * (τ + Nat.size (P.natDegree + Q.natDegree - 2 * j)) := by
  rw [sResV, coeff_det_lastCol (show 0 < P.natDegree + Q.natDegree - 2 * j by omega)
    (Matrix.of fun i k => Chapter4.SyHa P Q j i (Fin.castLE (by omega) k))
    (fun i => if (i : ℕ) < Q.natDegree - j then 0 else X ^ ((i : ℕ) - (Q.natDegree - j)))
    (sResVMat P Q j) (fun r c => by rw [sResVMat, Matrix.of_apply, Matrix.of_apply]) a]
  refine int_size_det_le _ (show 0 < P.natDegree + Q.natDegree - 2 * j by omega) (fun i k => ?_)
  show Int.size
      (Matrix.updateCol
        (Matrix.of fun i k => Chapter4.SyHa P Q j i (Fin.castLE (by omega) k))
        ⟨P.natDegree + Q.natDegree - 2 * j - 1, by omega⟩
        (fun r => (if (r : ℕ) < Q.natDegree - j
          then 0 else X ^ ((r : ℕ) - (Q.natDegree - j))).coeff a) i k) ≤ τ
  rw [Matrix.updateCol_apply]
  by_cases hk : k = ⟨P.natDegree + Q.natDegree - 2 * j - 1, by omega⟩
  · rw [if_pos hk]
    split_ifs
    · simp [Int.size]
    · exact int_size_coeff_X_pow hτ1 _ _
  · rw [if_neg hk]
    exact int_size_SyHa_le hP hQ j i _

/-- **BPR Proposition 8.48 (size of signed subresultants).**  If `P, Q ∈ ℤ[X]` have coefficients
    of bitsize at most `τ` (with `1 ≤ τ`), then every coefficient of `sResP_j(P,Q)`,
    `sResU_j(P,Q)`, `sResV_j(P,Q)` has bitsize at most `(p+q-2j)·(τ + bit(p+q-2j))`. -/
theorem proposition_8_48 (P Q : ℤ[X]) {τ : ℕ} (hτ1 : 1 ≤ τ)
    (hP : ∀ i, Int.size (P.coeff i) ≤ τ) (hQ : ∀ i, Int.size (Q.coeff i) ≤ τ)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hjq : j ≤ Q.natDegree) (a : ℕ) :
    Int.size ((sResP P Q j).coeff a)
        ≤ (P.natDegree + Q.natDegree - 2 * j)
            * (τ + Nat.size (P.natDegree + Q.natDegree - 2 * j))
      ∧ Int.size ((sResU P Q j).coeff a)
        ≤ (P.natDegree + Q.natDegree - 2 * j)
            * (τ + Nat.size (P.natDegree + Q.natDegree - 2 * j))
      ∧ Int.size ((sResV P Q j).coeff a)
        ≤ (P.natDegree + Q.natDegree - 2 * j)
            * (τ + Nat.size (P.natDegree + Q.natDegree - 2 * j)) :=
  ⟨sResP_coeff_size_le P Q hP hQ hpq hjq a, sResU_coeff_size_le P Q hτ1 hP hQ hpq hjq a,
    sResV_coeff_size_le P Q hτ1 hP hQ hpq hjq a⟩

end Azurite.BPR.Chapter8
