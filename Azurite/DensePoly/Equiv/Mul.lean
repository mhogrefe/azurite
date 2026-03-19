import Azurite.DensePoly.Mul
import Azurite.DensePoly.Equiv.Add
import Mathlib.Algebra.Polynomial.Coeff

open Polynomial

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

/-! ### Shared helpers -/

-- Helper: coeff beyond (p.size + q.size - 1) sums to zero
private lemma coeff_beyond_zero (p q : DensePoly R) (n : ℕ)
    (h_ge : ¬(n < p.coeffs.size + q.coeffs.size - 1)) :
    ∑ x ∈ Finset.antidiagonal n, (DensePoly.toPoly p).coeff x.1 * (DensePoly.toPoly q).coeff x.2 = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  have hpz : (DensePoly.toPoly p).coeff x.1 = 0 ∨ (DensePoly.toPoly q).coeff x.2 = 0 := by
    simp_rw [coeff_toPoly]
    by_contra! hc
    have ht1 : x.1 < p.coeffs.size := by
      by_contra h_ge_p
      push_neg at h_ge_p
      exact hc.1 (by dsimp [coeff]; rw [Array.getElem?_eq_none (by omega)]; rfl)
    have ht2 : x.2 < q.coeffs.size := by
      by_contra h_ge_q
      push_neg at h_ge_q
      exact hc.2 (by dsimp [coeff]; rw [Array.getElem?_eq_none (by omega)]; rfl)
    omega
  rcases hpz with h1 | h2
  · rw [h1, zero_mul]
  · rw [h2, mul_zero]

-- Helper: empty coeffs → zero poly
omit [DecidableEq R] in
private lemma empty_implies_zero_mul (p : DensePoly R) (hp : p.coeffs.size = 0) : p = 0 :=
  DensePoly.ext (Array.eq_empty_of_size_eq_zero hp)

/-! ### Proofs for `mulBasecaseList` (old implementation, kept for comparison) -/

omit [DecidableEq R] in
lemma List.sum_map_eq_finset_sum_antidiagonal (n : ℕ) (p q : DensePoly R) :
  ((List.range (n + 1)).map (fun i => p.coeff i * q.coeff (n - i))).sum =
  ∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2 := by
  have hl : ∑ i ∈ Finset.range (n + 1), p.coeff i * q.coeff (n - i) = ((List.range (n + 1)).map (fun i => p.coeff i * q.coeff (n - i))).sum := rfl
  rw [← hl]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j) n).symm

@[simp] lemma toPoly_mulBasecaseList (p q : DensePoly R) :
  DensePoly.toPoly (mulBasecaseList p q) = DensePoly.toPoly p * DensePoly.toPoly q := by
  ext n; rw [Polynomial.coeff_mul]
  dsimp [mulBasecaseList]
  split
  · next h_empty =>
    revert h_empty; simp only [Bool.or_eq_true, beq_iff_eq]; intro h_empty
    rcases h_empty with hp | hq
    · rw [empty_implies_zero_mul p hp]; simp
    · rw [empty_implies_zero_mul q hq]; simp
  · next h_not_empty =>
    rw [toPoly_normalize, coeff_list_toPoly]
    simp only [Array.toList_ofFn]
    rw [List.getCoeff_ofFn_aux]
    split
    · next h_lt =>
      change ((List.range (n + 1)).map (fun idx => p.coeff idx * q.coeff (n - idx))).sum = _
      simp_rw [coeff_toPoly]
      exact List.sum_map_eq_finset_sum_antidiagonal n p q
    · exact (coeff_beyond_zero p q n ‹_›).symm

/-! ### Proofs for `mulBasecase` (Finset.sum-based implementation) -/

@[simp] lemma toPoly_mulBasecase (p q : DensePoly R) :
  DensePoly.toPoly (mulBasecase p q) = DensePoly.toPoly p * DensePoly.toPoly q := by
  ext n; rw [Polynomial.coeff_mul]
  dsimp [mulBasecase]
  split
  · next h_empty =>
    revert h_empty; simp only [Bool.or_eq_true, beq_iff_eq]; intro h_empty
    rcases h_empty with hp | hq
    · rw [empty_implies_zero_mul p hp]; simp
    · rw [empty_implies_zero_mul q hq]; simp
  · next h_not_empty =>
    rw [toPoly_normalize, coeff_list_toPoly]
    simp only [Array.toList_ofFn]
    rw [List.getCoeff_ofFn_aux]
    split
    · next h_lt =>
      simp_rw [coeff_toPoly]
      exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j) n).symm
    · exact (coeff_beyond_zero p q n ‹_›).symm

/-! ### Proofs for `mulBasecaseFold` (Fin.foldl-based implementation) -/

omit [DecidableEq R] in
/-- `Fin.foldl` of addition equals `Finset.range` sum. -/
lemma fin_foldl_eq_finset_range_sum (n : ℕ) (f : ℕ → R) :
    Fin.foldl n (fun acc i => acc + f i.val) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, Fin.foldl_succ_last]
    congr 1

/-- `mulBasecaseFold` produces the same result as `mulBasecase`. -/
lemma mulBasecaseFold_eq_mulBasecase (p q : DensePoly R) :
    mulBasecaseFold p q = mulBasecase p q := by
  simp only [mulBasecaseFold, mulBasecaseCoeffs, mulBasecase]
  split
  · apply DensePoly.ext; simp [normalize]
  · apply congrArg; apply congrArg; funext n
    exact fin_foldl_eq_finset_range_sum (↑n + 1)
      (fun j => p.coeff j * q.coeff (↑n - j))

@[simp] lemma toPoly_mulBasecaseFold (p q : DensePoly R) :
    DensePoly.toPoly (mulBasecaseFold p q) = DensePoly.toPoly p * DensePoly.toPoly q := by
  rw [mulBasecaseFold_eq_mulBasecase]; exact toPoly_mulBasecase p q

/-! ### Lift to `mul` -/

@[simp] lemma toPoly_mul (p q : DensePoly R) :
    DensePoly.toPoly (p * q) = DensePoly.toPoly p * DensePoly.toPoly q := by
  show DensePoly.toPoly (DensePolyMulConfig.dmul p q) = _
  simp [DensePolyMulConfig.dmul, toPoly_mulBasecaseFold]

@[simp] lemma coeff_mul (p q : DensePoly R) (n : ℕ) :
    coeff (p * q) n = ∑ x ∈ Finset.antidiagonal n, coeff p x.1 * coeff q x.2 := by
  have h := toPoly_mul p q
  have hc := congr_fun (congr_arg Polynomial.coeff h) n
  rw [Polynomial.coeff_mul] at hc
  simp_rw [coeff_toPoly] at hc
  exact hc

@[simp] lemma ofPoly_mul (p q : Polynomial R) :
    DensePoly.ofPoly (p * q) = DensePoly.ofPoly p * DensePoly.ofPoly q := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_mul, toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

end Azurite.DensePoly
