import Azurite.DensePoly.Mul
import Azurite.DensePoly.Equiv.Add
import Mathlib.Algebra.Polynomial.Coeff

open Polynomial

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

omit [DecidableEq R] in
lemma List.sum_map_eq_finset_sum_antidiagonal (n : ℕ) (p q : DensePoly R) :
  ((List.range (n + 1)).map (fun i => p.coeff i * q.coeff (n - i))).sum =
  ∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2 := by
  have hl : ∑ i ∈ Finset.range (n + 1), p.coeff i * q.coeff (n - i) = ((List.range (n + 1)).map (fun i => p.coeff i * q.coeff (n - i))).sum := rfl
  rw [← hl]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j) n).symm

@[simp] lemma toPoly_mulBasecase (p q : DensePoly R) :
  DensePoly.toPoly (mulBasecase p q) = DensePoly.toPoly p * DensePoly.toPoly q := by
  ext n
  rw [Polynomial.coeff_mul]
  dsimp [mulBasecase]
  split
  · next h_empty =>
    revert h_empty
    simp only [Bool.or_eq_true, beq_iff_eq]
    intro h_empty
    rcases h_empty with hp | hq
    · have hp0 : p = 0 := by
        apply DensePoly.ext
        dsimp [zero]
        have hl : p.coeffs.toList.length = 0 := by
          rw [Array.length_toList]
          exact hp
        exact Array.ext' (List.length_eq_zero_iff.mp hl)
      rw [hp0]
      simp
    · have hq0 : q = 0 := by
        apply DensePoly.ext
        dsimp [zero]
        have hl : q.coeffs.toList.length = 0 := by
          rw [Array.length_toList]
          exact hq
        exact Array.ext' (List.length_eq_zero_iff.mp hl)
      rw [hq0]
      simp
  · next h_not_empty =>
    have h_norm : DensePoly.toPoly (normalize (Array.ofFn (fun (i : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
      ((List.range (i.val + 1)).map (fun idx => p.coeff idx * q.coeff (i.val - idx))).sum))) =
      (Array.ofFn (fun (i : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
      ((List.range (i.val + 1)).map (fun idx => p.coeff idx * q.coeff (i.val - idx))).sum)).toList.toPoly := by
      exact toPoly_normalize _
    rw [h_norm]
    rw [coeff_list_toPoly]
    have hof : (Array.ofFn (fun (i : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
      ((List.range (i.val + 1)).map (fun idx => p.coeff idx * q.coeff (i.val - idx))).sum)).toList = 
               List.ofFn (fun (i : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
      ((List.range (i.val + 1)).map (fun idx => p.coeff idx * q.coeff (i.val - idx))).sum) := by
      simp
    rw [hof, List.getCoeff_ofFn_aux]
    split
    · next h_lt =>
      change ((List.range (n + 1)).map (fun idx => p.coeff idx * q.coeff (n - idx))).sum = _
      simp_rw [coeff_toPoly]
      exact List.sum_map_eq_finset_sum_antidiagonal n p q
    · next h_ge =>
      simp_rw [coeff_toPoly]
      symm
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_antidiagonal] at hx
      have hpz : p.coeff x.1 = 0 ∨ q.coeff x.2 = 0 := by
        by_contra! hc
        have ht1 : x.1 < p.coeffs.size := by
          by_contra h_ge_p
          have h1 : p.coeff x.1 = 0 := by
            dsimp [coeff]
            have hn_p : p.coeffs.toList.length ≤ x.1 := by
              have hs : p.coeffs.size = p.coeffs.toList.length := Array.length_toList.symm
              omega
            rw [← Array.getElem?_toList]
            rw [List.getElem?_eq_none hn_p]
            rfl
          exact hc.1 h1
        have ht2 : x.2 < q.coeffs.size := by
          by_contra h_ge_q
          have h2 : q.coeff x.2 = 0 := by
            dsimp [coeff]
            have hn_q : q.coeffs.toList.length ≤ x.2 := by
              have hs : q.coeffs.size = q.coeffs.toList.length := Array.length_toList.symm
              omega
            rw [← Array.getElem?_toList]
            rw [List.getElem?_eq_none hn_q]
            rfl
          exact hc.2 h2
        omega
      rcases hpz with h1 | h2
      · rw [h1, zero_mul]
      · rw [h2, mul_zero]

@[simp] lemma coeff_mulBasecase (p q : DensePoly R) (n : ℕ) :
  coeff (mulBasecase p q) n = ∑ x ∈ Finset.antidiagonal n, coeff p x.1 * coeff q x.2 := by
  have h := toPoly_mulBasecase p q
  have hc : (DensePoly.toPoly (mulBasecase p q)).coeff n = (DensePoly.toPoly p * DensePoly.toPoly q).coeff n := by rw [h]
  rw [Polynomial.coeff_mul] at hc
  simp_rw [coeff_toPoly] at hc
  exact hc

@[simp] lemma ofPoly_mulBasecase (p q : Polynomial R) :
  DensePoly.ofPoly (p * q) = mulBasecase (DensePoly.ofPoly p) (DensePoly.ofPoly q) := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_mulBasecase, toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

-- Lift to `mul`
@[simp] lemma toPoly_mul (p q : DensePoly R) : DensePoly.toPoly (p * q) = DensePoly.toPoly p * DensePoly.toPoly q := by
  dsimp [HMul.hMul, Mul.mul, mul]
  exact toPoly_mulBasecase p q

@[simp] lemma coeff_mul (p q : DensePoly R) (n : ℕ) : coeff (p * q) n = ∑ x ∈ Finset.antidiagonal n, coeff p x.1 * coeff q x.2 := by
  dsimp [HMul.hMul, Mul.mul, mul]
  exact coeff_mulBasecase p q n

@[simp] lemma ofPoly_mul (p q : Polynomial R) : DensePoly.ofPoly (p * q) = DensePoly.ofPoly p * DensePoly.ofPoly q := by
  dsimp [HMul.hMul, Mul.mul, mul]
  exact ofPoly_mulBasecase p q

end Azurite.DensePoly
