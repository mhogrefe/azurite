import Azurite.BasuPollackRoy.Chapter10.Section10_1.Notation_10_1

/-!
# BPR Lemma 10.2: the Cauchy bound bounds the roots

`lemma_10_2`: every root of `P ≠ 0` has absolute value strictly smaller than
the Cauchy bound `C(P)` of Notation 10.1. BPR's proof: writing
`aₚx = −∑_{i<p} aᵢ x^{i−p+1}`, for `|x| ≥ 1` each `|x|^{i−p+1} ≤ 1` gives
`|aₚ||x| ≤ ∑_{i<p}|aᵢ|`, that is `|x| ≤ C(P) − 1 < C(P)`; for `|x| ≤ 1` the
bound follows from `C(P) ≥ 1`.

The statement holds over any ordered field; in BPR's setting the field is a
real closed `R` containing the coefficient field `K`. The companion lower
bound is Lemma 10.3 (`Lemma_10_3.lean`), derived from this lemma via the
reciprocal polynomial.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **BPR Lemma 10.2 (Cauchy).** The absolute value of any root of `P` is
smaller than `C(P)`. -/
theorem lemma_10_2 {P : K[X]} (hP : P ≠ 0) {x : K} (hx : P.IsRoot x) :
    |x| < cauchyBound P := by
  set p := P.natDegree with hp
  -- a nonzero polynomial with a root has positive degree
  have hdP : 0 < p := by
    by_contra h0
    have hC := Polynomial.eq_C_of_natDegree_eq_zero (by omega : P.natDegree = 0)
    rw [hC, Polynomial.IsRoot, Polynomial.eval_C] at hx
    exact hP (by rw [hC, hx, Polynomial.C_0])
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  rcases lt_or_ge |x| 1 with hx1 | hx1
  -- |x| ≤ 1: immediate from C(P) ≥ 1
  · exact lt_of_lt_of_le hx1 (one_le_cauchyBound hP)
  -- |x| ≥ 1: normalize the vanishing evaluation by the leading coefficient
  have heval : ∑ i ∈ Finset.range (p + 1), (P.coeff i / P.leadingCoeff) * x ^ i = 0 := by
    have h0 : ∑ i ∈ Finset.range (p + 1), P.coeff i * x ^ i = 0 := by
      have h := hx
      rwa [Polynomial.IsRoot, Polynomial.eval_eq_sum_range] at h
    calc ∑ i ∈ Finset.range (p + 1), (P.coeff i / P.leadingCoeff) * x ^ i
        = (∑ i ∈ Finset.range (p + 1), P.coeff i * x ^ i) / P.leadingCoeff := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := by rw [h0, zero_div]
  rw [Finset.sum_range_succ, show P.coeff p / P.leadingCoeff = 1 from by
    rw [show P.coeff p = P.leadingCoeff from rfl, div_self hlc], one_mul] at heval
  have hxp : x ^ p = -∑ i ∈ Finset.range p, (P.coeff i / P.leadingCoeff) * x ^ i := by
    linarith [heval]
  -- the estimate: |x|ᵖ ≤ (C(P) − 1)·|x|^{p−1}
  have hkey : |x| ^ p ≤ (cauchyBound P - 1) * |x| ^ (p - 1) := by
    calc |x| ^ p = |x ^ p| := (abs_pow x p).symm
      _ = |∑ i ∈ Finset.range p, (P.coeff i / P.leadingCoeff) * x ^ i| := by
          rw [hxp, abs_neg]
      _ ≤ ∑ i ∈ Finset.range p, |(P.coeff i / P.leadingCoeff) * x ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range p, |P.coeff i / P.leadingCoeff| * |x| ^ (p - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hx1 (by
              have := Finset.mem_range.mp hi
              omega : i ≤ p - 1)) (abs_nonneg _)
      _ = (∑ i ∈ Finset.range p, |P.coeff i / P.leadingCoeff|) * |x| ^ (p - 1) := by
          rw [← Finset.sum_mul]
      _ = (cauchyBound P - 1) * |x| ^ (p - 1) := by
          congr 1
          rw [cauchyBound, ← hp, Finset.sum_range_succ,
            show P.coeff p / P.leadingCoeff = 1 from by
              rw [show P.coeff p = P.leadingCoeff from rfl, div_self hlc], abs_one]
          ring
  -- divide by |x|^{p−1} and conclude
  have hxpow : (0 : K) < |x| ^ (p - 1) := by positivity
  have hxsplit : |x| ^ p = |x| * |x| ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hxsplit] at hkey
  have h2 : |x| ≤ cauchyBound P - 1 := le_of_mul_le_mul_right hkey hxpow
  linarith [one_le_cauchyBound hP]

end Azurite.BPR
