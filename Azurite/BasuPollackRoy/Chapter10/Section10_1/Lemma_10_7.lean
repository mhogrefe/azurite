import Azurite.BasuPollackRoy.Chapter10.Section10_1.Lemma_10_3
import Azurite.BasuPollackRoy.Chapter10.Section10_1.Lemma_10_6

/-!
# BPR Lemma 10.7: the lower modified Cauchy bound

`lemma_10_7`: every *nonzero* root of `P ≠ 0` has absolute value strictly
greater than `c′(P)` (Notation 10.5). BPR's proof: apply Lemma 10.6 to the
reciprocal polynomial `x^p P(1/x)`, exactly as Lemma 10.3 derives the `c(P)`
bound from Lemma 10.2.

The bridge differs from Lemma 10.3's in one respect: the reversal has degree
`p − q`, so its modified Cauchy bound carries the factor `p − q + 1` where
`c′(P)⁻¹` carries `p + 1`. The bridge is therefore the *inequality*
`cauchyBound'_reverse_le : C′(x^p P(1/x)) ≤ c′(P)⁻¹` — all the lemma needs —
with the square sums themselves agreeing by the same coefficient reindexing.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The modified Cauchy bound of the reciprocal polynomial is at most the
reciprocal of `c′(P)`: the square sums agree by reindexing, and the reversal's
degree factor `p − q + 1` is at most `p + 1`. -/
theorem cauchyBound'_reverse_le (P : K[X]) :
    cauchyBound' P.reverse ≤ (cauchyLowerBound' P)⁻¹ := by
  set p := P.natDegree with hp
  set q := P.natTrailingDegree with hq
  have hqp : q ≤ p := Polynomial.natTrailingDegree_le_natDegree P
  rw [cauchyBound', cauchyLowerBound', inv_inv, Polynomial.reverse_natDegree,
    Polynomial.reverse_leadingCoeff]
  -- the square sums agree, by the reindexing of Lemma 10.3's bridge
  have hsums : ∑ i ∈ Finset.range (p - q + 1), (P.reverse.coeff i / P.trailingCoeff) ^ 2
      = ∑ i ∈ Finset.range (p + 1), (P.coeff i / P.trailingCoeff) ^ 2 := by
    have hcoeff : ∀ i ∈ Finset.range (p - q + 1),
        (P.reverse.coeff i / P.trailingCoeff) ^ 2
          = (P.coeff (p - i) / P.trailingCoeff) ^ 2 := by
      intro i hi
      rw [Polynomial.coeff_reverse, Polynomial.revAt_le (by
        have := Finset.mem_range.mp hi
        omega : i ≤ p)]
    rw [Finset.sum_congr rfl hcoeff]
    have hext : ∑ i ∈ Finset.range (p + 1), (P.coeff (p - i) / P.trailingCoeff) ^ 2
        = ∑ i ∈ Finset.range (p - q + 1), (P.coeff (p - i) / P.trailingCoeff) ^ 2 := by
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le (p - q + 1)) (by omega : p - q + 1 ≤ p + 1),
        ← Finset.range_eq_Ico, Finset.sum_eq_zero (s := Finset.Ico (p - q + 1) (p + 1)),
        add_zero]
      intro i hi
      rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by
        have := Finset.mem_Ico.mp hi
        omega : p - i < q), zero_div, zero_pow (by omega : (2:ℕ) ≠ 0)]
    rw [← hext]
    have hreflect := Finset.sum_range_reflect
      (fun j => (P.coeff j / P.trailingCoeff) ^ 2) (p + 1)
    calc ∑ i ∈ Finset.range (p + 1), (P.coeff (p - i) / P.trailingCoeff) ^ 2
        = ∑ i ∈ Finset.range (p + 1), (P.coeff (p + 1 - 1 - i) / P.trailingCoeff) ^ 2 := by
          exact Finset.sum_congr rfl (fun i hi => by norm_num)
      _ = ∑ j ∈ Finset.range (p + 1), (P.coeff j / P.trailingCoeff) ^ 2 := hreflect
  rw [hsums]
  -- the factor of the reversal is smaller: p − q + 1 ≤ p + 1
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have : ((p - q : ℕ) : K) ≤ (p : K) := Nat.cast_le.mpr (by omega)
  linarith

/-- **BPR Lemma 10.7.** The absolute value of any nonzero root of `P` is
bigger than `c′(P)`. Follows from Lemma 10.6 applied to the reciprocal
polynomial `x^p P(1/x)`. -/
theorem lemma_10_7 {P : K[X]} (hP : P ≠ 0) {x : K} (hx : P.IsRoot x) (hx0 : x ≠ 0) :
    cauchyLowerBound' P < |x| := by
  have hrev_ne : P.reverse ≠ 0 := by
    rw [Ne, Polynomial.reverse_eq_zero]
    exact hP
  -- `x⁻¹` is a root of the reciprocal polynomial
  have hxinv : P.reverse.IsRoot x⁻¹ := by
    rw [Polynomial.isRoot_reverse_iff (inv_ne_zero hx0), inv_inv]
    exact hx
  -- Lemma 10.6 for the reversal, bounded through the bridge
  have h2 := lt_of_lt_of_le (lemma_10_6 hrev_ne hxinv) (cauchyBound'_reverse_le P)
  rw [abs_inv] at h2
  exact (inv_lt_inv₀ (abs_pos.mpr hx0) (cauchyLowerBound'_pos hP)).mp h2

end Azurite.BPR
