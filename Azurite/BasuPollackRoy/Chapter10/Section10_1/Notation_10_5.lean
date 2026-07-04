import Azurite.BasuPollackRoy.Chapter10.Section10_1.Notation_10_1

/-!
# BPR Notation 10.5: the modified Cauchy bounds

The modified Cauchy bounds replace the absolute values of Notation 10.1 by
squares, at the cost of a factor `p + 1`:

* `C′(P) = (p+1) · ∑_{q ≤ i ≤ p} aᵢ²/aₚ²`,
* `c′(P) = ((p+1) · ∑_{q ≤ i ≤ p} aᵢ²/a_q²)⁻¹`.

Being rational expressions in the coefficients — no absolute values — they
can be used where a bound must itself be a polynomial expression in
parameters. As in Notation 10.1, the Lean sums run over `0 ≤ i ≤ p`; the
extra terms vanish.

The support lemmas mirror Notation 10.1's: both normalizing sums contain a
term equal to `1` (at `i = p` and `i = q`), so `C′(P) ≥ 1` and
`0 < c′(P) ≤ 1`.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **BPR Notation 10.5 (modified Cauchy bound).**
`C′(P) = (p+1) · ∑ᵢ (aᵢ/aₚ)²`. -/
noncomputable def cauchyBound' (P : K[X]) : K :=
  (P.natDegree + 1) * ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i / P.leadingCoeff) ^ 2

/-- **BPR Notation 10.5 (modified Cauchy bound), lower version.**
`c′(P) = ((p+1) · ∑ᵢ (aᵢ/a_q)²)⁻¹` where `a_q` is the trailing coefficient. -/
noncomputable def cauchyLowerBound' (P : K[X]) : K :=
  ((P.natDegree + 1) *
    ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i / P.trailingCoeff) ^ 2)⁻¹

/-- The normalizing square sum of `C′(P)` is at least `1` (the `i = p` term
is `1`). -/
theorem one_le_sum_sq_div_leadingCoeff {P : K[X]} (hP : P ≠ 0) :
    1 ≤ ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i / P.leadingCoeff) ^ 2 := by
  have h1 : (P.coeff P.natDegree / P.leadingCoeff) ^ 2 = 1 := by
    rw [show P.coeff P.natDegree = P.leadingCoeff from rfl,
      div_self (Polynomial.leadingCoeff_ne_zero.mpr hP), one_pow]
  calc (1 : K) = (P.coeff P.natDegree / P.leadingCoeff) ^ 2 := h1.symm
    _ ≤ _ := Finset.single_le_sum
        (f := fun i => (P.coeff i / P.leadingCoeff) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.self_mem_range_succ P.natDegree)

/-- The normalizing square sum of `c′(P)` is at least `1` (the `i = q` term
is `1`). -/
theorem one_le_sum_sq_div_trailingCoeff {P : K[X]} (hP : P ≠ 0) :
    1 ≤ ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i / P.trailingCoeff) ^ 2 := by
  have htc : P.trailingCoeff ≠ 0 := fun h => hP (Polynomial.trailingCoeff_eq_zero.mp h)
  have h1 : (P.coeff P.natTrailingDegree / P.trailingCoeff) ^ 2 = 1 := by
    rw [show P.coeff P.natTrailingDegree = P.trailingCoeff from rfl, div_self htc, one_pow]
  calc (1 : K) = (P.coeff P.natTrailingDegree / P.trailingCoeff) ^ 2 := h1.symm
    _ ≤ _ := Finset.single_le_sum
        (f := fun i => (P.coeff i / P.trailingCoeff) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_range_succ_iff.mpr (Polynomial.natTrailingDegree_le_natDegree P))

theorem one_le_cauchyBound' {P : K[X]} (hP : P ≠ 0) : 1 ≤ cauchyBound' P := by
  rw [cauchyBound']
  calc (1 : K) = 1 * 1 := (one_mul 1).symm
    _ ≤ (P.natDegree + 1) * ∑ i ∈ Finset.range (P.natDegree + 1),
          (P.coeff i / P.leadingCoeff) ^ 2 := by
        apply mul_le_mul _ (one_le_sum_sq_div_leadingCoeff hP) zero_le_one (by positivity)
        have : (0 : K) ≤ (P.natDegree : K) := by positivity
        linarith

theorem cauchyBound'_pos {P : K[X]} (hP : P ≠ 0) : 0 < cauchyBound' P :=
  lt_of_lt_of_le one_pos (one_le_cauchyBound' hP)

/-- The full normalizing product of `c′(P)` is at least `1`. -/
theorem one_le_mul_sum_sq_trailing {P : K[X]} (hP : P ≠ 0) :
    1 ≤ (P.natDegree + 1 : K) *
      ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i / P.trailingCoeff) ^ 2 := by
  calc (1 : K) = 1 * 1 := (one_mul 1).symm
    _ ≤ _ := by
        apply mul_le_mul _ (one_le_sum_sq_div_trailingCoeff hP) zero_le_one (by positivity)
        have : (0 : K) ≤ (P.natDegree : K) := by positivity
        linarith

theorem cauchyLowerBound'_pos {P : K[X]} (hP : P ≠ 0) : 0 < cauchyLowerBound' P :=
  inv_pos.mpr (lt_of_lt_of_le one_pos (one_le_mul_sum_sq_trailing hP))

theorem cauchyLowerBound'_le_one {P : K[X]} (hP : P ≠ 0) : cauchyLowerBound' P ≤ 1 := by
  rw [cauchyLowerBound',
    inv_le_one₀ (lt_of_lt_of_le one_pos (one_le_mul_sum_sq_trailing hP))]
  exact one_le_mul_sum_sq_trailing hP

end Azurite.BPR
