import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Sign.Defs
import Mathlib.Tactic.Positivity

/-! # BPR Section 2.1 — Proposition 2.4: Sign of polynomial for large `|x|`

**Proposition 2.4 (BPR p.35).** Let `P = aₚ Xᵖ + … + a₀`, `aₚ ≠ 0`, be
a polynomial with coefficients in an ordered field `F`. If
```
|x| > 2 ∑_{i ≤ p} |aᵢ / aₚ|,
```
then `P(x)` and `aₚ · xᵖ` have the same sign.

*Proof sketch.* Write `P(x) = L + R` where `L = aₚ · xᵖ` is the
leading term and `R = ∑_{i < p} aᵢ · xⁱ` is the remainder. Show
`|R| < |L|` using the hypothesis, which forces
`sign(P(x)) = sign(L)`.
-/

namespace Azurite.BPR

open Polynomial

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- If |a − b| < |b| and b ≠ 0, then sign(a) = sign(b). -/
private lemma sign_eq_of_abs_sub_lt {a b : F} (hb : b ≠ 0) (h : |a - b| < |b|) :
    SignType.sign a = SignType.sign b := by
  rcases lt_or_gt_of_ne hb with hbn | hbp
  · have : a < 0 := by
      linarith [abs_of_neg hbn, (abs_sub_lt_iff.mp h).1, (abs_sub_lt_iff.mp h).2]
    rw [sign_neg hbn, sign_neg this]
  · have : 0 < a := by
      linarith [abs_of_pos hbp, (abs_sub_lt_iff.mp h).1, (abs_sub_lt_iff.mp h).2]
    rw [sign_pos hbp, sign_pos this]

/-- The tail of P (everything except the leading term) evaluated at x. -/
private lemma eval_sub_lead (P : F[X]) (x : F) :
    P.eval x - P.leadingCoeff * x ^ P.natDegree =
    ∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i := by
  have h : P.eval x = (∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i)
      + P.coeff P.natDegree * x ^ P.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
  unfold leadingCoeff
  linarith

/-- **BPR Proposition 2.4.** If |x| > 2 ∑ᵢ≤ₚ |aᵢ/aₚ|, then P(x) and
    aₚ·x^p have the same sign. -/
theorem prop_2_4 (P : F[X]) (hP : P ≠ 0) (x : F)
    (hx : 2 * ∑ i ∈ Finset.range (P.natDegree + 1),
      |P.coeff i / P.leadingCoeff| < |x|) :
    SignType.sign (P.eval x) =
    SignType.sign (P.leadingCoeff * x ^ P.natDegree) := by
  set p := P.natDegree with hp_def
  set ap := P.leadingCoeff with hap_def
  set L := ap * x ^ p with hL_def
  have hap_ne : ap ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hx_pos : 0 < |x| := by
    have h1 : (0 : F) ≤ 2 * ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap| := by positivity
    linarith
  have hx_ne : x ≠ 0 := fun h => by simp [h] at hx_pos
  have hL_ne : L ≠ 0 := mul_ne_zero hap_ne (pow_ne_zero _ hx_ne)
  -- Apply sign_eq_of_abs_sub_lt: suffices |P.eval x - L| < |L|
  apply sign_eq_of_abs_sub_lt hL_ne
  -- Rewrite the difference as the tail sum
  rw [eval_sub_lead]
  -- Split on p = 0 (trivial) vs p ≥ 1
  by_cases hp : p = 0
  · -- Constant polynomial: tail sum is empty, |0| < |L|
    rw [show P.natDegree = 0 from hp ▸ hp_def.symm]
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
    exact abs_pos.mpr hL_ne
  · -- Degree p ≥ 1
    have hp_pos : 0 < p := Nat.pos_of_ne_zero hp
    have h1le : 1 ≤ |x| := by
      have h_ap_term : |P.coeff p / ap| = 1 := by
        rw [show P.coeff p = ap from rfl, div_self hap_ne, abs_one]
      have h_sum_ge : 1 ≤ ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap| := by
        calc (1:F) = |P.coeff p / ap| := h_ap_term.symm
          _ ≤ ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap| :=
              Finset.single_le_sum (fun i _ => abs_nonneg (P.coeff i / ap))
                (show p ∈ Finset.range (p + 1) by simp)
      linarith [mul_le_mul_of_nonneg_left h_sum_ge (by positivity : (0:F) ≤ 2)]
    have hsum_lt : ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap| < |x| / 2 := by
      rw [lt_div_iff₀ (two_pos (α := F))]; linarith
    -- Main inequality chain
    calc |∑ i ∈ Finset.range p, P.coeff i * x ^ i|
        ≤ ∑ i ∈ Finset.range p, |P.coeff i * x ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range p, |P.coeff i| * |x| ^ i := by
          congr 1; ext i; rw [abs_mul, abs_pow]
      _ ≤ ∑ i ∈ Finset.range p, |P.coeff i| * |x| ^ (p - 1) := by
          apply Finset.sum_le_sum; intro i hi
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ h1le (Nat.le_pred_of_lt (Finset.mem_range.mp hi)))
            (abs_nonneg _)
      _ = (∑ i ∈ Finset.range p, |P.coeff i|) * |x| ^ (p - 1) :=
          (Finset.sum_mul ..).symm
      _ ≤ (∑ i ∈ Finset.range (p + 1), |P.coeff i|) * |x| ^ (p - 1) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (by omega)) (fun i _ _ => abs_nonneg _)
      _ = (|ap| * ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap|) * |x| ^ (p - 1) := by
          congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
          rw [abs_div]; exact (mul_div_cancel₀ _ (abs_ne_zero.mpr hap_ne)).symm
      _ < (|ap| * (|x| / 2)) * |x| ^ (p - 1) := by
          apply mul_lt_mul_of_pos_right _ (pow_pos hx_pos _)
          exact mul_lt_mul_of_pos_left hsum_lt (abs_pos.mpr hap_ne)
      _ = |ap| * (|x| ^ (p - 1) * |x|) / 2 := by ring
      _ = |ap| * |x| ^ p / 2 := by
          congr 2; rw [← pow_succ]; congr 1; omega
      _ < |ap| * |x| ^ p := by
          linarith [mul_pos (abs_pos.mpr hap_ne) (pow_pos hx_pos p)]
      _ = |L| := by rw [abs_mul, abs_pow]

end Azurite.BPR
