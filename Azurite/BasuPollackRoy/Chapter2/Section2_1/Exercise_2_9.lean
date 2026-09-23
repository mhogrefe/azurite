import Azurite.BasuPollackRoy.Chapter2.Section2_1.IsRealClosedOrder

/-! # BPR Section 2.1 — Exercise 2.9: Quadratic constant-sign criterion

> In a real closed field `R`, a degree-2 polynomial `P = a x² + b x + c` with
> `a ≠ 0` has constant non-zero sign on `R` (i.e.\ is everywhere strictly
> positive or everywhere strictly negative) iff its discriminant `b² − 4ac`
> is negative.

**Proof sketch (BPR).** The completing-the-square identity
`4a · P(x) = (2 a x + b)² − (b² − 4ac)`, valid over any commutative ring,
is the engine. Since `(2 a x + b)² ≥ 0` for every `x`:

* If `b² − 4ac < 0`, then `4a · P(x) > 0` for every `x`. Dividing by `4a`
  preserves the sign when `a > 0` and flips it when `a < 0`, so `P` has
  constant non-zero sign.
* Conversely, if `b² − 4ac ≥ 0`, the discriminant has a square root `s ∈ R`
  by `IsRealClosed.exists_eq_pow_of_nonneg`, and `x₀ := (−b + s)/(2a)` is a
  root of `P` (a direct calculation). A root rules out constant non-zero
  sign.
-/

namespace Azurite.BPR

/-- **BPR Exercise 2.9.** In a real closed field `R`, a second-degree polynomial
    `P = aX² + bX + c` with `a ≠ 0` has constant non-zero sign (i.e. is everywhere
    positive or everywhere negative) if and only if its discriminant `b² − 4ac`
    is negative.

    **Proof.** Completing the square gives
    `4a · P(x) = (2ax + b)² − (b² − 4ac)`,
    the classical identity valid over any ring.

    **(⇐)** If `b² − 4ac < 0` then `4a · P(x) > 0` for all `x` since
    `(2ax + b)² ≥ 0`. Dividing by `4a` preserves the sign if `a > 0` and flips it
    if `a < 0`, so `P` has constant non-zero sign.

    **(⇒)** By contraposition: if `b² − 4ac ≥ 0` then in a real closed field we
    may write `b² − 4ac = s²` for some `s ∈ R` (by `IsRealClosed.exists_eq_pow_of_nonneg`),
    and `x₀ = (−b + s) / (2a)` is a root of `P` (a direct calculation using the
    completing-the-square identity). A root witnesses that `P` does not have
    constant non-zero sign. -/
theorem exercise_2_9 {R : Type*} [Field R] [IsRealClosed R]
    {a b c : R} (ha : a ≠ 0) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    ((∀ x : R, 0 < a * x ^ 2 + b * x + c) ∨
     (∀ x : R, a * x ^ 2 + b * x + c < 0)) ↔
      b ^ 2 - 4 * a * c < 0 := by
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  -- Key completing-the-square identity.
  have key : ∀ x : R, 4 * a * (a * x ^ 2 + b * x + c) =
      (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) := fun x => by ring
  constructor
  · -- Forward: constant non-zero sign ⇒ discriminant < 0 (by contraposition).
    intro hsign
    by_contra hdisc
    push Not at hdisc
    -- Extract a square root of the discriminant in the real closed field.
    obtain ⟨s, hs⟩ := IsRealClosed.exists_eq_pow_of_nonneg hdisc two_ne_zero
    -- Candidate root: x₀ = (-b + s) / (2a).
    have h2a : (2 * a : R) ≠ 0 := mul_ne_zero two_ne_zero ha
    have h4a : (4 * a : R) ≠ 0 := mul_ne_zero (by norm_num) ha
    set x₀ : R := (-b + s) / (2 * a) with hx₀_def
    -- Then 2a·x₀ + b = s, so 4a·P(x₀) = s² − (b² − 4ac) = 0.
    have h2ax₀b : 2 * a * x₀ + b = s := by
      rw [hx₀_def]; field_simp; ring
    have hPx₀ : a * x₀ ^ 2 + b * x₀ + c = 0 := by
      have h4aP : 4 * a * (a * x₀ ^ 2 + b * x₀ + c) = 0 := by
        rw [key, h2ax₀b, ← hs]; ring
      exact (mul_eq_zero.mp h4aP).resolve_left h4a
    -- A root contradicts constant non-zero sign at x₀.
    rcases hsign with hpos | hneg
    · exact absurd (hpos x₀) (by rw [hPx₀]; exact lt_irrefl 0)
    · exact absurd (hneg x₀) (by rw [hPx₀]; exact lt_irrefl 0)
  · -- Backward: discriminant < 0 ⇒ constant non-zero sign.
    intro hdisc
    -- In either sign of `a`, show 4a·P(x) has the same (strict) sign as `a`.
    have h4aP_pos_of_a_pos : 0 < a → ∀ x : R, 0 < 4 * a * (a * x ^ 2 + b * x + c) := by
      intro hap x
      rw [key]
      have : 0 ≤ (2 * a * x + b) ^ 2 := sq_nonneg _
      linarith
    have h4aP_pos_of_a_neg : a < 0 → ∀ x : R, 0 < 4 * a * (a * x ^ 2 + b * x + c) := by
      intro han x
      rw [key]
      have : 0 ≤ (2 * a * x + b) ^ 2 := sq_nonneg _
      linarith
    rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
    · -- a < 0 ⇒ 4a < 0, so P(x) < 0.
      right
      intro x
      have h4a_neg : 4 * a < 0 := by
        have : (0 : R) < 4 := by norm_num
        exact mul_neg_of_pos_of_neg this ha_neg
      have hP_pos := h4aP_pos_of_a_neg ha_neg x
      -- 4a · P(x) > 0 with 4a < 0 forces P(x) < 0.
      by_contra hPge
      push Not at hPge
      have : 4 * a * (a * x ^ 2 + b * x + c) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt h4a_neg) hPge
      linarith
    · -- a > 0 ⇒ 4a > 0, so P(x) > 0.
      left
      intro x
      have h4a_pos : 0 < 4 * a := by
        have : (0 : R) < 4 := by norm_num
        exact mul_pos this ha_pos
      have hP_pos := h4aP_pos_of_a_pos ha_pos x
      exact (mul_pos_iff_of_pos_left h4a_pos).mp hP_pos

end Azurite.BPR
