import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_b_c

/-!
# BPR Proposition 2.20: Constant Sign on a Non-Vanishing Interval

**Proposition 2.20 (BPR).** Let R be a real closed field, `P ∈ R[X]` such that P
does not vanish in `(a, b)`. Then P has constant sign in the interval `(a, b)`.

The proof assumes R is an ordered field with the intermediate value property
(which holds for real closed fields by Theorem 2.11, via `R[i]` algebraically closed).
-/

namespace Azurite.BPR.Proposition2_20

open Polynomial Azurite.BPR Azurite.BPR.Theorem2_11

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Proposition 2.20.** Over an ordered field `R` with the intermediate
    value property, if `P ∈ R[X]` does not vanish on `(a, b)`, then `P` has
    constant sign on `(a, b)`: it is either everywhere positive or everywhere
    negative on the open interval.

    If `(a, b) = ∅` (i.e. `a ≥ b`) both disjuncts hold vacuously. -/
theorem proposition_2_20 (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (a b : R)
    (hP : ∀ x ∈ Set.Ioo a b, P.eval x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 < P.eval x) ∨ (∀ x ∈ Set.Ioo a b, P.eval x < 0) := by
  -- Suppose, for contradiction, that neither disjunct holds. Pick a point
  -- `y ∈ (a, b)` with `P y ≤ 0` (so `P y < 0` by non-vanishing) and
  -- `z ∈ (a, b)` with `P z ≥ 0` (so `P z > 0`); IVP on the sub-interval
  -- between them produces a root, contradicting `hP`.
  by_contra hne
  push Not at hne
  obtain ⟨⟨y, hy_ab, hy_nonpos⟩, ⟨z, hz_ab, hz_nonneg⟩⟩ := hne
  have hPy_ne : P.eval y ≠ 0 := hP y hy_ab
  have hPz_ne : P.eval z ≠ 0 := hP z hz_ab
  have hPy_neg : P.eval y < 0 := lt_of_le_of_ne hy_nonpos hPy_ne
  have hPz_pos : 0 < P.eval z := lt_of_le_of_ne hz_nonneg (Ne.symm hPz_ne)
  -- Whichever of `y, z` comes first, `P` takes values of opposite sign at the
  -- two endpoints, so IVP produces a root in the open sub-interval ⊆ `(a, b)`.
  have key : ∀ {u v : R}, u ∈ Set.Ioo a b → v ∈ Set.Ioo a b →
      u < v → P.eval u * P.eval v < 0 → False := by
    intro u v hu hv huv hsign
    obtain ⟨w, hwu, hwv, hPw⟩ := hIVP P u v huv hsign
    have hw_ab : w ∈ Set.Ioo a b :=
      ⟨lt_trans hu.1 hwu, lt_trans hwv hv.2⟩
    exact hP w hw_ab hPw
  -- `y ≠ z` since `P(y) < 0 < P(z)`; dispatch both orderings.
  rcases lt_trichotomy y z with hyz | hyz | hyz
  · exact key hy_ab hz_ab hyz (mul_neg_of_neg_of_pos hPy_neg hPz_pos)
  · exact absurd (hyz ▸ hPy_neg : P.eval z < 0) (not_lt.mpr (le_of_lt hPz_pos))
  · exact key hz_ab hy_ab hyz (mul_neg_of_pos_of_neg hPz_pos hPy_neg)

/-- **BPR Proposition 2.20** (real closed form). Over a real closed field `R`,
    if `P ∈ R[X]` does not vanish on `(a, b)`, then `P` has constant sign on
    `(a, b)`. -/
theorem proposition_2_20_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) (a b : R) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    (∀ x ∈ Set.Ioo a b, P.eval x ≠ 0) →
    (∀ x ∈ Set.Ioo a b, 0 < P.eval x) ∨ (∀ x ∈ Set.Ioo a b, P.eval x < 0) := by
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  have : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact proposition_2_20 theorem_2_11_b_c P a b

end Azurite.BPR.Proposition2_20
