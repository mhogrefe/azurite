import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Azurite.Rat.LogBase2

namespace Azurite.Rat

/-- Reverses an ordering. -/
def reverseOrdering : Ordering → Ordering
  | Ordering.lt => Ordering.gt
  | Ordering.eq => Ordering.eq
  | Ordering.gt => Ordering.lt

@[simp] lemma reverseOrdering_lt : reverseOrdering Ordering.lt = Ordering.gt := rfl
@[simp] lemma reverseOrdering_eq : reverseOrdering Ordering.eq = Ordering.eq := rfl
@[simp] lemma reverseOrdering_gt : reverseOrdering Ordering.gt = Ordering.lt := rfl

-- All 9 combinations of compare on Ordering values. These are needed because
-- `simp` and `simp_all` cannot reduce `compare Ordering.x Ordering.y` on their own.
@[simp] lemma compare_ordering_lt_lt : compare Ordering.lt Ordering.lt = Ordering.eq := by decide
@[simp] lemma compare_ordering_lt_eq : compare Ordering.lt Ordering.eq = Ordering.lt := by decide
@[simp] lemma compare_ordering_lt_gt : compare Ordering.lt Ordering.gt = Ordering.lt := by decide
@[simp] lemma compare_ordering_eq_lt : compare Ordering.eq Ordering.lt = Ordering.gt := by decide
@[simp] lemma compare_ordering_eq_eq : compare Ordering.eq Ordering.eq = Ordering.eq := by decide
@[simp] lemma compare_ordering_eq_gt : compare Ordering.eq Ordering.gt = Ordering.lt := by decide
@[simp] lemma compare_ordering_gt_lt : compare Ordering.gt Ordering.lt = Ordering.gt := by decide
@[simp] lemma compare_ordering_gt_eq : compare Ordering.gt Ordering.eq = Ordering.gt := by decide
@[simp] lemma compare_ordering_gt_gt : compare Ordering.gt Ordering.gt = Ordering.eq := by decide

-- Link `compare x.num 0` to the rational sign of `x`.
lemma compare_num_zero_neg (x : ℚ) (h : x < 0) : compare x.num 0 = Ordering.lt :=
  compare_lt_iff_lt.mpr (Rat.num_neg.mpr h)
lemma compare_num_zero_zero : compare (0 : ℚ).num 0 = Ordering.eq := by decide
lemma compare_num_zero_pos (x : ℚ) (h : 0 < x) : compare x.num 0 = Ordering.gt :=
  compare_gt_iff_gt.mpr (Rat.num_pos.mpr h)
/-- `Mathlib.Tactic.Ring.instOrdRat_mathlib` (from the Ring tactic) and
`Rat.linearOrder.toOrd` are both valid `Ord ℚ` instances. They agree everywhere;
this lemma lets us move between them in proofs. -/
lemma ring_ord_eq_linear_ord (x y : ℚ) :
    @compare ℚ Mathlib.Tactic.Ring.instOrdRat_mathlib x y =
    @compare ℚ Rat.linearOrder.toOrd x y := by
  show (if x ≤ y then if y ≤ x then Ordering.eq else Ordering.lt else Ordering.gt) =
       compareOfLessAndEq x y
  unfold compareOfLessAndEq
  rcases lt_trichotomy x y with h | rfl | h
  · simp [le_of_lt h, not_le.mpr h]
  · simp
  · simp [h.ne', le_of_lt h, not_le.mpr h]

/-- Fast computable comparison for rational numbers using bit sizes and logarithmic bounds. -/
def cmp (x y : ℚ) : Ordering :=
  -- First check signs
  let x_sign := compare x.num 0
  let y_sign := compare y.num 0
  let sign_cmp := compare x_sign y_sign

  if sign_cmp ≠ Ordering.eq ∨ x_sign == Ordering.eq then
    sign_cmp
  else
    let is_pos := x_sign == Ordering.gt
    -- Both numbers have the same strict sign and are non-zero.

    -- Then check if one is < 1 and the other is > 1
    let x_cmp_one := compare x.num.natAbs x.den
    let y_cmp_one := compare y.num.natAbs y.den
    let one_cmp := compare x_cmp_one y_cmp_one

    if one_cmp ≠ Ordering.eq then
      if is_pos then one_cmp else reverseOrdering one_cmp
    else
      -- Then compare numerators and denominators
      let n_cmp := compare x.num.natAbs y.num.natAbs
      let d_cmp := compare x.den y.den

      if n_cmp == Ordering.eq ∧ d_cmp == Ordering.eq then
        Ordering.eq
      else
        let nd_cmp := compare n_cmp d_cmp
        if nd_cmp ≠ Ordering.eq then
          if is_pos then nd_cmp else reverseOrdering nd_cmp
        else
          -- Then compare floor ∘ log_2 ∘ abs
          let log_cmp := compare (floorLogBase2Abs x) (floorLogBase2Abs y)
          if log_cmp ≠ Ordering.eq then
            if is_pos then log_cmp else reverseOrdering log_cmp
          else
            -- Finally, cross-multiply.
            let prod_cmp := compare (x.num.natAbs * y.den) (x.den * y.num.natAbs)
            if is_pos then prod_cmp else reverseOrdering prod_cmp

lemma cmp_sign_cmp_ne_eq (x y : ℚ)
    (h_ne : compare (compare x.num 0) (compare y.num 0) ≠ Ordering.eq) :
    cmp x y = compare (compare x.num 0) (compare y.num 0) := by
  unfold cmp
  dsimp
  rw [if_pos]
  · left
    exact h_ne

-- Stage 1: the sign_cmp value is correct (equals compare x y) at the stage-1 exit.
-- Covers both the differing-signs case and the x = 0 case.
lemma sign_cmp_correct (x y : ℚ)
    (h : compare x.num 0 ≠ compare y.num 0 ∨ x = 0) :
    compare (compare x.num 0) (compare y.num 0) = compare x y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · -- x < 0, y < 0: both have sign lt, so h reduces to x = 0, contradicting x < 0
    rw [compare_num_zero_neg _ hx, compare_num_zero_neg _ hy] at h
    simp at h; exact absurd h hx.ne
  · -- x < 0, y = 0
    rw [compare_num_zero_neg _ hx, compare_num_zero_zero, ring_ord_eq_linear_ord]
    exact (compare_lt_iff_lt.mpr hx).symm
  · -- x < 0, y > 0
    rw [compare_num_zero_neg _ hx, compare_num_zero_pos _ hy, ring_ord_eq_linear_ord]
    exact (compare_lt_iff_lt.mpr (hx.trans hy)).symm
  · -- x = 0, y < 0
    rw [compare_num_zero_zero, compare_num_zero_neg _ hy, ring_ord_eq_linear_ord]
    exact (compare_gt_iff_gt.mpr hy).symm
  · simp
  · -- x = 0, y > 0
    rw [compare_num_zero_zero, compare_num_zero_pos _ hy, ring_ord_eq_linear_ord]
    exact (compare_lt_iff_lt.mpr hy).symm
  · -- x > 0, y < 0
    rw [compare_num_zero_pos _ hx, compare_num_zero_neg _ hy, ring_ord_eq_linear_ord]
    exact (compare_gt_iff_gt.mpr (hy.trans hx)).symm
  · -- x > 0, y = 0
    rw [compare_num_zero_pos _ hx, compare_num_zero_zero, ring_ord_eq_linear_ord]
    exact (compare_gt_iff_gt.mpr hx).symm
  · -- x > 0, y > 0: both have sign gt, so h reduces to x = 0, contradicting x > 0
    rw [compare_num_zero_pos _ hx, compare_num_zero_pos _ hy] at h
    simp at h; exact absurd h (ne_of_gt hx)

-- Stage 2: when both x and y have the same nonzero sign and their |·| vs 1
-- bracket differs, cmp gives the correct answer.
-- (x_cmp_one = compare x.num.natAbs x.den encodes whether |x| < 1, = 1, or > 1.)
lemma cmp_one_cmp_ne_eq (x y : ℚ)
    (h_sign_eq : compare x.num 0 = compare y.num 0)
    (h_nz : x.num ≠ 0)
    (h_one_ne : compare (compare x.num.natAbs x.den) (compare y.num.natAbs y.den) ≠ Ordering.eq) :
    cmp x y = compare x y := by
  sorry

-- Stage 3: when n_cmp = eq and d_cmp = eq (same nonzero sign), x and y are equal.
-- (natAbs equal + same sign ⇒ num equal; den equal ⇒ x = y as reduced fractions.)
lemma eq_of_same_sign_natAbs_den (x y : ℚ)
    (h_sign_eq : compare x.num 0 = compare y.num 0)
    (h_nz : x.num ≠ 0)
    (h_num : x.num.natAbs = y.num.natAbs)
    (h_den : x.den = y.den) :
    x = y := by
  sorry

-- Stage 4: when nd_cmp ≠ eq (numerator comparison and denominator comparison
-- point in opposite directions), cmp gives the correct answer.
lemma cmp_nd_cmp_ne_eq (x y : ℚ)
    (h_sign_eq : compare x.num 0 = compare y.num 0)
    (h_nz : x.num ≠ 0)
    (h_one_eq : compare (compare x.num.natAbs x.den) (compare y.num.natAbs y.den) = Ordering.eq)
    (h_not_both_eq : ¬(x.num.natAbs = y.num.natAbs ∧ x.den = y.den))
    (h_nd_ne : compare (compare x.num.natAbs y.num.natAbs) (compare x.den y.den) ≠ Ordering.eq) :
    cmp x y = compare x y := by
  sorry

-- Stage 5: when log_cmp ≠ eq, cmp gives the correct answer.
-- (Uses floorLogBase2Abs_lt_imp_abs_lt to convert log order to absolute value order.)
lemma cmp_log_cmp_ne_eq (x y : ℚ)
    (h_sign_eq : compare x.num 0 = compare y.num 0)
    (h_nz : x.num ≠ 0)
    (h_one_eq : compare (compare x.num.natAbs x.den) (compare y.num.natAbs y.den) = Ordering.eq)
    (h_not_both_eq : ¬(x.num.natAbs = y.num.natAbs ∧ x.den = y.den))
    (h_nd_eq : compare (compare x.num.natAbs y.num.natAbs) (compare x.den y.den) = Ordering.eq)
    (h_log_ne : compare (floorLogBase2Abs x) (floorLogBase2Abs y) ≠ Ordering.eq) :
    cmp x y = compare x y := by
  sorry

-- Stage 6 (helper): the cross-multiply comparison is always the exact comparison of
-- absolute values. (Both den fields are positive by the Rat invariant.)
lemma cross_mul_eq_compare_abs (x y : ℚ) :
    compare (x.num.natAbs * y.den) (x.den * y.num.natAbs) = compare |x| |y| := by
  sorry

-- Main theorem: cmp agrees with the standard ordered-field comparison everywhere.
theorem cmp_eq_compare (x y : ℚ) : cmp x y = compare x y := by
  sorry

end Azurite.Rat
