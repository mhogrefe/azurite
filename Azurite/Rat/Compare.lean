import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Cast.Lemmas
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

-- Helpers for the |·| vs 1 comparison stage.

/-- The numerator of `|x|` equals `x.num.natAbs` (as an integer). -/
lemma rat_abs_num (x : ℚ) : (|x|).num = x.num.natAbs := by
  rw [Rat.abs_def, Rat.divInt_eq_div]
  exact Rat.num_div_eq_of_coprime (by exact_mod_cast Rat.pos x)
      (by rw [Int.natAbs_natCast, Int.natAbs_natCast]; exact x.reduced)

/-- `|x| < 1` if and only if the numerator absolute value is less than the denominator. -/
lemma abs_lt_one_iff (x : ℚ) : |x| < 1 ↔ x.num.natAbs < x.den := by
  rw [← Rat.num_lt_denom_iff, rat_abs_num, Rat.den_abs_eq_den]; exact_mod_cast Iff.rfl

/-- `compare x.num.natAbs x.den` equals `compare |x| 1`. -/
lemma compare_natAbs_den_eq (x : ℚ) :
    compare x.num.natAbs x.den = compare |x| (1 : ℚ) := by
  rw [ring_ord_eq_linear_ord]
  rcases Nat.lt_trichotomy x.num.natAbs x.den with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr ((abs_lt_one_iff x).mpr h)]
  · have h4 : (|x|).num = (|x|.den : ℤ) := by
      rw [rat_abs_num, Rat.den_abs_eq_den]; exact_mod_cast h
    have hab : |x| = 1 := by
      conv_lhs => rw [← Rat.num_div_den |x|]; rw [h4]
      push_cast
      apply div_self
      rw [Rat.den_abs_eq_den]; exact_mod_cast (Rat.pos x).ne'
    rw [h]; simp [compare_eq_iff_eq.mpr hab]
  · have hge : 1 ≤ |x| := not_lt.mp ((abs_lt_one_iff x).not.mpr (Nat.not_lt.mpr h.le))
    have hgt : (|x|.den : ℤ) < (|x|).num := by
      rw [rat_abs_num, Rat.den_abs_eq_den]; exact_mod_cast h
    have hne1 : |x| ≠ 1 := by intro heq; rw [heq] at hgt; simp at hgt
    rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (lt_of_le_of_ne hge hne1.symm)]

-- Helper: when x and y are on different sides of 1 (Rat.linearOrder.toOrd),
-- comparing (compare x 1) with (compare y 1) gives the same result as comparing x with y.
private lemma pos_one_cmp_eq_cmp (x y : ℚ)
    (h_ne : @compare Ordering instOrdOrdering
              (@compare ℚ Rat.linearOrder.toOrd x 1)
              (@compare ℚ Rat.linearOrder.toOrd y 1) ≠ Ordering.eq) :
    @compare Ordering instOrdOrdering
      (@compare ℚ Rat.linearOrder.toOrd x 1)
      (@compare ℚ Rat.linearOrder.toOrd y 1) =
    @compare ℚ Rat.linearOrder.toOrd x y := by
  rcases lt_trichotomy x 1 with hx | rfl | hx <;>
  rcases lt_trichotomy y 1 with hy | rfl | hy
  · simp [compare_lt_iff_lt.mpr hx, compare_lt_iff_lt.mpr hy] at h_ne
  · simp [compare_lt_iff_lt.mpr hx]
  · rw [compare_lt_iff_lt.mpr hx, compare_gt_iff_gt.mpr hy]
    simp [compare_lt_iff_lt.mpr (hx.trans hy)]
  · simp [compare_lt_iff_lt.mpr hy, compare_gt_iff_gt.mpr hy]
  · simp at h_ne
  · simp [compare_gt_iff_gt.mpr hy, compare_lt_iff_lt.mpr hy]
  · rw [compare_gt_iff_gt.mpr hx, compare_lt_iff_lt.mpr hy]
    simp [compare_gt_iff_gt.mpr (hy.trans hx)]
  · simp [compare_gt_iff_gt.mpr hx]
  · simp [compare_gt_iff_gt.mpr hx, compare_gt_iff_gt.mpr hy] at h_ne

-- Stage 2: when both x and y have the same nonzero sign and their |·| vs 1
-- bracket differs, cmp gives the correct answer.
-- (x_cmp_one = compare x.num.natAbs x.den encodes whether |x| < 1, = 1, or > 1.)
lemma cmp_one_cmp_ne_eq (x y : ℚ)
    (h_sign_eq : compare x.num 0 = compare y.num 0)
    (h_nz : x.num ≠ 0)
    (h_one_ne : compare (compare x.num.natAbs x.den) (compare y.num.natAbs y.den) ≠ Ordering.eq) :
    cmp x y = compare x y := by
  have h_sign_cmp : compare (compare x.num 0) (compare y.num 0) = Ordering.eq := by
    rw [h_sign_eq]; rcases compare y.num 0 with _ | _ | _ <;> simp
  -- stage-1 doesn't exit (sign_cmp = eq, x_sign ≠ eq)
  unfold cmp
  rw [if_neg (by push_neg; exact ⟨by rw [h_sign_cmp], by simpa using h_nz⟩)]
  -- rewrite natAbs comparisons as |·| vs 1
  rw [compare_natAbs_den_eq x, compare_natAbs_den_eq y] at h_one_ne ⊢
  rw [if_pos h_one_ne]
  -- case split: positive or negative
  have hx_ne_zero : x ≠ 0 := fun h => by rw [h] at h_nz; simp at h_nz
  rcases lt_or_gt_of_ne hx_ne_zero with hx | hx
  · -- x < 0: y < 0 (same sign); is_pos = false; return reverseOrdering one_cmp
    have hy : y < 0 := Rat.num_neg.mp (compare_lt_iff_lt.mp
      (h_sign_eq.symm.trans (compare_num_zero_neg _ hx)))
    rw [compare_num_zero_neg _ hx, abs_of_neg hx, abs_of_neg hy]
    rw [abs_of_neg hx, abs_of_neg hy] at h_one_ne
    rw [show compare x y = @compare ℚ Rat.linearOrder.toOrd x y from ring_ord_eq_linear_ord x y]
    conv_lhs => rw [ring_ord_eq_linear_ord, ring_ord_eq_linear_ord]
    have h_ne' : @compare Ordering instOrdOrdering
        (@compare ℚ Rat.linearOrder.toOrd (-x) 1)
        (@compare ℚ Rat.linearOrder.toOrd (-y) 1) ≠ Ordering.eq := by
      rwa [ring_ord_eq_linear_ord, ring_ord_eq_linear_ord] at h_one_ne
    rw [pos_one_cmp_eq_cmp _ _ h_ne']
    -- reverseOrdering (compare (-x) (-y)) = compare x y
    rw [show @compare ℚ Rat.linearOrder.toOrd (-x) (-y) =
            reverseOrdering (@compare ℚ Rat.linearOrder.toOrd x y) from by
      rcases lt_trichotomy x y with h | rfl | h
      · simp [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr (neg_lt_neg h)]
      · simp
      · simp [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr (neg_lt_neg h)]]
    rcases (@compare ℚ Rat.linearOrder.toOrd x y) with _ | _ | _ <;> simp
  · -- x > 0: y > 0 (same sign); is_pos = true; return one_cmp
    have hy : 0 < y := Rat.num_pos.mp (compare_gt_iff_gt.mp
      (h_sign_eq.symm.trans (compare_num_zero_pos _ hx)))
    rw [compare_num_zero_pos _ hx, abs_of_pos hx, abs_of_pos hy]
    rw [abs_of_pos hx, abs_of_pos hy] at h_one_ne
    rw [show compare x y = @compare ℚ Rat.linearOrder.toOrd x y from ring_ord_eq_linear_ord x y]
    conv_lhs => rw [ring_ord_eq_linear_ord, ring_ord_eq_linear_ord]
    exact pos_one_cmp_eq_cmp _ _
      (by rwa [ring_ord_eq_linear_ord, ring_ord_eq_linear_ord] at h_one_ne)

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
