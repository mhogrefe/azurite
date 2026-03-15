import Mathlib.Data.Rat.Defs
import Azurite.Rat.LogBase2

namespace Azurite.Rat

/-- Reverses an ordering. -/
def reverseOrdering : Ordering → Ordering
  | Ordering.lt => Ordering.gt
  | Ordering.eq => Ordering.eq
  | Ordering.gt => Ordering.lt

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

end Azurite.Rat
