import Azurite.AzRat.LogBase2
import Azurite.AzNat.Compare
import Azurite.AzNat.Mul

/-!
# Fast comparison for `AzRat`

`AzRat.cmp x y` compares two rationals with a staged, limb-level algorithm: magnitude comparisons
use `AzNat.compare`, the bit-length screen uses `AzRat.floorLogBase2Abs`, and the final
fallback cross-multiplies with `AzNat` multiplication. The stages, in order, short-circuit on:

1. sign (negative `<` zero `<` positive);
2. whether `|·|` is `< 1`, `= 1`, or `> 1`;
3. equality of numerator and denominator magnitudes;
4. numerator-vs-denominator magnitude comparison pointing the same way;
5. `⌊log₂ |·|⌋`;
6. cross-multiplication `num x · den y` vs `den x · num y`.

For negative operands the magnitude orderings are reversed via `Ordering.swap`.
-/

namespace Azurite.AzRat

/-- The sign of `x` as an `Ordering` relative to `0`: `lt` if negative, `eq` if zero,
`gt` if positive. -/
def signOrd (x : AzRat) : Ordering :=
  if x.num = 0 then Ordering.eq
  else if x.sign then Ordering.gt else Ordering.lt

/-- Fast computable comparison for `AzRat`. -/
def cmp (x y : AzRat) : Ordering :=
  -- First check signs.
  let x_sign := signOrd x
  let y_sign := signOrd y
  let sign_cmp := compare x_sign y_sign

  if sign_cmp ≠ Ordering.eq ∨ x_sign == Ordering.eq then
    sign_cmp
  else
    let is_pos := x_sign == Ordering.gt
    -- Both numbers have the same strict sign and are non-zero.

    -- Then check if one is < 1 and the other is > 1.
    let x_cmp_one := AzNat.compare x.num x.den
    let y_cmp_one := AzNat.compare y.num y.den
    let one_cmp := compare x_cmp_one y_cmp_one

    if one_cmp ≠ Ordering.eq then
      if is_pos then one_cmp else one_cmp.swap
    else
      -- Then compare numerators and denominators.
      let n_cmp := AzNat.compare x.num y.num
      let d_cmp := AzNat.compare x.den y.den

      if n_cmp == Ordering.eq ∧ d_cmp == Ordering.eq then
        Ordering.eq
      else
        let nd_cmp := compare n_cmp d_cmp
        if nd_cmp ≠ Ordering.eq then
          if is_pos then nd_cmp else nd_cmp.swap
        else
          -- Then compare floor ∘ log_2 ∘ abs.
          let log_cmp := compare (floorLogBase2Abs x) (floorLogBase2Abs y)
          if log_cmp ≠ Ordering.eq then
            if is_pos then log_cmp else log_cmp.swap
          else
            -- Finally, cross-multiply.
            let prod_cmp := AzNat.compare (x.num * y.den) (x.den * y.num)
            if is_pos then prod_cmp else prod_cmp.swap

/-! ### Order instances

`cmp` backs the standard order structure, mirroring `AzInt`: `≤` and `<` are
defined by the comparison result, so deciding an inequality runs the staged
limb-level algorithm above (never `ℚ` arithmetic). The `LinearOrder` instance
itself lives in `Azurite/AzRat/Equiv/Order.lean`, where the order laws are
transferred from `ℚ` via `cmp_eq_compare`. -/

instance : Ord AzRat := ⟨cmp⟩

instance : LE AzRat where
  le q r := cmp q r ≠ Ordering.gt

instance : LT AzRat where
  lt q r := cmp q r = Ordering.lt

instance : DecidableRel (α := AzRat) (· ≤ ·) :=
  fun q r => if h : cmp q r ≠ Ordering.gt then isTrue h else isFalse h

instance : DecidableRel (α := AzRat) (· < ·) :=
  fun q r => if h : cmp q r = Ordering.lt then isTrue h else isFalse h

instance : Max AzRat where
  max q r := if q ≤ r then r else q

instance : Min AzRat where
  min q r := if q ≤ r then q else r

end Azurite.AzRat
