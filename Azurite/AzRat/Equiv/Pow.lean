import Azurite.AzRat.Pow
import Azurite.AzRat.Equiv.Unary
import Azurite.AzNat.Equiv.Pow

/-!
# Equivalence of `AzRat` exponentiation with `ℚ` exponentiation

`AzRat.pow` (componentwise sliding-window powers, no reduction) agrees with
`ℚ` exponentiation under `toRat`: the magnitude side reuses
`AzNat.toNat_pow`, and the sign side is a case split on `q.sign` and the
parity of `n` (an even exponent makes the result nonnegative), exactly as
in `AzInt.toInt_pow`.

For integer exponents, the key fact is structural: although a negative
exponent is implemented directly (numerator and denominator roles swapped,
no intermediate reciprocal), `q.zpow (-(n+1)) = (q.pow (n+1))⁻¹` holds by
unfolding (`zpow_negSucc`) — the reciprocal of a reduced fraction is the
swap. `toRat_zpow` then chains `toRat_pow` with the reciprocal theorem.
-/

namespace Azurite.AzRat

@[simp] theorem toRat_pow (q : AzRat) (n : ℕ) : toRat (q.pow n) = toRat q ^ n := by
  rw [toRat_eq_divInt, toRat_eq_divInt q]
  have hsign : (q.pow n).sign = (q.sign || (n % 2 == 0)) := rfl
  have hnum : ((q.pow n).num.toNat : ℤ) = (q.num.toNat : ℤ) ^ n := by
    show ((q.num.pow n).toNat : ℤ) = _
    rw [AzNat.toNat_pow]; push_cast; ring
  have hden : ((q.pow n).den.toNat : ℤ) = (q.den.toNat : ℤ) ^ n := by
    show ((q.den.pow n).toNat : ℤ) = _
    rw [AzNat.toNat_pow]; push_cast; ring
  rw [hsign, hnum, hden]
  cases hs : q.sign
  · -- negative base: the sign of the power depends on the parity of `n`
    rcases Nat.even_or_odd n with he | ho
    · rw [show (false || (n % 2 == 0)) = true by simp [Nat.even_iff.mp he],
        ite_eq_left rfl, ite_eq_right Bool.false_ne_true,
        Rat.divInt_eq_div, Rat.divInt_eq_div, div_pow]
      push_cast [Even.neg_pow he]; ring
    · rw [show (false || (n % 2 == 0)) = false by simp [Nat.odd_iff.mp ho],
        ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        Rat.divInt_eq_div, Rat.divInt_eq_div, div_pow]
      push_cast [Odd.neg_pow ho]; ring
  · -- nonnegative base: the power is nonnegative
    rw [show (true || (n % 2 == 0)) = true from rfl, ite_eq_left rfl, ite_eq_left rfl,
      Rat.divInt_eq_div, Rat.divInt_eq_div, div_pow]
    push_cast; ring

@[simp] theorem ofRat_pow (r : ℚ) (n : ℕ) : (ofRat r).pow n = ofRat (r ^ n) :=
  toRat_injective (by rw [toRat_pow, toRat_ofRat, toRat_ofRat])

/-- `AzRat.zpow` at a negative exponent is the reciprocal of the positive
power, structurally: the direct implementation swaps the numerator and
denominator roles, which is exactly `inv` of the componentwise power, so
the equality holds by unfolding — no `toRat`-level reasoning needed. -/
theorem zpow_negSucc (q : AzRat) (n : ℕ) :
    q.zpow (Int.negSucc n) = (q.pow (n + 1))⁻¹ := by
  show q.zpow (Int.negSucc n) = AzRat.inv (q.pow (n + 1))
  by_cases h : q.num = 0
  · have hp : (q.pow (n + 1)).num = 0 := by
      show q.num.pow (n + 1) = 0
      rw [h]
      exact AzNat.toNat_injective (by
        rw [AzNat.toNat_pow, AzNat.toNat_zero, Nat.zero_pow (Nat.succ_pos n)])
    simp only [AzRat.zpow]
    rw [dite_eq_left h, AzRat.inv, dite_eq_left hp]
  · have hp : (q.pow (n + 1)).num ≠ 0 := fun h0 => by
      have h1 := congrArg AzNat.toNat (show q.num.pow (n + 1) = 0 from h0)
      rw [AzNat.toNat_pow, AzNat.toNat_zero] at h1
      exact h (AzNat.toNat_injective (by
        rw [(Nat.pow_eq_zero.mp h1).1, AzNat.toNat_zero]))
    simp only [AzRat.zpow]
    rw [dite_eq_right h, AzRat.inv, dite_eq_right hp]
    rfl

@[simp] theorem toRat_zpow (q : AzRat) (z : ℤ) : toRat (q.zpow z) = toRat q ^ z := by
  cases z with
  | ofNat n =>
    show toRat (q.pow n) = _
    rw [toRat_pow, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n =>
    rw [zpow_negSucc, toRat_inv, toRat_pow, _root_.zpow_negSucc]

@[simp] theorem ofRat_zpow (r : ℚ) (z : ℤ) : (ofRat r).zpow z = ofRat (r ^ z) :=
  toRat_injective (by rw [toRat_zpow, toRat_ofRat, toRat_ofRat])

end Azurite.AzRat
