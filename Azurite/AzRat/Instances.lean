import Azurite.AzRat.Equiv.Construct
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Div
import Azurite.AzRat.Equiv.Order
import Azurite.AzRat.Equiv.Sub

/-!
# Algebraic instances for `AzRat`

`AzRat` is a linearly ordered field: this file assembles the `Field` and
`IsStrictOrderedRing` instances (which, together with the verified
`LinearOrder` from `Azurite/AzRat/Equiv/Order.lean`, give the full linearly
ordered field API) on top of the computational operations defined earlier.
Every law is transported from `ℚ` through the injection `toRat` and the
`toRat_*` commutation theorems — no new computation is introduced, and all
data fields are the existing verified operations.

The casts are computable and limb-level: `NatCast`/`IntCast` go through
`AzNat.ofNat`/`AzInt.ofInt` and `toAzRat`, and `RatCast` is `ofRat`.

With the additive group structure in place, Mathlib's lattice absolute
value `|·|` becomes available, and it agrees with the constant-time
`AzRat.abs` (`abs_eq`).
-/

namespace Azurite.AzRat

instance : NatCast AzRat := ⟨fun n => (AzNat.ofNat n).toAzRat⟩

@[simp] theorem toRat_natCast (n : ℕ) : toRat (n : AzRat) = n := by
  show toRat (AzNat.ofNat n).toAzRat = _
  rw [toRat_toAzRat, AzNat.toNat_ofNat]

instance : IntCast AzRat := ⟨fun z => (AzInt.ofInt z).toAzRat⟩

@[simp] theorem toRat_intCast (z : ℤ) : toRat (z : AzRat) = z := by
  show toRat (AzInt.ofInt z).toAzRat = _
  rw [toRat_toAzRat_int, AzInt.toInt_ofInt]

instance : RatCast AzRat := ⟨ofRat⟩

@[simp] theorem toRat_ratCast (q : ℚ) : toRat (q : AzRat) = q := toRat_ofRat q

instance : NNRatCast AzRat := ⟨fun q => ofRat q⟩

@[simp] theorem toRat_nnratCast (q : ℚ≥0) : toRat (q : AzRat) = q := toRat_ofRat q

instance : Nontrivial AzRat := ⟨0, 1, fun h => by
  have : (0 : ℚ) = 1 := by rw [← toRat_zero, ← toRat_one, h]
  exact absurd this (by norm_num)⟩

instance : Field AzRat where
  add_assoc a b c := toRat_injective (by simp only [toRat_add]; ring)
  zero_add a := toRat_injective (by simp)
  add_zero a := toRat_injective (by simp)
  add_comm a b := toRat_injective (by simp only [toRat_add]; ring)
  mul_assoc a b c := toRat_injective (by simp only [toRat_mul]; ring)
  one_mul a := toRat_injective (by simp)
  mul_one a := toRat_injective (by simp)
  left_distrib a b c := toRat_injective (by simp only [toRat_add, toRat_mul]; ring)
  right_distrib a b c := toRat_injective (by simp only [toRat_add, toRat_mul]; ring)
  zero_mul a := toRat_injective (by simp)
  mul_zero a := toRat_injective (by simp)
  mul_comm a b := toRat_injective (by simp only [toRat_mul]; ring)
  neg_add_cancel a := toRat_injective (by simp)
  sub_eq_add_neg := AzRat.sub_eq_add_neg
  div_eq_mul_inv := AzRat.div_eq_mul_inv
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast_zero := toRat_injective (by simp)
  natCast_succ n := toRat_injective (by simp)
  intCast_ofNat n := toRat_injective (by simp)
  intCast_negSucc n := toRat_injective (by simp [Int.cast_negSucc])
  mul_inv_cancel a ha := toRat_injective (by
    rw [toRat_mul, toRat_inv, toRat_one]
    exact mul_inv_cancel₀ fun h => ha (toRat_injective (h.trans toRat_zero.symm)))
  inv_zero := toRat_injective (by simp)
  nnqsmul q a := (q : AzRat) * a
  qsmul q a := (q : AzRat) * a
  nnratCast_def q := toRat_injective (by
    simp only [toRat_nnratCast, toRat_div, toRat_natCast]
    exact NNRat.cast_def q)
  ratCast_def q := toRat_injective (by
    simp only [toRat_ratCast, toRat_div, toRat_intCast, toRat_natCast]
    exact (Rat.num_div_den q).symm)

instance : IsStrictOrderedRing AzRat :=
  Function.Injective.isStrictOrderedRing toRat toRat_zero toRat_one toRat_add
    toRat_mul (fun {a b} => (le_iff_toRat_le a b).symm)
    (fun {a b} => (lt_iff_toRat_lt a b).symm)

/-- The constant-time `AzRat.abs` (a sign-bit flip) is the lattice absolute
value `|·|` that the new additive group structure makes available. Stated
with `AzRat.abs` on the left so that `simp` normalizes to the `|·|`
notation, where Mathlib's `abs_*` lemmas apply. -/
@[simp] theorem abs_eq (q : AzRat) : q.abs = |q| := by
  rw [AzRat.abs_eq_max_neg, _root_.abs_eq_max_neg]

/-- `toRat_abs` (`Azurite/AzRat/Equiv/Unary.lean`, where `|·|` is not yet
available on the `AzRat` side) restated in the `|·|` normal form. -/
@[simp] theorem toRat_abs' (q : AzRat) : toRat |q| = |toRat q| := by
  rw [← abs_eq, toRat_abs]

/-- `ofRat_abs` restated in the `|·|` normal form. -/
@[simp] theorem ofRat_abs' (r : ℚ) : ofRat |r| = |ofRat r| := by
  rw [ofRat_abs, abs_eq]

end Azurite.AzRat

namespace Azurite

-- Sanity checks: numeric literals, field operations, and `|·|` all compute
-- (string-anchored via `AzRat.toString`).

#guard ((2 : AzRat) + 3).toString == "5"
#guard ((1 : AzRat) / 3 - 1 / 2).toString == "-1/6"
#guard ((-6 : AzRat) * (2 / 3)).toString == "-4"
#guard ((2 / 3 : AzRat) ^ 2).toString == "4/9"
#guard (((3 / 4 : ℚ) : AzRat)).toString == "3/4"
#guard ((-22 : ℤ) : AzRat).toString == "-22"
#guard (|(-5 : AzRat) / 2|).toString == "5/2"

end Azurite
