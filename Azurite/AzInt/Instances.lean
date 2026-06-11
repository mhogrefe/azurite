import Azurite.AzInt.Equiv.Mul
import Azurite.AzInt.Equiv.Sub
import Azurite.AzInt.Equiv.Pow

namespace Azurite.AzInt

private theorem toInt_injective {a b : AzInt} (h : a.toInt = b.toInt) : a = b := by
  rw [← ofInt_toInt a, ← ofInt_toInt b, h]

-- Computable casts: `NatCast` goes limb-level through `AzNat.ofNat` and
-- `IntCast` is `ofInt` (the defaults `Nat.unaryCast` / `Int.castDef` would
-- build the value by `n` additions of `1`). Declared before the `CommRing`
-- instance so its `NatCast`/`IntCast` parents pick them up.

instance : NatCast AzInt := ⟨fun n => (AzNat.ofNat n).toAzInt⟩

@[simp] theorem toInt_natCast (n : ℕ) : (n : AzInt).toInt = n := by
  show ((AzNat.ofNat n).toNat : ℤ) = (n : ℤ)
  rw [AzNat.toNat_ofNat]

instance : IntCast AzInt := ⟨ofInt⟩

@[simp] theorem toInt_intCast (i : ℤ) : (i : AzInt).toInt = i := toInt_ofInt i

instance : CommRing AzInt where
  add_assoc a b c := toInt_injective (by simp [toInt_add, Int.add_assoc])
  zero_add a := toInt_injective (by simp [toInt_add])
  add_zero a := toInt_injective (by simp [toInt_add])
  add_comm a b := toInt_injective (by simp [toInt_add, Int.add_comm])
  mul_assoc a b c := toInt_injective (by simp [toInt_mul, Int.mul_assoc])
  one_mul a := toInt_injective (by simp [toInt_mul])
  mul_one a := toInt_injective (by simp [toInt_mul])
  left_distrib a b c := toInt_injective (by simp [toInt_add, toInt_mul]; ring)
  right_distrib a b c := toInt_injective (by simp [toInt_add, toInt_mul]; ring)
  zero_mul a := toInt_injective (by simp [toInt_mul])
  mul_zero a := toInt_injective (by simp [toInt_mul])
  mul_comm a b := toInt_injective (by simp [toInt_mul, Int.mul_comm])
  neg_add_cancel a := toInt_injective (by simp [toInt_add, toInt_neg])
  sub_eq_add_neg a b := toInt_injective (by simp [toInt_sub, toInt_add, toInt_neg]; ring)
  natCast_zero := toInt_injective (by simp)
  natCast_succ n := toInt_injective (by simp [toInt_add])
  intCast_ofNat n := toInt_injective (by simp)
  intCast_negSucc n := toInt_injective (by simp [toInt_neg, Int.negSucc_eq])
  -- `n • z` / `i • z` are one cast plus one multiplication (the default
  -- `nsmulRec`/`zsmulRec` would be `n` additions).
  nsmul n z := (n : AzInt) * z
  nsmul_zero z := toInt_injective (by simp [toInt_mul])
  nsmul_succ n z := toInt_injective (by simp [toInt_add, toInt_mul]; ring)
  zsmul i z := (i : AzInt) * z
  zsmul_zero' z := toInt_injective (by simp [toInt_mul])
  zsmul_succ' n z := toInt_injective (by simp [toInt_add, toInt_mul]; ring)
  zsmul_neg' n z := toInt_injective (by
    simp [toInt_mul, toInt_neg, Int.negSucc_eq]; ring)
  -- Exponentiation `z ^ n` runs `AzInt.pow` (magnitude delegated to `AzNat`'s sliding-window
  -- power), so it is `O(log n)` multiplications rather than the default `O(n)`, and
  -- `z.pow n = z ^ n` definitionally. The `npow_succ` obligation is discharged through `toInt`
  -- via `toInt_pow` (which does not need the `Ring` structure that is still being built).
  npow n z := z.pow n
  npow_zero z := toInt_injective (by rw [toInt_pow, pow_zero, toInt_one])
  npow_succ n z := toInt_injective (by rw [toInt_mul, toInt_pow, toInt_pow, pow_succ])

instance : Nontrivial AzInt := ⟨0, 1, fun h => by
  have : (0 : Int) = 1 := by rw [← toInt_zero, ← toInt_one, h]
  exact absurd this (by decide)⟩

instance : NoZeroDivisors AzInt where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have h' : a.toInt * b.toInt = 0 := by rw [← toInt_mul, h]; rfl
    rcases mul_eq_zero.mp h' with ha | hb
    · left; exact toInt_injective (by rw [ha]; rfl)
    · right; exact toInt_injective (by rw [hb]; rfl)

instance : IsDomain AzInt := {}

end Azurite.AzInt
