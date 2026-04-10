import Mathlib.Data.Nat.Bitwise
import Azurite.UInt64.ClearBit

namespace UInt64

theorem toNat_clearBit (u : UInt64) (i : Nat) (hi : i < 64) :
    (u.clearBit i).toNat = u.toNat &&& (2 ^ 64 - 1 - 2 ^ i) := by
  unfold clearBit
  rw [if_pos hi]
  rw [_root_.UInt64.toNat_and, _root_.UInt64.toNat_not, _root_.UInt64.toNat_shiftLeft,
      show ((1 : UInt64).toNat = 1) from rfl]
  have hi_eq : (_root_.UInt64.ofNat i).toNat = i := by
    show i % 2 ^ 64 = i
    exact Nat.mod_eq_of_lt (by omega)
  rw [hi_eq, Nat.mod_eq_of_lt hi]
  have hpow : (1 : Nat) <<< i < 2 ^ 64 := by
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by omega) hi
  rw [Nat.mod_eq_of_lt hpow, Nat.one_shiftLeft]
  rfl

theorem clearBit_of_ge (u : UInt64) (i : Nat) (hi : 64 ≤ i) : u.clearBit i = u := by
  unfold clearBit
  rw [if_neg (by omega)]

end UInt64
