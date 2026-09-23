import Mathlib.Data.Nat.Bitwise
import Azurite.UInt64.SetBit

namespace UInt64

theorem toNat_setBit (u : UInt64) (i : Nat) (hi : i < 64) :
    (u.setBit i).toNat = u.toNat ||| (1 <<< i) := by
  unfold setBit
  rw [ite_eq_left hi]
  rw [_root_.UInt64.toNat_or, _root_.UInt64.toNat_shiftLeft,
      show ((1 : UInt64).toNat = 1) from rfl]
  have hi_eq : (_root_.UInt64.ofNat i).toNat = i := by
    show i % 2 ^ 64 = i
    exact Nat.mod_eq_of_lt (by omega)
  rw [hi_eq, Nat.mod_eq_of_lt hi]
  have hpow : (1 : Nat) <<< i < 2 ^ 64 := by
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by omega) hi
  rw [Nat.mod_eq_of_lt hpow]

theorem setBit_of_ge (u : UInt64) (i : Nat) (hi : 64 ≤ i) : u.setBit i = u := by
  unfold setBit
  rw [ite_eq_right (by omega)]

end UInt64
