import Mathlib.Data.Nat.Bitwise
import Azurite.UInt64.TestBit
import Azurite.UInt64.Equiv.Basic

namespace UInt64

theorem testBit_eq_toNat_testBit (u : UInt64) (i : Nat) :
    u.testBit i = u.toNat.testBit i := by
  unfold testBit
  split
  · rename_i hi
    have hshift : ((u >>> _root_.UInt64.ofNat i) &&& 1).toNat = u.toNat / 2 ^ i % 2 := by
      rw [_root_.UInt64.toNat_and, _root_.UInt64.toNat_shiftRight,
          show ((1 : UInt64).toNat = 1) from rfl, Nat.and_one_is_mod]
      have hi_eq : (_root_.UInt64.ofNat i).toNat = i := by
        show i % 2 ^ 64 = i
        exact Nat.mod_eq_of_lt (by omega)
      rw [hi_eq, Nat.mod_eq_of_lt hi, Nat.shiftRight_eq_div_pow]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hmod_lt : u.toNat / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases hb : (u >>> _root_.UInt64.ofNat i) &&& 1 = 0
    · have h0 : ((u >>> _root_.UInt64.ofNat i) &&& 1).toNat = 0 := by rw [hb]; rfl
      rw [hshift] at h0
      simp [hb]
      omega
    · have hne : ((u >>> _root_.UInt64.ofNat i) &&& 1).toNat ≠ 0 := by
        intro h
        apply hb
        apply _root_.UInt64.eq_of_toNat_eq
        rw [h]
        rfl
      rw [hshift] at hne
      have heq1 : u.toNat / 2 ^ i % 2 = 1 := by omega
      simp [hb, heq1]
  · rename_i hi
    symm
    apply Nat.testBit_eq_false_of_lt
    have hu_lt : u.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
    exact lt_of_lt_of_le hu_lt (Nat.pow_le_pow_right (by omega) (by omega))

end UInt64
