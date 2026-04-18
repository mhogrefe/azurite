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

private lemma testBit_compl64 (i j : Nat) (hi : i < 64) (hj : j < 64) :
    Nat.testBit (2 ^ 64 - 1 - 2 ^ i) j = !decide (i = j) := by
  have h_k_lt_64 : 2 ^ i < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hi
  have h_k_one : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have h_k1_eq : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; omega
  have h_k1_le : 2 ^ (i + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  have h_decomp :
      2 ^ 64 - 1 - 2 ^ i = 2 ^ (i + 1) * (2 ^ (63 - i) - 1) + (2 ^ i - 1) := by
    have h_pow_64 : 2 ^ (i + 1) * 2 ^ (63 - i) = 2 ^ 64 := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.mul_sub_one, h_pow_64]
    omega
  rw [h_decomp]
  have hy : 2 ^ i - 1 < 2 ^ (i + 1) := by omega
  rw [Nat.testBit_two_pow_mul_add _ hy, Nat.testBit_two_pow_sub_one,
      Nat.testBit_two_pow_sub_one]
  by_cases h_ij : i = j
  · subst h_ij; simp
  · rw [decide_eq_false h_ij, Bool.not_false]
    split
    · rename_i h_jsub; rw [decide_eq_true_eq]; omega
    · rename_i h_jsub; rw [decide_eq_true_eq]; omega

theorem testBit_toNat_clearBit (u : UInt64) (i j : Nat) :
    (u.clearBit i).toNat.testBit j = (u.toNat.testBit j && !decide (i = j)) := by
  by_cases hj : j < 64
  · by_cases hi : i < 64
    · rw [UInt64.toNat_clearBit u i hi, Nat.testBit_and]
      congr 1
      exact testBit_compl64 i j hi hj
    · push Not at hi
      rw [UInt64.clearBit_of_ge u i hi]
      have h_ij : i ≠ j := by omega
      rw [decide_eq_false h_ij, Bool.not_false, Bool.and_true]
  · push Not at hj
    have hu_testBit : u.toNat.testBit j = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (UInt64.toNat_lt u)
        (Nat.pow_le_pow_right (by omega) hj))
    have hcu_testBit : (u.clearBit i).toNat.testBit j = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (UInt64.toNat_lt _)
        (Nat.pow_le_pow_right (by omega) hj))
    rw [hu_testBit, hcu_testBit, Bool.false_and]

end UInt64
