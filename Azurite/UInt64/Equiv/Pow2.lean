import Mathlib.Data.Nat.Bitwise
import Azurite.UInt64.Pow2
import Azurite.UInt64.Equiv.Basic

namespace UInt64

private lemma and_sub_one_eq_zero_iff (u : UInt64) (hu : u ≠ 0) :
    u &&& (u - 1) = 0 ↔ u.toNat.isPowerOfTwo := by
  have hu_nat : u.toNat ≠ 0 := by
    intro h
    apply hu
    apply _root_.UInt64.eq_of_toNat_eq
    rw [h]
    rfl
  rw [← Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hu_nat]
  have huint_iff : u &&& (u - 1) = 0 ↔ (u &&& (u - 1)).toNat = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h
      apply _root_.UInt64.eq_of_toNat_eq
      exact h
  rw [huint_iff, _root_.UInt64.toNat_and, _root_.UInt64.toNat_sub,
      show ((1 : UInt64).toNat) = 1 from rfl]
  have hu_lt : u.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hu_ge : 1 ≤ u.toNat := Nat.one_le_iff_ne_zero.mpr hu_nat
  have heq : (2 ^ 64 - 1 + u.toNat) % 2 ^ 64 = u.toNat - 1 := by omega
  rw [heq]

theorem isPowerOfTwo_iff (u : UInt64) :
    u.isPowerOfTwo = true ↔ u.toNat.isPowerOfTwo := by
  unfold isPowerOfTwo
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  by_cases hu : u = 0
  · subst hu
    simp only [not_true_eq_false, false_and, false_iff]
    rintro ⟨k, hk⟩
    have := Nat.two_pow_pos k
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [h0] at hk
    omega
  · rw [and_sub_one_eq_zero_iff u hu]
    simp [hu]

end UInt64
