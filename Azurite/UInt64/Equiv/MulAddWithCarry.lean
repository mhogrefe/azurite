import Azurite.UInt64.MulAddWithCarry
import Azurite.UInt64.Equiv.MulWithCarry

namespace UInt64

private lemma mulAddWithCarry_aux (hi lo acc : UInt64)
    (hN : hi.toNat * 2^64 + lo.toNat ≤ (2^64 - 1) * 2^64) :
    (if lo + acc < lo then hi + 1 else hi).toNat * 2^64 + (lo + acc).toNat
      = hi.toNat * 2^64 + lo.toNat + acc.toNat := by
  have hacc := _root_.UInt64.toNat_lt acc
  have hlo_lt := _root_.UInt64.toNat_lt lo
  have hhi_lt := _root_.UInt64.toNat_lt hi
  have hhi_le : hi.toNat ≤ 2^64 - 1 := by
    by_contra h
    have hge : hi.toNat ≥ 2^64 := by omega
    have : 2^64 * 2^64 ≤ hi.toNat * 2^64 := Nat.mul_le_mul_right _ hge
    omega
  have h_one : (1 : UInt64).toNat = 1 := rfl
  have h_add_lo : (lo + acc).toNat = (lo.toNat + acc.toNat) % 2^64 :=
    _root_.UInt64.toNat_add lo acc
  have h_add_hi : (hi + 1).toNat = (hi.toNat + 1) % 2^64 :=
    _root_.UInt64.toNat_add hi 1
  have h_cmp : (lo + acc < lo) ↔ lo.toNat + acc.toNat ≥ 2^64 := by
    rw [_root_.UInt64.lt_iff_toNat_lt, h_add_lo]; omega
  by_cases hcarry : lo + acc < lo
  · rw [if_pos hcarry]
    have hge : lo.toNat + acc.toNat ≥ 2^64 := h_cmp.mp hcarry
    have hlo' : (lo + acc).toNat = lo.toNat + acc.toNat - 2^64 := by
      rw [h_add_lo, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    -- When carry fires, hi < 2^64 - 1 (else a*b+c+acc would exceed 2^128 - 1).
    have hhi_strict : hi.toNat < 2^64 - 1 := by
      by_contra h
      have hhi_eq : hi.toNat = 2^64 - 1 := by omega
      have hlo_eq : lo.toNat = 0 := by
        rw [hhi_eq] at hN
        have : (2^64 - 1) * 2^64 + lo.toNat ≤ (2^64 - 1) * 2^64 := hN
        omega
      omega
    have hhi' : (hi + 1).toNat = hi.toNat + 1 := by
      rw [h_add_hi, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg hcarry]
    have hlt : lo.toNat + acc.toNat < 2^64 := by
      by_contra h; exact hcarry (h_cmp.mpr (Nat.not_lt.mp h))
    rw [h_add_lo, Nat.mod_eq_of_lt hlt]; ring

theorem mulAddWithCarry_eq (a b acc c : UInt64) :
    (mulAddWithCarry a b acc c).1.toNat * 2^64 + (mulAddWithCarry a b acc c).2.toNat
      = a.toNat * b.toNat + acc.toNat + c.toNat := by
  unfold mulAddWithCarry
  dsimp
  rw [add_ite_zero]
  have hmwc : (mulWithCarry a b c).1.toNat * 2^64 + (mulWithCarry a b c).2.toNat
      = a.toNat * b.toNat + c.toNat := mulWithCarry_eq a b c
  have ha := _root_.UInt64.toNat_lt a
  have hb := _root_.UInt64.toNat_lt b
  have hc := _root_.UInt64.toNat_lt c
  have hab : a.toNat * b.toNat ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hbd : (mulWithCarry a b c).1.toNat * 2^64 + (mulWithCarry a b c).2.toNat
      ≤ (2^64 - 1) * 2^64 := by
    rw [hmwc]
    have : (2^64 - 1) * (2^64 - 1) + (2^64 - 1) = (2^64 - 1) * 2^64 := by ring
    omega
  have key := mulAddWithCarry_aux (mulWithCarry a b c).1 (mulWithCarry a b c).2 acc hbd
  linarith [key, hmwc]

end UInt64
