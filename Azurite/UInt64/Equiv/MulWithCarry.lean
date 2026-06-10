import Azurite.UInt64.MulWithCarry
import Azurite.UInt64.Equiv.WideMul

namespace UInt64

private lemma mulWithCarry_aux (hi lo c : UInt64)
    (hN : hi.toNat * 2^64 + lo.toNat ≤ (2^64 - 1) * (2^64 - 1)) :
    (if lo + c < lo then hi + 1 else hi).toNat * 2^64 + (lo + c).toNat
      = hi.toNat * 2^64 + lo.toNat + c.toNat := by
  have hc := _root_.UInt64.toNat_lt c
  have hlo_lt := _root_.UInt64.toNat_lt lo
  have hhi_lt := _root_.UInt64.toNat_lt hi
  have hhi_le : hi.toNat ≤ 2^64 - 2 := by
    by_contra h
    have hge : hi.toNat ≥ 2^64 - 1 := by omega
    have hmul : (2^64 - 1) * 2^64 ≤ hi.toNat * 2^64 := Nat.mul_le_mul_right _ hge
    have h1 : ((2^64 - 1) * 2^64 : Nat) = (2^64 - 1) * (2^64 - 1) + (2^64 - 1) := by
      rw [Nat.mul_sub_one]; omega
    omega
  have h_one : (1 : UInt64).toNat = 1 := rfl
  have h_add_lo : (lo + c).toNat = (lo.toNat + c.toNat) % 2^64 :=
    _root_.UInt64.toNat_add lo c
  have h_add_hi : (hi + 1).toNat = (hi.toNat + 1) % 2^64 :=
    _root_.UInt64.toNat_add hi 1
  have h_cmp : (lo + c < lo) ↔ lo.toNat + c.toNat ≥ 2^64 := by
    rw [_root_.UInt64.lt_iff_toNat_lt, h_add_lo]; omega
  by_cases hcarry : lo + c < lo
  · rw [if_pos hcarry]
    have hge : lo.toNat + c.toNat ≥ 2^64 := h_cmp.mp hcarry
    have hlo' : (lo + c).toNat = lo.toNat + c.toNat - 2^64 := by
      rw [h_add_lo, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    have hhi' : (hi + 1).toNat = hi.toNat + 1 := by
      rw [h_add_hi, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg hcarry]
    have hlt : lo.toNat + c.toNat < 2^64 := by
      by_contra h; exact hcarry (h_cmp.mpr (Nat.not_lt.mp h))
    rw [h_add_lo, Nat.mod_eq_of_lt hlt]; ring

theorem mulWithCarry_eq (a b c : UInt64) :
    (mulWithCarry a b c).1.toNat * 2^64 + (mulWithCarry a b c).2.toNat
      = a.toNat * b.toNat + c.toNat := by
  have hwm : (wideMul a b).1.toNat * 2^64 + (wideMul a b).2.toNat = a.toNat * b.toNat :=
    toNat_wideMul a b
  have ha := _root_.UInt64.toNat_lt a
  have hb := _root_.UInt64.toNat_lt b
  have hab : a.toNat * b.toNat ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hbd : (wideMul a b).1.toNat * 2^64 + (wideMul a b).2.toNat ≤
      (2^64 - 1) * (2^64 - 1) := by rw [hwm]; exact hab
  have key := mulWithCarry_aux (wideMul a b).1 (wideMul a b).2 c hbd
  show ((wideMul a b).1 +
        (if (wideMul a b).2 + c < (wideMul a b).2 then 1 else 0)).toNat * 2^64
      + ((wideMul a b).2 + c).toNat = a.toNat * b.toNat + c.toNat
  rw [add_ite_zero, key, hwm]

end UInt64
