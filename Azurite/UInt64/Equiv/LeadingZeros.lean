import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Set
import Azurite.UInt64.LeadingZeros
import Azurite.UInt64.Equiv.Basic

namespace UInt64

/-- Shifting a nonzero `d : UInt64` left by `leadingZeros d` bits brings it into
    the normalized range `[2^63, 2^64)`. -/
theorem two_pow_63_le_toNat_shiftLeft_leadingZeros (d : UInt64) (hd : d ≠ 0) :
    2 ^ 63 ≤ (d <<< _root_.UInt64.ofNat (leadingZeros d)).toNat := by
  have hd_nat_ne : d.toNat ≠ 0 := fun h => hd (_root_.UInt64.eq_of_toNat_eq (h.trans rfl))
  have hd_lt : d.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hL_lt_64 : d.toNat.log2 < 64 := (Nat.log2_lt hd_nat_ne).mpr hd_lt
  have hL_le_63 : d.toNat.log2 ≤ 63 := by omega
  set L := d.toNat.log2 with hL_def
  have hk_def : leadingZeros d = 63 - L := by
    show (if d = 0 then 64 else 63 - d.toNat.log2) = 63 - L
    rw [if_neg hd]
  set k := leadingZeros d with hk_eq
  have hk_le : k ≤ 63 := by rw [hk_def]; exact Nat.sub_le _ _
  have hLk : L + k = 63 := by rw [hk_def]; omega
  have hpow_le : 2 ^ L ≤ d.toNat := Nat.log2_self_le hd_nat_ne
  have hpow_hi : d.toNat < 2 ^ (L + 1) :=
    (Nat.log2_lt hd_nat_ne).mp (Nat.lt_succ_of_le (Nat.le_refl _))
  have h_ofNat_k : (_root_.UInt64.ofNat k).toNat = k := by
    show k % 2 ^ 64 = k; exact Nat.mod_eq_of_lt (by omega)
  have h_k_mod : k % 64 = k := Nat.mod_eq_of_lt (by omega)
  have h_prod_lt : d.toNat * 2 ^ k < 2 ^ 64 := by
    calc d.toNat * 2 ^ k
        < 2 ^ (L + 1) * 2 ^ k :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hpow_hi
      _ = 2 ^ (L + 1 + k) := (Nat.pow_add 2 (L + 1) k).symm
      _ = 2 ^ 64 := by congr 1; omega
  have h_eq : (d <<< _root_.UInt64.ofNat k).toNat = d.toNat * 2 ^ k := by
    rw [_root_.UInt64.toNat_shiftLeft, h_ofNat_k, h_k_mod, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt h_prod_lt]
  rw [h_eq]
  calc 2 ^ 63 = 2 ^ (L + k) := by rw [hLk]
    _ = 2 ^ L * 2 ^ k := Nat.pow_add 2 L k
    _ ≤ d.toNat * 2 ^ k := Nat.mul_le_mul_right _ hpow_le

end UInt64
