import Mathlib.Data.Nat.Bitwise
import Azurite.UInt64.WideAdd

namespace UInt64

/-- Correctness of `wideAdd`: the returned `(hi, lo)` pair represents the sum of the
two 128-bit inputs modulo `2^128`. -/
theorem toNat_wideAdd (x y : UInt64 × UInt64) :
    (wideAdd x y).1.toNat * 2 ^ 64 + (wideAdd x y).2.toNat
      = (x.1.toNat * 2 ^ 64 + x.2.toNat + (y.1.toNat * 2 ^ 64 + y.2.toNat)) % 2 ^ 128 := by
  unfold wideAdd
  set X1 : ℕ := x.1.toNat
  set X0 : ℕ := x.2.toNat
  set Y1 : ℕ := y.1.toNat
  set Y0 : ℕ := y.2.toNat
  have hX1 : X1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hX0 : X0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY1 : Y1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY0 : Y0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hlo_toNat : (x.2 + y.2).toNat = (X0 + Y0) % 2 ^ 64 :=
    _root_.UInt64.toNat_add _ _
  -- Bridge the UInt64 carry to a Nat carry.
  have hcarry_toNat :
      (if x.2 + y.2 < x.2 then (1 : UInt64) else 0).toNat
        = (if 2 ^ 64 ≤ X0 + Y0 then 1 else 0) := by
    by_cases h : 2 ^ 64 ≤ X0 + Y0
    · have hlt : x.2 + y.2 < x.2 := by
        rw [_root_.UInt64.lt_iff_toNat_lt, hlo_toNat]
        have hmod : (X0 + Y0) % 2 ^ 64 = X0 + Y0 - 2 ^ 64 := by omega
        rw [hmod]; omega
      rw [ite_eq_left hlt, ite_eq_left h]; rfl
    · have hsum_lt : X0 + Y0 < 2 ^ 64 := by push Not at h; exact h
      have hlo_eq : (x.2 + y.2).toNat = X0 + Y0 := by
        rw [hlo_toNat, Nat.mod_eq_of_lt hsum_lt]
      have hnlt : ¬ x.2 + y.2 < x.2 := by
        rw [_root_.UInt64.lt_iff_toNat_lt, hlo_eq]; omega
      rw [ite_eq_right hnlt, ite_eq_right h]; rfl
  rw [_root_.UInt64.toNat_add, _root_.UInt64.toNat_add, hlo_toNat, hcarry_toNat]
  set cN : ℕ := if 2 ^ 64 ≤ X0 + Y0 then 1 else 0 with hcN_def
  have hcN_le : cN ≤ 1 := by rw [hcN_def]; split <;> omega
  show ((X1 + Y1) % 2 ^ 64 + cN) % 2 ^ 64 * 2 ^ 64 + (X0 + Y0) % 2 ^ 64
      = (X1 * 2 ^ 64 + X0 + (Y1 * 2 ^ 64 + Y0)) % 2 ^ 128
  rw [hcN_def]
  split
  all_goals (rename_i hcase; omega)

end UInt64
