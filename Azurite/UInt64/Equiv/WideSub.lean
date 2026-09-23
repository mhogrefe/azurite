import Mathlib.Data.Nat.Bitwise
import Azurite.UInt64.WideSub

namespace UInt64

/-- Correctness of `wideSub`: the returned `(hi, lo)` pair represents the difference of
the two 128-bit inputs modulo `2^128`. -/
theorem toNat_wideSub (x y : UInt64 × UInt64) :
    (wideSub x y).1.toNat * 2 ^ 64 + (wideSub x y).2.toNat
      = (2 ^ 128 - (y.1.toNat * 2 ^ 64 + y.2.toNat) + (x.1.toNat * 2 ^ 64 + x.2.toNat))
          % 2 ^ 128 := by
  unfold wideSub
  set X1 : ℕ := x.1.toNat
  set X0 : ℕ := x.2.toNat
  set Y1 : ℕ := y.1.toNat
  set Y0 : ℕ := y.2.toNat
  have hX1 : X1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hX0 : X0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY1 : Y1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY0 : Y0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hlo_toNat : (x.2 - y.2).toNat = (2 ^ 64 - Y0 + X0) % 2 ^ 64 :=
    _root_.UInt64.toNat_sub _ _
  -- Bridge the UInt64 borrow to a Nat borrow.
  have hborrow_toNat :
      (if x.2 < y.2 then (1 : UInt64) else 0).toNat
        = (if X0 < Y0 then 1 else 0) := by
    by_cases h : X0 < Y0
    · have hlt : x.2 < y.2 := by
        rw [_root_.UInt64.lt_iff_toNat_lt]; exact h
      rw [ite_eq_left hlt, ite_eq_left h]; rfl
    · have hnlt : ¬ x.2 < y.2 := by
        rw [_root_.UInt64.lt_iff_toNat_lt]; exact h
      rw [ite_eq_right hnlt, ite_eq_right h]; rfl
  have hhi_inner : (x.1 - y.1).toNat = (2 ^ 64 - Y1 + X1) % 2 ^ 64 :=
    _root_.UInt64.toNat_sub _ _
  rw [_root_.UInt64.toNat_sub, hhi_inner, hborrow_toNat, hlo_toNat]
  set bN : ℕ := if X0 < Y0 then 1 else 0 with hbN_def
  have hbN_le : bN ≤ 1 := by rw [hbN_def]; split <;> omega
  show (2 ^ 64 - bN + (2 ^ 64 - Y1 + X1) % 2 ^ 64) % 2 ^ 64 * 2 ^ 64
      + (2 ^ 64 - Y0 + X0) % 2 ^ 64
      = (2 ^ 128 - (Y1 * 2 ^ 64 + Y0) + (X1 * 2 ^ 64 + X0)) % 2 ^ 128
  rw [hbN_def]
  split
  all_goals (rename_i hcase; omega)

end UInt64
