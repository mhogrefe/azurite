import Mathlib.Data.Nat.Basic
import Azurite.UInt64.SubWithBorrow

namespace UInt64

theorem subWithBorrow_zero_eq (a b : UInt64) :
  (subWithBorrow a b false).1.toNat + b.toNat + 0 =
    a.toNat + (if (subWithBorrow a b false).2 then 1 else 0) * 2^64 := by
  unfold subWithBorrow
  dsimp
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have he1 : (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2^64 := UInt64.toNat_sub a b
  have hl1 : decide (a < b) = true ↔ a.toNat < b.toNat := by
    rw [decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  by_cases h : a < b <;> simp [h] at * <;> omega

theorem subWithBorrow_one_eq (a b : UInt64) :
  (subWithBorrow a b true).1.toNat + b.toNat + 1 =
    a.toNat + (if (subWithBorrow a b true).2 then 1 else 0) * 2^64 := by
  unfold subWithBorrow
  dsimp
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have he1 : (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2^64 := UInt64.toNat_sub a b
  have he2 : (a - b - 1).toNat = (2 ^ 64 - (1 : UInt64).toNat + (a - b).toNat) % 2^64 :=
    UInt64.toNat_sub (a - b) 1
  have h_one : (1 : UInt64).toNat = 1 := rfl

  have hl1 : decide (a < b) = true ↔ a.toNat < b.toNat := by
    rw [decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  have hl2 : decide (a - b < 1) = true ↔ (a - b).toNat < 1 := by
    rw [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, h_one]

  by_cases h1 : a < b <;> by_cases h2 : a - b < 1 <;>
    simp [h1, h2, h_one] at * <;> omega

theorem subWithBorrow_eq (a b : UInt64) (c : Bool) :
  (subWithBorrow a b c).1.toNat + b.toNat + (if c then 1 else 0) =
    a.toNat + (if (subWithBorrow a b c).2 then 1 else 0) * 2^64 := by
  cases c
  · have h0 : (if false = true then 1 else 0 : Nat) = 0 := rfl
    rw [h0]
    apply subWithBorrow_zero_eq
  · have h1 : (if true = true then 1 else 0 : Nat) = 1 := rfl
    rw [h1]
    apply subWithBorrow_one_eq

end UInt64
