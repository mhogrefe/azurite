import Mathlib.Data.Nat.Basic
import Azurite.AzNat.Add

namespace Azurite.AzNat

theorem addWithCarry_zero_eq (a b : UInt64) :
  a.toNat + b.toNat + 0 = (if (addWithCarry a b false).2 then 1 else 0) * 2^64 + (addWithCarry a b false).1.toNat := by
  unfold addWithCarry
  dsimp
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have he1 : (a + b).toNat = (a.toNat + b.toNat) % 2^64 := UInt64.toNat_add a b
  have hl1 : decide (a + b < a) = true ↔ a.toNat + b.toNat ≥ 2^64 := by
    rw [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    omega
  by_cases h : a + b < a <;> simp [h] at * <;> omega

theorem addWithCarry_one_eq (a b : UInt64) :
  a.toNat + b.toNat + 1 = (if (addWithCarry a b true).2 then 1 else 0) * 2^64 + (addWithCarry a b true).1.toNat := by
  unfold addWithCarry
  dsimp
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have he1 : (a + b).toNat = (a.toNat + b.toNat) % 2^64 := UInt64.toNat_add a b
  have he2 : (a + b + 1).toNat = ((a + b).toNat + 1) % 2^64 := UInt64.toNat_add (a + b) (1 : UInt64)
  have h_one : (1 : UInt64).toNat = 1 := rfl

  have hl1 : decide (a + b < a) = true ↔ a.toNat + b.toNat ≥ 2^64 := by
    rw [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    omega
  have hl2 : decide (a + b + 1 < a + b) = true ↔ (a + b).toNat + 1 ≥ 2^64 := by
    rw [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, h_one]
    have hab := UInt64.toNat_lt (a + b)
    omega

  by_cases h1 : a + b < a <;> by_cases h2 : a + b + 1 < a + b <;> simp [h1, h2, h_one] at * <;> omega

theorem addWithCarry_eq (a b : UInt64) (c : Bool) :
  a.toNat + b.toNat + (if c then 1 else 0) = (if (addWithCarry a b c).2 then 1 else 0) * 2^64 + (addWithCarry a b c).1.toNat := by
  cases c
  · have h0 : (if false = true then 1 else 0 : Nat) = 0 := rfl
    rw [h0]
    apply addWithCarry_zero_eq
  · have h1 : (if true = true then 1 else 0 : Nat) = 1 := rfl
    rw [h1]
    apply addWithCarry_one_eq

end Azurite.AzNat
