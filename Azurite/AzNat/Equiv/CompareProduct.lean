/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.CompareProduct
import Azurite.AzNat.Equiv.CompareProducts

/-!
## Correctness of `AzNat.compareProduct`

`compareProduct_eq : compareProduct a b c = compare (a.toNat * b.toNat) c.toNat`, screen by
screen, with the bit-length bounds `2^(size x − 1) ≤ x < 2^(size x)`.
-/

namespace Azurite.AzNat

/-- **Correctness of `compareProduct`.** -/
theorem compareProduct_eq (a b c : AzNat) :
    compareProduct a b c = Ord.compare (a.toNat * b.toNat) c.toNat := by
  unfold compareProduct
  have h1 : ∀ u : AzNat, u = 1 ↔ u.toNat = 1 :=
    fun u => ⟨fun h => by rw [h, toNat_one], fun h => toNat_injective (h.trans toNat_one.symm)⟩
  simp only [eq_zero_iff_toNat, h1, compare_eq_compare_toNat, le_iff_toNat_le, ← size_toNat,
    toNat_mul]
  set x := a.toNat
  set y := b.toNat
  set z := c.toNat
  split_ifs with hab hc hc' ha hb hge hs hs2
  · symm; rw [compare_Nat_eq_iff]
    rcases hab with h | h <;> simp [h, hc]
  · symm; rw [compare_Nat_lt_iff]
    have : x * y = 0 := by rcases hab with h | h <;> simp [h]
    rw [this]; exact Nat.pos_of_ne_zero hc
  · symm; rw [compare_Nat_gt_iff, hc']
    rw [not_or] at hab
    exact Nat.mul_pos (Nat.pos_of_ne_zero hab.1) (Nat.pos_of_ne_zero hab.2)
  · rw [ha, one_mul]
  · rw [hb, mul_one]
  all_goals rw [not_or] at hab
  all_goals have hx : 2 ≤ x := by omega
  all_goals have hy : 2 ≤ y := by omega
  all_goals have hz : 0 < z := Nat.pos_of_ne_zero hc'
  · symm; rw [compare_Nat_gt_iff]
    rcases hge with h | h
    · calc z < 2 * z := by omega
        _ ≤ y * x := Nat.mul_le_mul (by omega) h
        _ = x * y := mul_comm _ _
    · calc z < 2 * z := by omega
        _ ≤ x * y := Nat.mul_le_mul (by omega) h
  · symm; rw [compare_Nat_gt_iff]
    calc z < 2 ^ z.size := Nat.lt_size_self z
      _ ≤ 2 ^ (x.size - 1 + (y.size - 1)) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have := Nat.size_pos.mpr (show 0 < x by omega)
          have := Nat.size_pos.mpr (show 0 < y by omega)
          omega
      _ = 2 ^ (x.size - 1) * 2 ^ (y.size - 1) := pow_add _ _ _
      _ ≤ x * y := Nat.mul_le_mul (two_pow_size_sub_one_le (by omega))
          (two_pow_size_sub_one_le (by omega))
  · symm; rw [compare_Nat_lt_iff]
    calc x * y < 2 ^ x.size * 2 ^ y.size :=
          Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self x) (Nat.lt_size_self y).le
            (Nat.two_pow_pos _)
      _ = 2 ^ (x.size + y.size) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (z.size - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ z := two_pow_size_sub_one_le hz

end Azurite.AzNat
