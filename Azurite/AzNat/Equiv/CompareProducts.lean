/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.CompareProducts
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Size

/-!
## Correctness of `AzNat.compareProducts`

`compareProducts_eq : compareProducts a b c d = compare (a.toNat * b.toNat) (c.toNat * d.toNat)`.
Each screen is a monotonicity fact about products of natural numbers, and the bit-length screen
rests on `2^(size x − 1) ≤ x < 2^(size x)`.
-/

namespace Azurite.AzNat

theorem compare_Nat_lt_iff (x y : ℕ) : Ord.compare x y = .lt ↔ x < y := by
  rcases lt_trichotomy x y with h | h | h
  · simp [compare_Nat_eq_of_lt _ _ h, h]
  · subst h; simp
  · simp [compare_Nat_eq_of_gt _ _ h, not_lt.mpr h.le]

theorem compare_Nat_eq_iff (x y : ℕ) : Ord.compare x y = .eq ↔ x = y := by
  rcases lt_trichotomy x y with h | h | h
  · simp [compare_Nat_eq_of_lt _ _ h, h.ne]
  · subst h; simp
  · simp [compare_Nat_eq_of_gt _ _ h, h.ne']

theorem compare_Nat_gt_iff (x y : ℕ) : Ord.compare x y = .gt ↔ y < x := by
  rcases lt_trichotomy x y with h | h | h
  · simp [compare_Nat_eq_of_lt _ _ h, not_lt.mpr h.le]
  · subst h; simp
  · simp [compare_Nat_eq_of_gt _ _ h, h]

theorem eq_zero_iff_toNat (a : AzNat) : a = 0 ↔ a.toNat = 0 :=
  ⟨fun h => by rw [h, toNat_zero], fun h => toNat_injective (h.trans toNat_zero.symm)⟩

/-- `2^(size x − 1) ≤ x` for `x > 0`. -/
theorem two_pow_size_sub_one_le {x : ℕ} (hx : 0 < x) : 2 ^ (x.size - 1) ≤ x :=
  Nat.lt_size.mp (by have := Nat.size_pos.mpr hx; omega)

/-- The product of two positive numbers compares like the pairs when those agree. -/
private theorem compare_mul_of_pairs {x y z w : ℕ} (hw : 0 < w)
    (hxz : Ord.compare x z = Ord.compare y w) :
    Ord.compare (x * y) (z * w) = Ord.compare x z := by
  rcases h : Ord.compare x z with _ | _ | _
  · rw [h] at hxz
    replace hxz := hxz.symm
    rw [compare_Nat_lt_iff] at h hxz ⊢
    exact Nat.mul_lt_mul_of_lt_of_le h hxz.le hw
  · rw [h] at hxz
    replace hxz := hxz.symm
    rw [compare_Nat_eq_iff] at h hxz ⊢
    rw [h, hxz]
  · rw [h] at hxz
    replace hxz := hxz.symm
    rw [compare_Nat_gt_iff] at h hxz ⊢
    exact Nat.mul_lt_mul_of_lt_of_le h hxz.le (Nat.lt_of_le_of_lt (Nat.zero_le _) hxz)

private theorem compare_mul_left {z y w : ℕ} (hz : 0 < z) :
    Ord.compare (z * y) (z * w) = Ord.compare y w := by
  rcases h : Ord.compare y w with _ | _ | _
  · rw [compare_Nat_lt_iff] at h ⊢; exact Nat.mul_lt_mul_of_pos_left h hz
  · rw [compare_Nat_eq_iff] at h ⊢; rw [h]
  · rw [compare_Nat_gt_iff] at h ⊢; exact Nat.mul_lt_mul_of_pos_left h hz

private theorem compare_mul_right {y x z : ℕ} (hy : 0 < y) :
    Ord.compare (x * y) (z * y) = Ord.compare x z := by
  rw [mul_comm x, mul_comm z, compare_mul_left hy]

/-- The bit-length screen: a surplus of two bits decides. -/
private theorem mul_lt_mul_of_size {x y z w : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : z.size + w.size + 2 ≤ x.size + y.size) : z * w < x * y := by
  have hxs := Nat.size_pos.mpr hx
  have hys := Nat.size_pos.mpr hy
  calc z * w < 2 ^ z.size * 2 ^ w.size :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self z) (Nat.lt_size_self w).le
          (Nat.two_pow_pos _)
    _ = 2 ^ (z.size + w.size) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (x.size - 1 + (y.size - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (x.size - 1) * 2 ^ (y.size - 1) := pow_add _ _ _
    _ ≤ x * y := Nat.mul_le_mul (two_pow_size_sub_one_le hx) (two_pow_size_sub_one_le hy)

/-- **Correctness of `compareProducts`.** -/
theorem compareProducts_eq (a b c d : AzNat) :
    compareProducts a b c d = Ord.compare (a.toNat * b.toNat) (c.toNat * d.toNat) := by
  unfold compareProducts
  simp only [eq_zero_iff_toNat, compare_eq_compare_toNat, ← size_toNat, toNat_mul, beq_iff_eq]
  set x := a.toNat
  set y := b.toNat
  set z := c.toNat
  set w := d.toNat
  split_ifs with hab hcd hcd' hp hp2 hp3 hq hq2 hq3 hs hs2
  · -- both products are zero
    symm; rw [compare_Nat_eq_iff]
    rcases hab with h | h <;> rcases hcd with h' | h' <;> simp [h, h']
  · symm; rw [compare_Nat_lt_iff]
    have : x * y = 0 := by rcases hab with h | h <;> simp [h]
    rw [this]
    rw [not_or] at hcd
    exact Nat.mul_pos (Nat.pos_of_ne_zero hcd.1) (Nat.pos_of_ne_zero hcd.2)
  · symm; rw [compare_Nat_gt_iff]
    have : z * w = 0 := by rcases hcd' with h | h <;> simp [h]
    rw [this]
    rw [not_or] at hab
    exact Nat.mul_pos (Nat.pos_of_ne_zero hab.1) (Nat.pos_of_ne_zero hab.2)
  all_goals rw [not_or] at hab hcd'
  all_goals have hx : 0 < x := Nat.pos_of_ne_zero hab.1
  all_goals have hy : 0 < y := Nat.pos_of_ne_zero hab.2
  all_goals have hz : 0 < z := Nat.pos_of_ne_zero hcd'.1
  all_goals have hw : 0 < w := Nat.pos_of_ne_zero hcd'.2
  · exact (compare_mul_of_pairs hw hp).symm
  · rw [compare_Nat_eq_iff] at hp2
    rw [hp2, compare_mul_left hz]
  · rw [compare_Nat_eq_iff] at hp3
    rw [hp3, compare_mul_right hw]
  · rw [mul_comm z w]
    exact (compare_mul_of_pairs hz hq).symm
  · rw [compare_Nat_eq_iff] at hq2
    rw [hq2, mul_comm z w, compare_mul_left hw]
  · rw [compare_Nat_eq_iff] at hq3
    rw [hq3, mul_comm z w, compare_mul_right hz]
  · symm; rw [compare_Nat_gt_iff]
    exact mul_lt_mul_of_size hx hy hs
  · symm; rw [compare_Nat_lt_iff]
    exact mul_lt_mul_of_size hz hw hs2

end Azurite.AzNat
