/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.CompareDouble
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Gcd.HalfBinary

/-!
## Correctness of `cmpDouble`

`cmpDouble_eq_compare_toNat`: `cmpDouble x y = Ord.compare x.toNat (2 * y.toNat)`.  The limbs
of `2 y` formed by `doubleLimb` telescope: over `k` positions their value plus the carry out of
the top position equals twice the value of the low `k` limbs of `y` (`seqVal_doubleLimb`), and
the carry out vanishes once the window extends past `y`.  The top-down loop compares values
because the lower limbs contribute less than one unit of the position being compared
(`cmpDouble.go_eq`).
-/

namespace Azurite.AzNat

/-- The carry into position `j` of the doubling: the top bit of `yⱼ₋₁` (`0` at position `0`). -/
def doubleCarry (y : Array UInt64) (j : ℕ) : ℕ :=
  if j = 0 then 0 else (y.getD (j - 1) 0).toNat / 2 ^ 63

theorem toNat_doubleLimb (y : Array UInt64) (i : ℕ) :
    (doubleLimb y i).toNat + 2 ^ 64 * doubleCarry y (i + 1)
      = 2 * (y.getD i 0).toNat + doubleCarry y i := by
  unfold doubleLimb doubleCarry
  have hlt := (y.getD i 0).toNat_lt
  have hsh : (y.getD i 0 <<< 1).toNat = (y.getD i 0).toNat * 2 % 2 ^ 64 := by
    rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]; rfl
  have hc : (if i = 0 then (0 : UInt64) else y.getD (i - 1) 0 >>> 63).toNat
      = if i = 0 then 0 else (y.getD (i - 1) 0).toNat / 2 ^ 63 := by
    split_ifs
    · rfl
    · rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have hc_le : (if i = 0 then 0 else (y.getD (i - 1) 0).toNat / 2 ^ 63) ≤ 1 := by
    split_ifs
    · omega
    · have := (y.getD (i - 1) 0).toNat_lt; omega
  rw [UInt64.toNat_add, hsh, hc, Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  omega

/-- The doubled limbs telescope: over any window, their value plus the carry out of the top equals
twice the value of `y`'s limbs plus the carry into the bottom. -/
theorem seqVal_doubleLimb (y : Array UInt64) : ∀ (n i : ℕ),
    seqVal (fun k => doubleLimb y k) i n + 2 ^ (64 * n) * doubleCarry y (i + n)
      = 2 * seqVal (fun k => y.getD k 0) i n + doubleCarry y i := by
  intro n
  induction n with
  | zero => intro i; simp [seqVal]
  | succ n ih =>
    intro i
    have h1 := toNat_doubleLimb y i
    have h2 := ih (i + 1)
    rw [show i + 1 + n = i + (n + 1) by omega] at h2
    simp only [seqVal]
    rw [show 64 * (n + 1) = 64 * n + 64 by ring, pow_add]
    zify at h1 h2 ⊢
    linear_combination h1 + (2 : ℤ) ^ 64 * h2

/-- Peeling the top limb off a window. -/
theorem seqVal_succ_top (f : ℕ → UInt64) : ∀ (n i : ℕ),
    seqVal f i (n + 1) = seqVal f i n + 2 ^ (64 * n) * (f (i + n)).toNat := by
  intro n
  induction n with
  | zero => intro i; simp [seqVal]
  | succ n ih =>
    intro i
    rw [seqVal, ih (i + 1), seqVal, show i + 1 + n = i + (n + 1) by omega,
      show 64 * (n + 1) = 64 * n + 64 by ring, pow_add]
    ring

/-- A window of `n` limbs is below `2^(64 n)`. -/
theorem seqVal_lt (f : ℕ → UInt64) : ∀ (n i : ℕ), seqVal f i n < 2 ^ (64 * n) := by
  intro n
  induction n with
  | zero => intro i; simp [seqVal]
  | succ n ih =>
    intro i
    rw [seqVal, show 64 * (n + 1) = 64 + 64 * n by ring, pow_add]
    have h1 := (f i).toNat_lt
    have h2 := ih (i + 1)
    have h3 : (2 : ℕ) ^ 64 * (seqVal f (i + 1) n + 1) ≤ 2 ^ 64 * 2 ^ (64 * n) :=
      Nat.mul_le_mul_left _ h2
    omega

/-- The top-down limb comparison compares the windows' values. -/
theorem cmpDouble.go_eq (x y : Array UInt64) : ∀ k : ℕ,
    cmpDouble.go x y k
      = Ord.compare (seqVal (fun i => x.getD i 0) 0 k) (seqVal (fun i => doubleLimb y i) 0 k) := by
  intro k
  induction k with
  | zero => simp [cmpDouble.go, seqVal]
  | succ k ih =>
    rw [cmpDouble.go, seqVal_succ_top, seqVal_succ_top, Nat.zero_add,
      compare_UInt64_eq_compare_toNat]
    have hx := seqVal_lt (fun i => x.getD i 0) k 0
    have hd := seqVal_lt (fun i => doubleLimb y i) k 0
    rcases Nat.lt_trichotomy (x.getD k 0).toNat (doubleLimb y k).toNat with h | h | h
    · rw [compare_Nat_eq_of_lt _ _ h]
      dsimp only
      refine (compare_Nat_eq_of_lt _ _ ?_).symm
      have : 2 ^ (64 * k) * ((x.getD k 0).toNat + 1) ≤ 2 ^ (64 * k) * (doubleLimb y k).toNat :=
        Nat.mul_le_mul_left _ h
      nlinarith
    · rw [h, Nat.compare_eq_eq.mpr rfl]
      dsimp only
      rw [ih, Nat.add_comm (seqVal _ 0 k), Nat.add_comm (seqVal _ 0 k), compare_add_eq]
    · rw [compare_Nat_eq_of_gt _ _ h]
      dsimp only
      refine (compare_Nat_eq_of_gt _ _ ?_).symm
      have : 2 ^ (64 * k) * ((doubleLimb y k).toNat + 1) ≤ 2 ^ (64 * k) * (x.getD k 0).toNat :=
        Nat.mul_le_mul_left _ h
      nlinarith

/-- **Correctness of `cmpDouble`.** -/
theorem cmpDouble_eq_compare_toNat (x y : AzNat) :
    cmpDouble x y = Ord.compare x.toNat (2 * y.toNat) := by
  unfold cmpDouble
  rw [cmpDouble.go_eq]
  set k := max x.limbs.size (y.limbs.size + 1) with hk
  have hx : seqVal (fun i => x.limbs.getD i 0) 0 k = x.toNat :=
    seqVal_array x.limbs k (by omega)
  have hy : seqVal (fun i => y.limbs.getD i 0) 0 k = y.toNat :=
    seqVal_array y.limbs k (by omega)
  have hcarry : doubleCarry y.limbs k = 0 := by
    unfold doubleCarry
    rw [ite_eq_right (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl
  have hd := seqVal_doubleLimb y.limbs k 0
  rw [Nat.zero_add, hcarry, Nat.mul_zero, Nat.add_zero, hy] at hd
  rw [hx, hd]
  simp [doubleCarry]

end Azurite.AzNat
