/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.LowMask
import Azurite.AzNat.Equiv.Basic

namespace Azurite.AzNat

private lemma toNatLimbsList_replicate_maxUInt64 (n : Nat) :
    toNatLimbsList (List.replicate n ((0 : UInt64) - 1)) = 2 ^ (64 * n) - 1 := by
  induction n with
  | zero => simp [toNatLimbsList]
  | succ n ih =>
    rw [List.replicate_succ, toNatLimbsList_cons, ih]
    have hmax : ((0 : UInt64) - 1).toNat = 2 ^ 64 - 1 := by decide
    rw [hmax]
    have h64 : 64 * (n + 1) = 64 * n + 64 := by ring
    rw [h64, Nat.pow_add]
    have hpos : 1 ≤ 2 ^ (64 * n) := Nat.one_le_pow _ _ (by omega)
    omega

private lemma shiftLeft_one_sub_one_toNat (k : Nat) :
    (((1 : UInt64) <<< UInt64.ofNat (k % 64)) - 1).toNat = 2 ^ (k % 64) - 1 := by
  simp only [UInt64.toNat_sub, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat,
             show 1 % 2 ^ 64 = 1 from by omega, Nat.one_shiftLeft]
  have hr : k % 64 < 64 := Nat.mod_lt _ (by omega)
  have hmod : (UInt64.ofNat (k % 64)).toNat = k % 64 := by
    show (k % 64) % 2 ^ 64 = k % 64; exact Nat.mod_eq_of_lt (by omega)
  rw [hmod, Nat.mod_eq_of_lt hr]
  have hpow : 2 ^ (k % 64) < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hr
  rw [Nat.mod_eq_of_lt hpow]
  have hone : 1 ≤ 2 ^ (k % 64) := Nat.one_le_pow _ _ (by omega)
  have heq : 2 ^ 64 - 1 + 2 ^ (k % 64) = 2 ^ 64 + (2 ^ (k % 64) - 1) := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega)]

theorem toNat_lowMask (k : Nat) : (AzNat.lowMask k).toNat = 2 ^ k - 1 := by
  unfold AzNat.lowMask toNat
  simp only
  split
  · -- k % 64 == 0
    rename_i h
    simp [BEq.beq] at h
    simp only [Array.toList_replicate]
    rw [toNatLimbsList_replicate_maxUInt64]
    congr 2
    omega
  · -- k % 64 ≠ 0
    rename_i hne
    simp [BEq.beq] at hne
    simp only [Array.toList_push, Array.toList_replicate]
    rw [toNatLimbsList_append, List.length_replicate]
    rw [toNatLimbsList_cons, show toNatLimbsList ([] : List UInt64) = 0 from rfl]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [toNatLimbsList_replicate_maxUInt64, shiftLeft_one_sub_one_toNat k]
    have hr : k % 64 < 64 := Nat.mod_lt _ (by omega)
    have hpow_part : 1 ≤ 2 ^ (k % 64) := Nat.one_le_pow _ _ (by omega)
    have hpow_full : 1 ≤ 2 ^ (64 * (k / 64)) := Nat.one_le_pow _ _ (by omega)
    have hdiv : k = 64 * (k / 64) + k % 64 := (Nat.div_add_mod k 64).symm
    have hpow_split : 2 ^ k = 2 ^ (k % 64) * 2 ^ (64 * (k / 64)) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hpow_split, Nat.sub_one_mul]
    have hle : 2 ^ (64 * (k / 64)) ≤ 2 ^ (k % 64) * 2 ^ (64 * (k / 64)) := by
      have := Nat.mul_le_mul_right (2 ^ (64 * (k / 64))) hpow_part
      omega
    omega

theorem lowMask_eq_ofNat (k : Nat) : AzNat.lowMask k = ofNat (2 ^ k - 1) := by
  apply toNat_injective
  rw [toNat_lowMask, toNat_ofNat]

end Azurite.AzNat
