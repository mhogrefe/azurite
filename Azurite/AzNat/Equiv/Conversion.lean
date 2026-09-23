/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Conversion
import Azurite.AzNat.Equiv.Basic

theorem UInt64.toNat_toAzNat (u : UInt64) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt64.toAzNat
  by_cases h : u = 0
  · simp [h, Azurite.AzNat.toNat, Azurite.AzNat.toNatLimbsList]
  · simp [h, Azurite.AzNat.toNat, Azurite.AzNat.toNatLimbsList]

theorem UInt32.toNat_toAzNat (u : UInt32) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt32.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

theorem UInt16.toNat_toAzNat (u : UInt16) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt16.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

theorem UInt8.toNat_toAzNat (u : UInt8) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt8.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

theorem USize.toNat_toAzNat (u : USize) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold USize.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

theorem Int64.toNat_toAzNatClampNeg (i : Int64) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int64.toAzNatClampNeg
  split
  · rename_i h
    have h1 : i.toBitVec.slt 0 = true := h
    have h2 : decide (i.toBitVec.toInt < 0) = true := h1
    have h3 : i.toInt < 0 := of_decide_eq_true h2
    simp [Azurite.AzNat.toNat, Azurite.AzNat.toNatLimbsList]
    change 0 = i.toInt.toNat
    omega
  · rename_i h
    rw [UInt64.toNat_toAzNat]
    have h1 : ¬(i.toBitVec.slt 0 = true) := h
    have h2 : ¬(decide (i.toBitVec.toInt < 0) = true) := h1
    have h3 : ¬(i.toInt < 0) := fun hc => h2 (decide_eq_true hc)
    have h4 : 0 ≤ i.toInt := by exact Int.not_lt.mp h3
    change i.toBitVec.toNat = i.toInt.toNat
    have h_toInt : i.toInt = if 2 * i.toBitVec.toNat < 2 ^ 64 then (i.toBitVec.toNat : ℤ) else (i.toBitVec.toNat : ℤ) - (2 ^ 64 : ℤ) := rfl
    have isLt := i.toBitVec.isLt
    omega

theorem Int32.toNat_toAzNatClampNeg (i : Int32) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int32.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [Int32.toInt_toInt64]

theorem Int16.toNat_toAzNatClampNeg (i : Int16) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int16.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [Int16.toInt_toInt64]

theorem Int8.toNat_toAzNatClampNeg (i : Int8) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int8.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [Int8.toInt_toInt64]

theorem ISize.toNat_toAzNatClampNeg (i : ISize) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold ISize.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [ISize.toInt_toInt64]

theorem UInt64.ofNat_toNat_eq_toAzNat (u : UInt64) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt64.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem UInt32.ofNat_toNat_eq_toAzNat (u : UInt32) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt32.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem UInt16.ofNat_toNat_eq_toAzNat (u : UInt16) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt16.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem UInt8.ofNat_toNat_eq_toAzNat (u : UInt8) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt8.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem USize.ofNat_toNat_eq_toAzNat (u : USize) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← USize.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem Int64.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int64) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int64.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

theorem Int32.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int32) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int32.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

theorem Int16.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int16) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int16.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

theorem Int8.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int8) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int8.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

theorem ISize.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : ISize) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← ISize.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

namespace Azurite.AzNat

lemma toNatLimbsList_mod_2_64 (l : List UInt64) : toNatLimbsList l % 2^64 = if h : 0 < l.length then (l.get ⟨0, h⟩).toNat else 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [toNatLimbsList]

lemma toNat_mod_2_64_eq_toUInt64_toNat (n : AzNat) : n.toNat % 2^64 = n.toUInt64.toNat := by
  unfold toNat toUInt64
  have ht := toNatLimbsList_mod_2_64 n.limbs.toList
  rw [ht]
  simp
  split
  · rfl
  · rfl

theorem toUInt64_toNat (n : AzNat) : n.toUInt64 = n.toNat.toUInt64 := by
  apply UInt64.ext
  have h_nat : n.toNat.toUInt64.toNat = n.toNat % 2^64 := rfl
  rw [h_nat]
  exact (toNat_mod_2_64_eq_toUInt64_toNat n).symm

theorem toUInt64_ofNat (n : Nat) : (ofNat n).toUInt64 = n.toUInt64 := by
  have ht := toUInt64_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- UInt32
lemma nat_toUInt64_toUInt32 (N : Nat) : N.toUInt64.toUInt32 = N.toUInt32 := by
  apply UInt32.ext
  have h1 : N.toUInt64.toUInt32.toNat = N.toUInt64.toNat % 2^32 := rfl
  have h2 : N.toUInt64.toNat = N % 2^64 := rfl
  have h3 : N.toUInt32.toNat = N % 2^32 := rfl
  rw [h1, h2, h3]
  exact Nat.mod_mod_of_dvd N (by decide)

theorem toUInt32_toNat (n : AzNat) : n.toUInt32 = n.toNat.toUInt32 := by
  have h1 : n.toUInt32 = n.toUInt64.toUInt32 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt32]

theorem toUInt32_ofNat (n : Nat) : (ofNat n).toUInt32 = n.toUInt32 := by
  have ht := toUInt32_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- UInt16
lemma nat_toUInt64_toUInt16 (N : Nat) : N.toUInt64.toUInt16 = N.toUInt16 := by
  apply UInt16.ext
  have h1 : N.toUInt64.toUInt16.toNat = N.toUInt64.toNat % 2^16 := rfl
  have h2 : N.toUInt64.toNat = N % 2^64 := rfl
  have h3 : N.toUInt16.toNat = N % 2^16 := rfl
  rw [h1, h2, h3]
  exact Nat.mod_mod_of_dvd N (by decide)

theorem toUInt16_toNat (n : AzNat) : n.toUInt16 = n.toNat.toUInt16 := by
  have h1 : n.toUInt16 = n.toUInt64.toUInt16 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt16]

theorem toUInt16_ofNat (n : Nat) : (ofNat n).toUInt16 = n.toUInt16 := by
  have ht := toUInt16_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- UInt8
lemma nat_toUInt64_toUInt8 (N : Nat) : N.toUInt64.toUInt8 = N.toUInt8 := by
  apply UInt8.ext
  have h1 : N.toUInt64.toUInt8.toNat = N.toUInt64.toNat % 2^8 := rfl
  have h2 : N.toUInt64.toNat = N % 2^64 := rfl
  have h3 : N.toUInt8.toNat = N % 2^8 := rfl
  rw [h1, h2, h3]
  exact Nat.mod_mod_of_dvd N (by decide)

theorem toUInt8_toNat (n : AzNat) : n.toUInt8 = n.toNat.toUInt8 := by
  have h1 : n.toUInt8 = n.toUInt64.toUInt8 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt8]

theorem toUInt8_ofNat (n : Nat) : (ofNat n).toUInt8 = n.toUInt8 := by
  have ht := toUInt8_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- USize
lemma nat_toUInt64_toUSize (N : Nat) : N.toUInt64.toUSize = N.toUSize := by
  apply USize.ext
  have h1 : N.toUInt64.toUSize.toNat = N.toUInt64.toNat % USize.size := rfl
  have h2 : N.toUInt64.toNat = N % 2^64 := rfl
  have h3 : N.toUSize.toNat = N % USize.size := rfl
  rw [h1, h2, h3]
  have hdvd : USize.size ∣ 2^64 := by
    obtain h | h := USize.size_eq
    · rw [h]; decide
    · rw [h]; decide
  exact Nat.mod_mod_of_dvd N hdvd

theorem toUSize_toNat (n : AzNat) : n.toUSize = n.toNat.toUSize := by
  have h1 : n.toUSize = n.toUInt64.toUSize := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUSize]

theorem toUSize_ofNat (n : Nat) : (ofNat n).toUSize = n.toUSize := by
  have ht := toUSize_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- Int64
theorem toInt64_toNat (n : AzNat) : n.toInt64 = n.toNat.toUInt64.toInt64 := by
  have h1 : n.toInt64 = n.toUInt64.toInt64 := rfl
  rw [h1, toUInt64_toNat]

theorem toInt64_ofNat (n : Nat) : (ofNat n).toInt64 = n.toUInt64.toInt64 := by
  have ht := toInt64_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- Int32
theorem toInt32_toNat (n : AzNat) : n.toInt32 = n.toNat.toUInt32.toInt32 := by
  have h1 : n.toInt32 = n.toUInt64.toUInt32.toInt32 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt32]

theorem toInt32_ofNat (n : Nat) : (ofNat n).toInt32 = n.toUInt32.toInt32 := by
  have ht := toInt32_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- Int16
theorem toInt16_toNat (n : AzNat) : n.toInt16 = n.toNat.toUInt16.toInt16 := by
  have h1 : n.toInt16 = n.toUInt64.toUInt16.toInt16 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt16]

theorem toInt16_ofNat (n : Nat) : (ofNat n).toInt16 = n.toUInt16.toInt16 := by
  have ht := toInt16_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- Int8
theorem toInt8_toNat (n : AzNat) : n.toInt8 = n.toNat.toUInt8.toInt8 := by
  have h1 : n.toInt8 = n.toUInt64.toUInt8.toInt8 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt8]

theorem toInt8_ofNat (n : Nat) : (ofNat n).toInt8 = n.toUInt8.toInt8 := by
  have ht := toInt8_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- ISize
theorem toISize_toNat (n : AzNat) : n.toISize = n.toNat.toUSize.toISize := by
  have h1 : n.toISize = n.toUInt64.toUSize.toISize := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUSize]

theorem toISize_ofNat (n : Nat) : (ofNat n).toISize = n.toUSize.toISize := by
  have ht := toISize_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

end Azurite.AzNat
