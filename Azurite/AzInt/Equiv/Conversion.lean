/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Conversion
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzInt.Equiv.Basic

-- Unsigned Equivs
theorem UInt64.toInt_toAzInt (u : UInt64) : u.toAzInt.toInt = u.toNat := by
  have hd : u.toAzInt = ⟨true, u.toAzNat, fun _ => rfl⟩ := rfl
  rw [hd]
  dsimp [Azurite.AzInt.toInt]
  simp
  rw [UInt64.toNat_toAzNat]

theorem UInt32.toInt_toAzInt (u : UInt32) : u.toAzInt.toInt = u.toNat := by
  have hd : u.toAzInt = ⟨true, u.toAzNat, fun _ => rfl⟩ := rfl
  rw [hd]
  dsimp [Azurite.AzInt.toInt]
  simp
  rw [UInt32.toNat_toAzNat]

theorem UInt16.toInt_toAzInt (u : UInt16) : u.toAzInt.toInt = u.toNat := by
  have hd : u.toAzInt = ⟨true, u.toAzNat, fun _ => rfl⟩ := rfl
  rw [hd]
  dsimp [Azurite.AzInt.toInt]
  simp
  rw [UInt16.toNat_toAzNat]

theorem UInt8.toInt_toAzInt (u : UInt8) : u.toAzInt.toInt = u.toNat := by
  have hd : u.toAzInt = ⟨true, u.toAzNat, fun _ => rfl⟩ := rfl
  rw [hd]
  dsimp [Azurite.AzInt.toInt]
  simp
  rw [UInt8.toNat_toAzNat]

theorem USize.toInt_toAzInt (u : USize) : u.toAzInt.toInt = u.toNat := by
  have hd : u.toAzInt = ⟨true, u.toAzNat, fun _ => rfl⟩ := rfl
  rw [hd]
  dsimp [Azurite.AzInt.toInt]
  simp
  rw [USize.toNat_toAzNat]

-- Signed Equivs
theorem Int64.toInt_toAzInt (i : Int64) : i.toAzInt.toInt = i.toInt := by
  unfold Int64.toAzInt
  split_ifs with h
  · change -(↑((-i).toUInt64.toAzNat.toNat)) = i.toInt
    have hz : ((-i).toUInt64).toAzNat.toNat = ((-i).toUInt64).toNat := UInt64.toNat_toAzNat _
    rw [hz]
    have hu : (-i).toUInt64.toNat = (-(i.toBitVec)).toNat := by rfl
    rw [hu]
    have h_lt : i.toBitVec.toInt < 0 := of_decide_eq_true h
    have ht : i.toBitVec.toInt = i.toInt := rfl
    rw [← ht]
    have h_toBitVec_toInt : i.toBitVec.toInt = if 2 * i.toBitVec.toNat < 2 ^ 64 then (i.toBitVec.toNat : ℤ) else (i.toBitVec.toNat : ℤ) - (2 ^ 64 : ℤ) := rfl
    have h_neg_toNat : (-(i.toBitVec)).toNat = (2^64 - i.toBitVec.toNat) % 2^64 := BitVec.toNat_neg i.toBitVec
    rw [h_neg_toNat]
    have isLt := i.toBitVec.isLt
    have h_mod : (2^64 - i.toBitVec.toNat) % 2^64 = 2^64 - i.toBitVec.toNat := by
      apply Nat.mod_eq_of_lt
      omega
    rw [h_mod]
    omega
  · change ↑(i.toUInt64.toAzNat.toNat) = i.toInt
    have hz : i.toUInt64.toAzNat.toNat = i.toUInt64.toNat := UInt64.toNat_toAzNat _
    rw [hz]
    have hu : i.toUInt64.toNat = i.toBitVec.toNat := rfl
    rw [hu]
    have h_not_lt : ¬(i.toBitVec.toInt < 0) := fun hc => h (decide_eq_true hc)
    have ht : i.toBitVec.toInt = i.toInt := rfl
    rw [← ht]
    have h_toBitVec_toInt : i.toBitVec.toInt = if 2 * i.toBitVec.toNat < 2 ^ 64 then (i.toBitVec.toNat : ℤ) else (i.toBitVec.toNat : ℤ) - (2 ^ 64 : ℤ) := rfl
    have isLt := i.toBitVec.isLt
    omega

theorem Int32.toInt_toAzInt (i : Int32) : i.toAzInt.toInt = i.toInt := by
  unfold Int32.toAzInt
  rw [Int64.toInt_toAzInt]
  exact Int32.toInt_toInt64 i

theorem Int16.toInt_toAzInt (i : Int16) : i.toAzInt.toInt = i.toInt := by
  unfold Int16.toAzInt
  rw [Int64.toInt_toAzInt]
  exact Int16.toInt_toInt64 i

theorem Int8.toInt_toAzInt (i : Int8) : i.toAzInt.toInt = i.toInt := by
  unfold Int8.toAzInt
  rw [Int64.toInt_toAzInt]
  exact Int8.toInt_toInt64 i

theorem ISize.toInt_toAzInt (i : ISize) : i.toAzInt.toInt = i.toInt := by
  unfold ISize.toAzInt
  rw [Int64.toInt_toAzInt]
  exact ISize.toInt_toInt64 i

-- Inverses
theorem UInt64.ofInt_toNat_eq_toAzInt (u : UInt64) : Azurite.AzInt.ofInt u.toNat = u.toAzInt := by
  have ht : Azurite.AzInt.ofInt u.toNat = Azurite.AzInt.ofInt (u.toAzInt.toInt) := by
    have h1 : u.toAzInt.toInt = u.toNat := UInt64.toInt_toAzInt u
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem UInt32.ofInt_toNat_eq_toAzInt (u : UInt32) : Azurite.AzInt.ofInt u.toNat = u.toAzInt := by
  have ht : Azurite.AzInt.ofInt u.toNat = Azurite.AzInt.ofInt (u.toAzInt.toInt) := by
    have h1 : u.toAzInt.toInt = u.toNat := UInt32.toInt_toAzInt u
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem UInt16.ofInt_toNat_eq_toAzInt (u : UInt16) : Azurite.AzInt.ofInt u.toNat = u.toAzInt := by
  have ht : Azurite.AzInt.ofInt u.toNat = Azurite.AzInt.ofInt (u.toAzInt.toInt) := by
    have h1 : u.toAzInt.toInt = u.toNat := UInt16.toInt_toAzInt u
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem UInt8.ofInt_toNat_eq_toAzInt (u : UInt8) : Azurite.AzInt.ofInt u.toNat = u.toAzInt := by
  have ht : Azurite.AzInt.ofInt u.toNat = Azurite.AzInt.ofInt (u.toAzInt.toInt) := by
    have h1 : u.toAzInt.toInt = u.toNat := UInt8.toInt_toAzInt u
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem USize.ofInt_toNat_eq_toAzInt (u : USize) : Azurite.AzInt.ofInt u.toNat = u.toAzInt := by
  have ht : Azurite.AzInt.ofInt u.toNat = Azurite.AzInt.ofInt (u.toAzInt.toInt) := by
    have h1 : u.toAzInt.toInt = u.toNat := USize.toInt_toAzInt u
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem Int64.ofInt_toInt_eq_toAzInt (i : Int64) : Azurite.AzInt.ofInt i.toInt = i.toAzInt := by
  have ht : Azurite.AzInt.ofInt i.toInt = Azurite.AzInt.ofInt (i.toAzInt.toInt) := by
    have h1 : i.toAzInt.toInt = i.toInt := Int64.toInt_toAzInt i
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem Int32.ofInt_toInt_eq_toAzInt (i : Int32) : Azurite.AzInt.ofInt i.toInt = i.toAzInt := by
  have ht : Azurite.AzInt.ofInt i.toInt = Azurite.AzInt.ofInt (i.toAzInt.toInt) := by
    have h1 : i.toAzInt.toInt = i.toInt := Int32.toInt_toAzInt i
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem Int16.ofInt_toInt_eq_toAzInt (i : Int16) : Azurite.AzInt.ofInt i.toInt = i.toAzInt := by
  have ht : Azurite.AzInt.ofInt i.toInt = Azurite.AzInt.ofInt (i.toAzInt.toInt) := by
    have h1 : i.toAzInt.toInt = i.toInt := Int16.toInt_toAzInt i
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem Int8.ofInt_toInt_eq_toAzInt (i : Int8) : Azurite.AzInt.ofInt i.toInt = i.toAzInt := by
  have ht : Azurite.AzInt.ofInt i.toInt = Azurite.AzInt.ofInt (i.toAzInt.toInt) := by
    have h1 : i.toAzInt.toInt = i.toInt := Int8.toInt_toAzInt i
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem ISize.ofInt_toInt_eq_toAzInt (i : ISize) : Azurite.AzInt.ofInt i.toInt = i.toAzInt := by
  have ht : Azurite.AzInt.ofInt i.toInt = Azurite.AzInt.ofInt (i.toAzInt.toInt) := by
    have h1 : i.toAzInt.toInt = i.toInt := ISize.toInt_toAzInt i
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem Azurite.AzNat.toInt_toAzInt (n : Azurite.AzNat) : n.toAzInt.toInt = (n.toNat : Int) := rfl

theorem Azurite.AzInt.toNat_natAbs (z : Azurite.AzInt) : z.natAbs.toNat = z.toInt.natAbs := by
  unfold Azurite.AzInt.natAbs
  dsimp [Azurite.AzInt.toInt]
  split_ifs with h
  · rfl
  · omega

theorem Azurite.AzNat.ofInt_toNat_eq_toAzInt (n : Azurite.AzNat) : Azurite.AzInt.ofInt (n.toNat : Int) = n.toAzInt := by
  have ht : Azurite.AzInt.ofInt (n.toNat : Int) = Azurite.AzInt.ofInt (n.toAzInt.toInt) := by
    have h1 : n.toAzInt.toInt = (n.toNat : Int) := Azurite.AzNat.toInt_toAzInt n
    rw [h1]
  rw [ht, Azurite.AzInt.ofInt_toInt]

theorem Azurite.AzInt.ofNat_natAbs_eq_natAbs (z : Azurite.AzInt) : Azurite.AzNat.ofNat z.toInt.natAbs = z.natAbs := by
  have ht : Azurite.AzNat.ofNat z.toInt.natAbs = Azurite.AzNat.ofNat z.natAbs.toNat := by
    have h1 : z.natAbs.toNat = z.toInt.natAbs := Azurite.AzInt.toNat_natAbs z
    rw [h1]
  rw [ht, Azurite.AzNat.ofNat_toNat]
