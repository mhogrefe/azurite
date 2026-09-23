/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Conversion
import Azurite.AzInt.Basic

def UInt64.toAzInt (u : UInt64) : Azurite.AzInt :=
  ⟨true, u.toAzNat, fun _ => rfl⟩

def UInt32.toAzInt (u : UInt32) : Azurite.AzInt := ⟨true, u.toAzNat, fun _ => rfl⟩
def UInt16.toAzInt (u : UInt16) : Azurite.AzInt := ⟨true, u.toAzNat, fun _ => rfl⟩
def UInt8.toAzInt (u : UInt8) : Azurite.AzInt := ⟨true, u.toAzNat, fun _ => rfl⟩
def USize.toAzInt (u : USize) : Azurite.AzInt := ⟨true, u.toAzNat, fun _ => rfl⟩

def Int64.toAzInt (i : Int64) : Azurite.AzInt :=
  if h : i < 0 then
    let abs_u := (-i).toUInt64
    ⟨false, abs_u.toAzNat, by
      intro h_abs
      have hz : abs_u = 0 := by
        unfold UInt64.toAzNat at h_abs
        split_ifs at h_abs with hu
        · exact hu
        · have hc : [abs_u] = [] := congrArg Array.toList (congrArg Azurite.AzNat.limbs h_abs)
          contradiction
      have hzvec : (-i).toBitVec = 0 := congrArg UInt64.toBitVec hz
      have hb : (-i).toBitVec = -(i.toBitVec) := rfl
      have hp : -(i.toBitVec) = 0 := by
        rw [← hb]
        exact hzvec
      have hn_neg : -(-(i.toBitVec)) = -0 := congrArg Neg.neg hp
      have hx : i.toBitVec = -(-(i.toBitVec)) := BitVec.neg_neg.symm
      have hn_zero : - (0 : BitVec 64) = 0 := rfl
      have i_eq_0 : i.toBitVec = 0 := by
        rw [hx, hn_neg, hn_zero]
      have hi_int : i.toBitVec.toInt = 0 := congrArg BitVec.toInt i_eq_0
      have hc : i.toBitVec.toInt < 0 := of_decide_eq_true h
      omega⟩
  else
    let abs_u := i.toUInt64
    ⟨true, abs_u.toAzNat, fun _ => rfl⟩

def Int32.toAzInt (i : Int32) : Azurite.AzInt := i.toInt64.toAzInt
def Int16.toAzInt (i : Int16) : Azurite.AzInt := i.toInt64.toAzInt
def Int8.toAzInt (i : Int8) : Azurite.AzInt := i.toInt64.toAzInt
def ISize.toAzInt (i : ISize) : Azurite.AzInt := i.toInt64.toAzInt

def Azurite.AzNat.toAzInt (n : Azurite.AzNat) : Azurite.AzInt := ⟨true, n, fun _ => rfl⟩

namespace Azurite.AzInt

def natAbs (z : AzInt) : Azurite.AzNat := z.abs


def toUInt64 (z : AzInt) : UInt64 :=
  if z.sign then z.abs.toUInt64 else -(z.abs.toUInt64)

def toUInt32 (z : AzInt) : UInt32 := z.toUInt64.toUInt32
def toUInt16 (z : AzInt) : UInt16 := z.toUInt64.toUInt16
def toUInt8 (z : AzInt) : UInt8 := z.toUInt64.toUInt8
def toUSize (z : AzInt) : USize := z.toUInt64.toUSize

def toInt64 (z : AzInt) : Int64 :=
  if z.sign then z.abs.toInt64 else -(z.abs.toInt64)

def toInt32 (z : AzInt) : Int32 := z.toInt64.toInt32
def toInt16 (z : AzInt) : Int16 := z.toInt64.toInt16
def toInt8 (z : AzInt) : Int8 := z.toInt64.toInt8
def toISize (z : AzInt) : ISize := z.toInt64.toISize

end Azurite.AzInt
