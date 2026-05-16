import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs

def UInt64.toAzNat (u : UInt64) : Azurite.AzNat :=
  if h : u = 0 then
    ⟨#[], by simp⟩
  else
    ⟨#[u], by
      intro hc
      have h1 : #[u].back? = some u := rfl
      rw [h1] at hc
      simp at hc
      contradiction⟩

def UInt32.toAzNat (u : UInt32) : Azurite.AzNat := u.toUInt64.toAzNat
def UInt16.toAzNat (u : UInt16) : Azurite.AzNat := u.toUInt64.toAzNat
def UInt8.toAzNat (u : UInt8) : Azurite.AzNat := u.toUInt64.toAzNat
def USize.toAzNat (u : USize) : Azurite.AzNat := u.toUInt64.toAzNat

def Int64.toAzNatClampNeg (i : Int64) : Azurite.AzNat :=
  if i < 0 then
    ⟨#[], by simp⟩
  else
    i.toUInt64.toAzNat

def Int32.toAzNatClampNeg (i : Int32) : Azurite.AzNat := i.toInt64.toAzNatClampNeg
def Int16.toAzNatClampNeg (i : Int16) : Azurite.AzNat := i.toInt64.toAzNatClampNeg
def Int8.toAzNatClampNeg (i : Int8) : Azurite.AzNat := i.toInt64.toAzNatClampNeg
def ISize.toAzNatClampNeg (i : ISize) : Azurite.AzNat := i.toInt64.toAzNatClampNeg

namespace Azurite.AzNat

def toUInt64 (n : AzNat) : UInt64 :=
  if h : n.limbs.size > 0 then n.limbs[0] else 0

def toUInt32 (n : AzNat) : UInt32 := n.toUInt64.toUInt32
def toUInt16 (n : AzNat) : UInt16 := n.toUInt64.toUInt16
def toUInt8 (n : AzNat) : UInt8 := n.toUInt64.toUInt8
def toUSize (n : AzNat) : USize := n.toUInt64.toUSize

def toInt64 (n : AzNat) : Int64 := n.toUInt64.toInt64
def toInt32 (n : AzNat) : Int32 := n.toUInt64.toUInt32.toInt32
def toInt16 (n : AzNat) : Int16 := n.toUInt64.toUInt16.toInt16
def toInt8 (n : AzNat) : Int8 := n.toUInt64.toUInt8.toInt8
def toISize (n : AzNat) : ISize := n.toUInt64.toUSize.toISize

end Azurite.AzNat
