import Azurite.AzNat.Parse
import Azurite.AzNat.ToString

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

#guard toString (0 : UInt64).toAzNat == "0"
#guard toString (5 : UInt64).toAzNat == "5"
#guard toString (18446744073709551615 : UInt64).toAzNat == "18446744073709551615"

#guard toString ((0 : Int64).toAzNatClampNeg) == "0"
#guard toString ((-5 : Int64).toAzNatClampNeg) == "0"
#guard toString ((-9223372036854775808 : Int64).toAzNatClampNeg) == "0"
#guard toString ((5 : Int64).toAzNatClampNeg) == "5"
#guard toString ((9223372036854775807 : Int64).toAzNatClampNeg) == "9223372036854775807"

#guard toString ((0 : Int32).toAzNatClampNeg) == "0"
#guard toString ((-5 : Int32).toAzNatClampNeg) == "0"
#guard toString ((5 : Int32).toAzNatClampNeg) == "5"

#guard toString ((-5 : ISize).toAzNatClampNeg) == "0"
#guard toString ((5 : ISize).toAzNatClampNeg) == "5"

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

#guard (Azurite.AzNat.parse "123".toList).get!.toUInt64 == 123
#guard (Azurite.AzNat.parse "18446744073709551617".toList).get!.toUInt64 == 1
#guard (Azurite.AzNat.parse "18446744073709551616".toList).get!.toInt64 == 0
#guard (Azurite.AzNat.parse "9223372036854775808".toList).get!.toInt64 == -9223372036854775808

#guard (Azurite.AzNat.parse "4294967297".toList).get!.toUInt32 == 1
#guard (Azurite.AzNat.parse "4294967295".toList).get!.toInt32 == -1
#guard (Azurite.AzNat.parse "2147483648".toList).get!.toInt32 == -2147483648

#guard (Azurite.AzNat.parse "65537".toList).get!.toUInt16 == 1
#guard (Azurite.AzNat.parse "65535".toList).get!.toInt16 == -1
#guard (Azurite.AzNat.parse "32768".toList).get!.toInt16 == -32768

#guard (Azurite.AzNat.parse "257".toList).get!.toUInt8 == 1
#guard (Azurite.AzNat.parse "255".toList).get!.toInt8 == -1
#guard (Azurite.AzNat.parse "128".toList).get!.toInt8 == -128
