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
