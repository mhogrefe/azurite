import Azurite.AzNat.Basic
import Azurite.AzNat.Compare

namespace Azurite

structure AzInt where
  sign : Bool
  abs : AzNat
  zero_sign : abs = 0 → sign = true
  deriving DecidableEq

instance : OfNat AzInt 0 := ⟨{ sign := true, abs := 0, zero_sign := fun _ => rfl}⟩
instance : OfNat AzInt 1 := ⟨{ sign := true, abs := 1, zero_sign := by intro h; contradiction}⟩

instance : Zero AzInt := ⟨0⟩
instance : One AzInt := ⟨1⟩

instance : Inhabited AzInt := ⟨0⟩

def AzInt.beqUInt64 (z : AzInt) (u : UInt64) : Bool :=
  z.sign && z.abs.beqUInt64 u

def AzInt.beqInt64 (z : AzInt) (i : Int64) : Bool :=
  if i ≥ 0 then
    z.sign && z.abs.beqUInt64 i.toUInt64
  else
    (!z.sign) && z.abs.beqUInt64 (-i).toUInt64

def AzInt.beqAzNat (z : AzInt) (a : AzNat) : Bool :=
  z.sign && (z.abs == a)

def AzInt.compareUInt64 (z : AzInt) (u : UInt64) : Ordering :=
  if z.sign then z.abs.compareUInt64 u else .lt

def AzInt.compareInt64 (z : AzInt) (i : Int64) : Ordering :=
  if z.sign then
    if i < 0 then .gt else z.abs.compareUInt64 i.toUInt64
  else
    if i < 0 then (z.abs.compareUInt64 (-i).toUInt64).swap
    else .lt

def AzInt.compareAzNat (z : AzInt) (a : AzNat) : Ordering :=
  if z.sign then Ord.compare z.abs a else .lt

end Azurite
