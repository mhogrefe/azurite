import Azurite.AzNat.Basic

namespace Azurite

structure AzInt where
  sign : Bool
  abs : AzNat
  zero_sign : abs = 0 → sign = true
  deriving DecidableEq

instance : OfNat AzInt 0 := ⟨{ sign := true, abs := 0, zero_sign := fun _ => rfl }⟩
instance : OfNat AzInt 1 := ⟨{ sign := true, abs := 1, zero_sign := by intro h; contradiction }⟩

instance : Zero AzInt := ⟨0⟩
instance : One AzInt := ⟨1⟩

instance : Inhabited AzInt := ⟨0⟩

/-- Extremely fast `O(1)` equality check against a UInt64 without requiring allocations. -/
def AzInt.beqUInt64 (z : AzInt) (u : UInt64) : Bool :=
  z.sign && z.abs.beqUInt64 u

/-- Extremely fast `O(1)` equality check against an Int64. -/
def AzInt.beqInt64 (z : AzInt) (i : Int64) : Bool :=
  if i ≥ 0 then
    z.sign && z.abs.beqUInt64 i.toUInt64
  else
    (!z.sign) && z.abs.beqUInt64 (-i).toUInt64

/-- Extremely fast equality check against an AzNat without requiring allocations. -/
def AzInt.beqAzNat (z : AzInt) (a : AzNat) : Bool :=
  z.sign && (z.abs == a)

end Azurite
