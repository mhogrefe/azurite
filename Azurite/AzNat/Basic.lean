namespace Azurite

structure AzNat where
  limbs : Array UInt64
  last_ne_zero : limbs.back? ≠ some 0
  deriving DecidableEq

instance : OfNat AzNat 0 := ⟨⟨#[], by simp⟩⟩
instance : OfNat AzNat 1 := ⟨⟨#[1], by decide⟩⟩

instance : Zero AzNat := ⟨0⟩
instance : One AzNat := ⟨1⟩

instance : Inhabited AzNat := ⟨0⟩

def AzNat.beqUInt64 (a : AzNat) (u : UInt64) : Bool :=
  match a.limbs.size with
  | 0 => u == 0
  | 1 => a.limbs.back? == some u
  | _ => false

def AzNat.beqInt64 (a : AzNat) (i : Int64) : Bool :=
  (i ≥ 0) && a.beqUInt64 i.toUInt64

end Azurite
