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

end Azurite
