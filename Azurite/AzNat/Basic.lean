namespace Azurite

structure AzNat where
  limbs : Array UInt64
  last_ne_zero : limbs.back? ≠ some 0
  deriving DecidableEq

instance : Inhabited AzNat := ⟨⟨#[], by simp⟩⟩

end Azurite
