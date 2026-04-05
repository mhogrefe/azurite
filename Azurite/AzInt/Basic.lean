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

end Azurite
