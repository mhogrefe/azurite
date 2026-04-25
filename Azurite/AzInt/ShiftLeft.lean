import Azurite.AzInt.Basic
import Azurite.AzNat.ShiftLeft

namespace Azurite.AzInt

/-- Left shift: `z <<< sh`.  Preserves the sign of `z` and shifts the magnitude
    left by `sh` bits. -/
def shiftLeft (z : AzInt) (sh : Nat) : AzInt :=
  ⟨z.sign, z.abs <<< sh, fun h => z.zero_sign (AzNat.shiftLeft_eq_zero h)⟩

instance : HShiftLeft AzInt Nat AzInt := ⟨shiftLeft⟩

end Azurite.AzInt
