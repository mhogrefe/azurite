import Azurite.AzInt.Basic
import Azurite.AzNat.Size

namespace Azurite

/-- The number of bits required to represent the integer's absolute value in binary.
Equivalent to `Nat.size` applied to the natural absolute value. -/
def AzInt.size (z : AzInt) : Nat := z.abs.size

end Azurite
