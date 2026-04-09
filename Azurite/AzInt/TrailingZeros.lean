import Azurite.AzInt.Basic
import Azurite.AzNat.TrailingZeros

namespace Azurite

/-- Count the number of trailing zeros in the binary representation of an integer.
Returns `none` for zero (which has infinitely many trailing zeros). -/
def AzInt.trailingZeros (z : AzInt) : Option Nat := z.abs.trailingZeros

end Azurite
