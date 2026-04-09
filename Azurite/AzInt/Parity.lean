import Azurite.AzInt.Basic
import Azurite.AzNat.Parity

namespace Azurite

/-- Efficient parity test for integers: delegates to absolute value. -/
def AzInt.isEven (z : AzInt) : Bool := z.abs.isEven

/-- Efficient parity test for integers: delegates to absolute value. -/
def AzInt.isOdd (z : AzInt) : Bool := z.abs.isOdd

end Azurite
