import Azurite.AzInt.Basic
import Azurite.AzNat.ToString

namespace Azurite.AzInt

/-- Converts an `AzInt` to a sequence of characters without evaluating standard `Int.toString`. -/
def toChars (z : AzInt) : List Char :=
  if z.sign then AzNat.toChars z.abs
  else '-' :: AzNat.toChars z.abs

instance : ToString AzInt where
  toString z := String.ofList (toChars z)

end Azurite.AzInt
