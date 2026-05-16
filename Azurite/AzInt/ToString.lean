import Azurite.AzInt.Basic
import Azurite.AzNat.ToStringBase

namespace Azurite.AzInt

/-- Convert an `AzInt` to its decimal `String` representation. Negative
    values are prefixed with `'-'`; the zero invariant (`sign = true`
    when `abs = 0`) ensures `0` prints as `"0"`, not `"-0"`. -/
def toString (z : AzInt) : String :=
  if z.sign then AzNat.toString z.abs
  else "-" ++ AzNat.toString z.abs

instance : ToString AzInt where
  toString := AzInt.toString

end Azurite.AzInt
