import Azurite.AzNat.Basic

namespace Azurite.AzNat

/-- Adds two 64-bit unsigned integers along with a boolean carry, returning the sum and the new carry out. -/
@[inline]
def addWithCarry (a b : UInt64) (c : Bool) : UInt64 × Bool :=
  let sum1 := a + b
  let c1 := sum1 < a
  let c_val : UInt64 := if c then 1 else 0
  let sum2 := sum1 + c_val
  let c2 := sum2 < sum1
  (sum2, c1 || c2)

end Azurite.AzNat
