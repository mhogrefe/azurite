import Azurite.UInt64.WideMul

namespace UInt64

/-- Computes `a * b + c` as a 128-bit result, returned as `(hi, lo)`. -/
@[inline]
def mulWithCarry (a b c : UInt64) : UInt64 × UInt64 :=
  let (hi, lo) := wideMul a b
  let lo' := lo + c
  let hi' := if lo' < lo then hi + 1 else hi
  (hi', lo')

end UInt64
