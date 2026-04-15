import Azurite.UInt64.MulWithCarry

namespace UInt64

/-- Computes `a * b + acc + c` as a 128-bit result, returned as `(hi, lo)`.
    Fits without overflow since `(2^64-1)^2 + 2 * (2^64-1) = 2^128 - 1`. -/
@[inline]
def mulAddWithCarry (a b acc c : UInt64) : UInt64 × UInt64 :=
  let (hi, lo) := mulWithCarry a b c
  let lo' := lo + acc
  let hi' := if lo' < lo then hi + 1 else hi
  (hi', lo')

end UInt64
