import Azurite.UInt64.WideMul

namespace UInt64

/-- Computes `a * b + c` as a 128-bit result, returned as `(hi, lo)`.

The carry is added as a conditional *scalar* (`if _ then 1 else 0`) rather
than by branching on the result pair, so codegen keeps `(hi', lo')` in
registers instead of boxing it at a control-flow join point. -/
@[inline]
def mulWithCarry (a b c : UInt64) : UInt64 × UInt64 :=
  let (hi, lo) := wideMul a b
  let lo' := lo + c
  (hi + (if lo' < lo then 1 else 0), lo')

end UInt64
