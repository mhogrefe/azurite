namespace UInt64

/-- Set the `i`-th bit of `u` (0-indexed, LSB first) to `1`. For `i ≥ 64` the original
value is returned; the operation is semantically invalid at those indices. -/
@[inline]
def setBit (u : UInt64) (i : Nat) : UInt64 :=
  if i < 64 then u ||| (1 <<< UInt64.ofNat i) else u

end UInt64
