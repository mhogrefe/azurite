namespace UInt64

/-- Return the `i`-th bit of `u` (0-indexed, LSB first). Returns `false` for `i ≥ 64`. -/
@[inline]
def testBit (u : UInt64) (i : Nat) : Bool :=
  if i < 64 then (u >>> UInt64.ofNat i) &&& 1 != 0 else false

end UInt64
