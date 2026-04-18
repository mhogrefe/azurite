namespace UInt64

/-- Test whether `u` is a multiple of `2 ^ k`, i.e. whether its `k` least-significant
bits are all zero. For `k ≥ 64`, only `0` qualifies. -/
@[inline]
def isMultipleOfPow2 (u : UInt64) (k : Nat) : Bool :=
  if k < 64 then u &&& ((1 <<< UInt64.ofNat k) - 1) == 0
  else u == 0

end UInt64
