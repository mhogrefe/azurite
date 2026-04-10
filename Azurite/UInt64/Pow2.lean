namespace UInt64

/-- Test whether a `UInt64` is a positive power of two (i.e. `2^k` for some `k`).
Returns `false` for `0`. Uses the classical bit trick `u &&& (u - 1) == 0` for nonzero `u`. -/
@[inline]
def isPowerOfTwo (u : UInt64) : Bool := u != 0 && (u &&& (u - 1) == 0)

end UInt64
