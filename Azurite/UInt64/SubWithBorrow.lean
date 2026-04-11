namespace UInt64

/-- Subtracts two 64-bit unsigned integers along with a boolean borrow, returning the difference
and the new borrow out. -/
@[inline]
def subWithBorrow (a b : UInt64) (c : Bool) : UInt64 × Bool :=
  let diff1 := a - b
  let c1 := a < b
  let c_val : UInt64 := if c then 1 else 0
  let diff2 := diff1 - c_val
  let c2 := diff1 < c_val
  (diff2, c1 || c2)

end UInt64
