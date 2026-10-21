/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Compare
import Azurite.AzNat.Pow
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Size

/-!
# Logarithms of naturals in a general base

`floorLogBase b n`, `ceilingLogBase b n` and `checkedLogBase b n` are `⌊log_b n⌋`, `⌈log_b n⌉`
and the exact exponent when `n = b^e` (`none` for `b ≤ 1` or `n = 0`; the checked one is
`none` when `n` is not a power of `b`).

The floor is found by a binary search on the exponent (`floorLogSearch`, maintaining
`b^lo ≤ n < b^hi`), which only ever compares a power `b.pow e` with `n`.  A `Float` estimate of
`log₂ n / log₂ b` from the bit lengths and the top 64 bits of each (`approxLog2`) proposes a
bracket of width three around the estimate; the bracket is verified by two power comparisons
and used if valid, so a wrong estimate costs only the fallback to the bracket `[0, size n)`,
never correctness.  The ceiling and the checked logarithm are the floor plus one exactness test.
-/

namespace Azurite.AzNat

/-- A `Float` approximation of `log₂ m` for `m ≠ 0`: the top 64 bits as a `Float`, plus the
number of bits below them. -/
def approxLog2 (m : AzNat) : Float :=
  if m.size ≤ 64 then Float.log2 (m.limbs.getD 0 0).toFloat
  else Float.log2 ((m >>> (m.size - 64)).limbs.getD 0 0).toFloat + (m.size - 64).toFloat

/-- A `Float` estimate of `⌊log_b n⌋` (any value is acceptable: the bracket built from it is
verified before use). -/
def estimateLogBase (b n : AzNat) : Nat :=
  (approxLog2 n / approxLog2 b).toUInt64.toNat

/-- Binary search for `⌊log_b n⌋` inside `[lo, hi)`, maintaining `b^lo ≤ n < b^hi`. -/
def floorLogSearch (b n : AzNat) (lo hi : Nat) : Nat :=
  if _h : lo + 1 < hi then
    let mid := (lo + hi) / 2
    if b.pow mid ≤ n then floorLogSearch b n mid hi else floorLogSearch b n lo mid
  else lo
  termination_by hi - lo
  decreasing_by all_goals omega

/-- `⌊log_b n⌋` (`none` for `b ≤ 1` or `n = 0`). -/
def floorLogBase (b n : AzNat) : Option Nat :=
  if b.size ≤ 1 ∨ n = 0 then none
  else
    let e := estimateLogBase b n
    let lo := e - 1
    let hi := e + 2
    if b.pow lo ≤ n ∧ n < b.pow hi then some (floorLogSearch b n lo hi)
    else some (floorLogSearch b n 0 n.size)

/-- `⌈log_b n⌉` (`none` for `b ≤ 1` or `n = 0`). -/
def ceilingLogBase (b n : AzNat) : Option Nat :=
  (floorLogBase b n).map fun e => if b.pow e = n then e else e + 1

/-- `some e` if `n = b^e`, `none` otherwise (and for `b ≤ 1`). -/
def checkedLogBase (b n : AzNat) : Option Nat :=
  (floorLogBase b n).bind fun e => if b.pow e = n then some e else none

end Azurite.AzNat
