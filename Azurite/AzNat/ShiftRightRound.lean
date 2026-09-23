/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Add
import Azurite.AzNat.IsMultipleOfPow2
import Azurite.AzNat.Parity
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.TestBit
import Azurite.Rounding.Basic

namespace Azurite

/-- Shift `n` right by `sh` bits, rounding according to `mode`.
Returns a pair `(v, ord)` where `v` is the rounded value and `ord` records how
it relates to the true value `n.toNat / 2^sh`:
`.lt` if `v < n/2^sh`, `.eq` if `v = n/2^sh`, `.gt` if `v > n/2^sh`. -/
def AzNat.shiftRightRound (n : AzNat) (mode : RoundingMode) (sh : Nat) :
    AzNat × Ordering :=
  match mode with
  | .Floor =>
    (n.shiftRight sh, if n.isMultipleOfPow2 sh then .eq else .lt)
  | .Down =>
    (n.shiftRight sh, if n.isMultipleOfPow2 sh then .eq else .lt)
  | .Ceiling =>
    if n.isMultipleOfPow2 sh then (n.shiftRight sh, .eq)
    else ((n.shiftRight sh).addUInt64 1, .gt)
  | .Up =>
    if n.isMultipleOfPow2 sh then (n.shiftRight sh, .eq)
    else ((n.shiftRight sh).addUInt64 1, .gt)
  | .Nearest =>
    if sh = 0 then (n, .eq)
    else if n.testBit (sh - 1) then
      if n.isMultipleOfPow2 (sh - 1) then
        let shifted := n.shiftRight sh
        if shifted.isOdd then (shifted.addUInt64 1, .gt) else (shifted, .lt)
      else
        ((n.shiftRight sh).addUInt64 1, .gt)
    else
      (n.shiftRight sh, if n.isMultipleOfPow2 sh then .eq else .lt)

end Azurite
