/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.IsMultipleOfPow2
import Azurite.UInt64.TestBit
import Azurite.Rounding.Basic

namespace UInt64

/-- Shift `u` right by `sh` bits, yielding `0` for `sh ≥ 64`. Used as the
semantically-correct primitive (the raw `>>>` reduces `sh` mod 64). -/
@[inline]
def shiftRightSat (u : UInt64) (sh : Nat) : UInt64 :=
  if sh < 64 then u >>> UInt64.ofNat sh else 0

/-- Shift `u` right by `sh` bits, rounding according to `mode`.
Returns a pair `(v, ord)` where `v` is the rounded value and `ord` records how
it relates to the true value `u.toNat / 2^sh`:
`.lt` if `v < u/2^sh`, `.eq` if `v = u/2^sh`, `.gt` if `v > u/2^sh`. -/
def shiftRightRound (u : UInt64) (mode : Azurite.RoundingMode) (sh : Nat) :
    UInt64 × Ordering :=
  match mode with
  | .Floor =>
    (shiftRightSat u sh, if u.isMultipleOfPow2 sh then .eq else .lt)
  | .Down =>
    (shiftRightSat u sh, if u.isMultipleOfPow2 sh then .eq else .lt)
  | .Ceiling =>
    if u.isMultipleOfPow2 sh then (shiftRightSat u sh, .eq)
    else (shiftRightSat u sh + 1, .gt)
  | .Up =>
    if u.isMultipleOfPow2 sh then (shiftRightSat u sh, .eq)
    else (shiftRightSat u sh + 1, .gt)
  | .Nearest =>
    if sh = 0 then (u, .eq)
    else if u.testBit (sh - 1) then
      if u.isMultipleOfPow2 (sh - 1) then
        let shifted := shiftRightSat u sh
        if shifted &&& 1 == 1 then (shifted + 1, .gt) else (shifted, .lt)
      else
        (shiftRightSat u sh + 1, .gt)
    else
      (shiftRightSat u sh, if u.isMultipleOfPow2 sh then .eq else .lt)

end UInt64
