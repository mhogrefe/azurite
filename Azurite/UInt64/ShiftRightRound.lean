import Azurite.UInt64.IsMultipleOfPow2
import Azurite.UInt64.TestBit
import Azurite.Rounding.Basic

namespace UInt64

/-- Shift `u` right by `sh` bits, yielding `0` for `sh ≥ 64`. Used as the
semantically-correct primitive (the raw `>>>` reduces `sh` mod 64). -/
@[inline]
def shiftRightSat (u : UInt64) (sh : Nat) : UInt64 :=
  if sh < 64 then u >>> UInt64.ofNat sh else 0

/-- Shift `u` right by `sh` bits, rounding the result according to `mode`. -/
def shiftRightRound (u : UInt64) (mode : Azurite.RoundingMode) (sh : Nat) : UInt64 :=
  match mode with
  | .Floor | .Down => shiftRightSat u sh
  | .Ceiling | .Up =>
    if u.isMultipleOfPow2 sh then shiftRightSat u sh
    else shiftRightSat u sh + 1
  | .Nearest =>
    if sh = 0 then u
    else if u.testBit (sh - 1) then
      if u.isMultipleOfPow2 (sh - 1) then
        let shifted := shiftRightSat u sh
        if shifted &&& 1 == 1 then shifted + 1 else shifted
      else
        shiftRightSat u sh + 1
    else
      shiftRightSat u sh

end UInt64
