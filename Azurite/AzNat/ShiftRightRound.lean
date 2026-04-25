import Azurite.AzNat.Add
import Azurite.AzNat.IsMultipleOfPow2
import Azurite.AzNat.Parity
import Azurite.AzNat.Parse
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

section Examples

private def parse (s : String) : AzNat := (AzNat.parse s.toList).get!

-- Floor / Down: plain shift right.
#guard (parse "13").shiftRightRound .Floor 2 == (parse "3", .lt)   -- 13/4 = 3.25
#guard (parse "15").shiftRightRound .Down 2 == (parse "3", .lt)    -- 15/4 = 3.75
#guard (parse "0").shiftRightRound .Floor 10 == (parse "0", .eq)
#guard (parse "12").shiftRightRound .Floor 2 == (parse "3", .eq)   -- exact

-- Ceiling / Up: round away from zero when there's any nonzero remainder.
#guard (parse "12").shiftRightRound .Ceiling 2 == (parse "3", .eq)  -- exact
#guard (parse "13").shiftRightRound .Ceiling 2 == (parse "4", .gt)
#guard (parse "15").shiftRightRound .Up 2 == (parse "4", .gt)
#guard (parse "0").shiftRightRound .Ceiling 10 == (parse "0", .eq)

-- Nearest: bit (sh-1) = 0 ⇒ round down.
#guard (parse "12").shiftRightRound .Nearest 2 == (parse "3", .eq)  -- 12 = 1100, exact
#guard (parse "13").shiftRightRound .Nearest 2 == (parse "3", .lt)  -- 13 = 1101, bit1 = 0

-- Nearest: bit (sh-1) = 1 and not a multiple of 2^(sh-1) ⇒ round up.
#guard (parse "15").shiftRightRound .Nearest 2 == (parse "4", .gt)  -- 15 = 1111
#guard (parse "11").shiftRightRound .Nearest 2 == (parse "3", .gt)  -- 11/4 = 2.75 → 3

-- Nearest with a tie (n/2^sh = x.5): round to even.
#guard (parse "5").shiftRightRound .Nearest 1 == (parse "2", .lt)   -- 5/2 = 2.5 → 2
#guard (parse "7").shiftRightRound .Nearest 1 == (parse "4", .gt)   -- 7/2 = 3.5 → 4
#guard (parse "14").shiftRightRound .Nearest 2 == (parse "4", .gt)  -- 14/4 = 3.5 → 4
#guard (parse "10").shiftRightRound .Nearest 2 == (parse "2", .lt)  -- 10/4 = 2.5 → 2

-- Nearest with sh = 0 is the identity.
#guard (parse "123").shiftRightRound .Nearest 0 == (parse "123", .eq)
#guard (parse "0").shiftRightRound .Nearest 0 == (parse "0", .eq)

-- A multi-limb example: 2^128 shifted right by 64 should give 2^64.
#guard (parse "340282366920938463463374607431768211456").shiftRightRound .Nearest 64
  == (parse "18446744073709551616", .eq)
#guard (parse "340282366920938463463374607431768211456").shiftRightRound .Ceiling 64
  == (parse "18446744073709551616", .eq)

end Examples

end Azurite
