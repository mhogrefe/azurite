import Azurite.AzNat.Add
import Azurite.AzNat.IsMultipleOfPow2
import Azurite.AzNat.Parity
import Azurite.AzNat.Parse
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.TestBit
import Azurite.Rounding.Basic

namespace Azurite

/-- Shift `n` right by `sh` bits, rounding the result according to `mode`. -/
def AzNat.shiftRightRound (n : AzNat) (mode : RoundingMode) (sh : Nat) : AzNat :=
  match mode with
  | .Floor | .Down => n.shiftRight sh
  | .Ceiling | .Up =>
    if n.isMultipleOfPow2 sh then n.shiftRight sh
    else (n.shiftRight sh).addUInt64 1
  | .Nearest =>
    if sh = 0 then n
    else if n.testBit (sh - 1) then
      if n.isMultipleOfPow2 (sh - 1) then
        let shifted := n.shiftRight sh
        if shifted.isOdd then shifted.addUInt64 1 else shifted
      else
        (n.shiftRight sh).addUInt64 1
    else
      n.shiftRight sh

section Examples

private def parse (s : String) : AzNat := (AzNat.parse s.toList).get!

-- Floor / Down: plain shift right.
#guard (parse "13").shiftRightRound .Floor 2 == parse "3"
#guard (parse "15").shiftRightRound .Down 2 == parse "3"
#guard (parse "0").shiftRightRound .Floor 10 == parse "0"

-- Ceiling / Up: round away from zero when there's any nonzero remainder.
#guard (parse "12").shiftRightRound .Ceiling 2 == parse "3"  -- exact
#guard (parse "13").shiftRightRound .Ceiling 2 == parse "4"
#guard (parse "15").shiftRightRound .Up 2 == parse "4"
#guard (parse "0").shiftRightRound .Ceiling 10 == parse "0"

-- Nearest: bit (sh-1) = 0 ⇒ round down.
#guard (parse "12").shiftRightRound .Nearest 2 == parse "3"  -- 12 = 1100
#guard (parse "13").shiftRightRound .Nearest 2 == parse "3"  -- 13 = 1101, bit1 = 0

-- Nearest: bit (sh-1) = 1 and not a multiple of 2^(sh-1) ⇒ round up.
#guard (parse "15").shiftRightRound .Nearest 2 == parse "4"  -- 15 = 1111
#guard (parse "11").shiftRightRound .Nearest 2 == parse "3"  -- 11 = 1011, bit1=1 but
                                                             -- 11/4 = 2.75, rounds to 3

-- Nearest with a tie (n/2^sh = x.5): round to even.
#guard (parse "5").shiftRightRound .Nearest 1 == parse "2"   -- 5/2 = 2.5 → 2
#guard (parse "7").shiftRightRound .Nearest 1 == parse "4"   -- 7/2 = 3.5 → 4
#guard (parse "14").shiftRightRound .Nearest 2 == parse "4"  -- 14/4 = 3.5 → 4
#guard (parse "10").shiftRightRound .Nearest 2 == parse "2"  -- 10/4 = 2.5 → 2

-- Nearest with sh = 0 is the identity.
#guard (parse "123").shiftRightRound .Nearest 0 == parse "123"
#guard (parse "0").shiftRightRound .Nearest 0 == parse "0"

-- A multi-limb example: 2^128 shifted right by 64 should give 2^64.
#guard (parse "340282366920938463463374607431768211456").shiftRightRound .Nearest 64
  == parse "18446744073709551616"
#guard (parse "340282366920938463463374607431768211456").shiftRightRound .Ceiling 64
  == parse "18446744073709551616"

end Examples

end Azurite
