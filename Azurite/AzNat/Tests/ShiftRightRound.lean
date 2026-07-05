import Azurite.AzNat.ParseBase
import Azurite.AzNat.ShiftRightRound
import Azurite.AzNat.ToStringBase

namespace Azurite

private def parse (s : String) : AzNat := (AzNat.parse s).get!

private def showSR (qc : AzNat × Ordering) : String × Ordering := (AzNat.toString qc.1, qc.2)

-- Floor / Down: plain shift right.
#guard showSR ((parse "13").shiftRightRound .Floor 2) == ("3", .lt)   -- 13/4 = 3.25
#guard showSR ((parse "15").shiftRightRound .Down 2) == ("3", .lt)    -- 15/4 = 3.75
#guard showSR ((parse "0").shiftRightRound .Floor 10) == ("0", .eq)
#guard showSR ((parse "12").shiftRightRound .Floor 2) == ("3", .eq)   -- exact

-- Ceiling / Up: round away from zero when there's any nonzero remainder.
#guard showSR ((parse "12").shiftRightRound .Ceiling 2) == ("3", .eq)  -- exact
#guard showSR ((parse "13").shiftRightRound .Ceiling 2) == ("4", .gt)
#guard showSR ((parse "15").shiftRightRound .Up 2) == ("4", .gt)
#guard showSR ((parse "0").shiftRightRound .Ceiling 10) == ("0", .eq)

-- Nearest: bit (sh-1) = 0 ⇒ round down.
#guard showSR ((parse "12").shiftRightRound .Nearest 2) == ("3", .eq)  -- 12 = 1100, exact
#guard showSR ((parse "13").shiftRightRound .Nearest 2) == ("3", .lt)  -- 13 = 1101, bit1 = 0

-- Nearest: bit (sh-1) = 1 and not a multiple of 2^(sh-1) ⇒ round up.
#guard showSR ((parse "15").shiftRightRound .Nearest 2) == ("4", .gt)  -- 15 = 1111
#guard showSR ((parse "11").shiftRightRound .Nearest 2) == ("3", .gt)  -- 11/4 = 2.75 → 3

-- Nearest with a tie (n/2^sh = x.5): round to even.
#guard showSR ((parse "5").shiftRightRound .Nearest 1) == ("2", .lt)   -- 5/2 = 2.5 → 2
#guard showSR ((parse "7").shiftRightRound .Nearest 1) == ("4", .gt)   -- 7/2 = 3.5 → 4
#guard showSR ((parse "14").shiftRightRound .Nearest 2) == ("4", .gt)  -- 14/4 = 3.5 → 4
#guard showSR ((parse "10").shiftRightRound .Nearest 2) == ("2", .lt)  -- 10/4 = 2.5 → 2

-- Nearest with sh = 0 is the identity.
#guard showSR ((parse "123").shiftRightRound .Nearest 0) == ("123", .eq)
#guard showSR ((parse "0").shiftRightRound .Nearest 0) == ("0", .eq)

-- A multi-limb example: 2^128 shifted right by 64 should give 2^64.
#guard showSR ((parse "340282366920938463463374607431768211456").shiftRightRound .Nearest 64)
  == ("18446744073709551616", .eq)
#guard showSR ((parse "340282366920938463463374607431768211456").shiftRightRound .Ceiling 64)
  == ("18446744073709551616", .eq)

end Azurite
