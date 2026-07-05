import Azurite.AzNat.DivRound
import Azurite.AzNat.ParseBase
import Azurite.AzNat.ToStringBase

namespace Azurite

private def parse (s : String) : AzNat := (AzNat.parse s).get!

private def showDR (qc : AzNat × Ordering) : String × Ordering := (AzNat.toString qc.1, qc.2)

-- Floor / Down: plain divMod quotient.
#guard showDR ((parse "13").divRound (parse "4") .Floor) == ("3", .lt)   -- 13/4 = 3.25
#guard showDR ((parse "15").divRound (parse "4") .Down) == ("3", .lt)    -- 15/4 = 3.75
#guard showDR ((parse "12").divRound (parse "4") .Floor) == ("3", .eq)   -- exact
#guard showDR ((parse "0").divRound (parse "5") .Floor) == ("0", .eq)

-- Ceiling / Up: round away from zero when there's any nonzero remainder.
#guard showDR ((parse "12").divRound (parse "4") .Ceiling) == ("3", .eq)  -- exact
#guard showDR ((parse "13").divRound (parse "4") .Ceiling) == ("4", .gt)
#guard showDR ((parse "15").divRound (parse "4") .Up) == ("4", .gt)

-- Nearest: r < y/2 ⇒ round down; r > y/2 ⇒ round up.
#guard showDR ((parse "13").divRound (parse "4") .Nearest) == ("3", .lt)  -- 13 = 3*4+1
#guard showDR ((parse "15").divRound (parse "4") .Nearest) == ("4", .gt)  -- 15 = 3*4+3

-- Nearest with a tie (y even, x = q*y + y/2): round to even quotient.
#guard showDR ((parse "10").divRound (parse "4") .Nearest) == ("2", .lt)  -- 10/4 = 2.5 → 2
#guard showDR ((parse "14").divRound (parse "4") .Nearest) == ("4", .gt)  -- 14/4 = 3.5 → 4

-- Nearest with odd divisor at the midpoint: y/2 = (y-1)/2, r > y/2 by parity.
#guard showDR ((parse "5").divRound (parse "3") .Nearest) == ("2", .gt)   -- 5/3 ≈ 1.67 → 2

-- A multi-limb example: 2^128 / 2 = 2^127.
#guard showDR ((parse "340282366920938463463374607431768211456").divRound (parse "2") .Nearest)
  == ("170141183460469231731687303715884105728", .eq)

end Azurite
