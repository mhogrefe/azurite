import Azurite.AzNat.Add
import Azurite.AzNat.Compare
import Azurite.AzNat.Div
import Azurite.AzNat.Parity
import Azurite.AzNat.Parse
import Azurite.AzNat.ShiftRight
import Azurite.Rounding.Basic

namespace Azurite

/-- Divide `x` by `y` rounding according to `mode`. Returns `(quotient, ord)`
where `ord` records how the rounded value relates to the true real value `x/y`:
`.lt` if quotient < x/y, `.eq` if equal, `.gt` if greater.

Behavior for `y = 0` is unspecified (`divMod x 0 = (0, x)` by convention). -/
def AzNat.divRound (x y : AzNat) (mode : RoundingMode) :
    AzNat × Ordering :=
  let qr := x.divMod y
  let quotient := qr.1
  let remainder := qr.2
  if remainder.limbs.size = 0 then (quotient, .eq)
  else
    match mode with
    | .Floor | .Down => (quotient, .lt)
    | .Ceiling | .Up => (quotient.addUInt64 1, .gt)
    | .Nearest =>
      match Ord.compare (y >>> 1) remainder with
      | .lt => (quotient.addUInt64 1, .gt)
      | .gt => (quotient, .lt)
      | .eq =>
        if y.isEven && quotient.isOdd then
          (quotient.addUInt64 1, .gt)
        else
          (quotient, .lt)

section Examples

private def parse (s : String) : AzNat := (AzNat.parse s.toList).get!

-- Floor / Down: plain divMod quotient.
#guard (parse "13").divRound (parse "4") .Floor == (parse "3", .lt)   -- 13/4 = 3.25
#guard (parse "15").divRound (parse "4") .Down == (parse "3", .lt)    -- 15/4 = 3.75
#guard (parse "12").divRound (parse "4") .Floor == (parse "3", .eq)   -- exact
#guard (parse "0").divRound (parse "5") .Floor == (parse "0", .eq)

-- Ceiling / Up: round away from zero when there's any nonzero remainder.
#guard (parse "12").divRound (parse "4") .Ceiling == (parse "3", .eq)  -- exact
#guard (parse "13").divRound (parse "4") .Ceiling == (parse "4", .gt)
#guard (parse "15").divRound (parse "4") .Up == (parse "4", .gt)

-- Nearest: r < y/2 ⇒ round down; r > y/2 ⇒ round up.
#guard (parse "13").divRound (parse "4") .Nearest == (parse "3", .lt)  -- 13 = 3*4+1
#guard (parse "15").divRound (parse "4") .Nearest == (parse "4", .gt)  -- 15 = 3*4+3

-- Nearest with a tie (y even, x = q*y + y/2): round to even quotient.
#guard (parse "10").divRound (parse "4") .Nearest == (parse "2", .lt)  -- 10/4 = 2.5 → 2
#guard (parse "14").divRound (parse "4") .Nearest == (parse "4", .gt)  -- 14/4 = 3.5 → 4

-- Nearest with odd divisor at the midpoint: y/2 = (y-1)/2, r > y/2 by parity.
#guard (parse "5").divRound (parse "3") .Nearest == (parse "2", .gt)   -- 5/3 ≈ 1.67 → 2

-- A multi-limb example.
#guard (parse "340282366920938463463374607431768211456").divRound (parse "2") .Nearest
  == (parse "170141183460469231731687303715884105728", .eq)

end Examples

end Azurite
