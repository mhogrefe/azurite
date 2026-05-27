import Azurite.AzNat.Add
import Azurite.AzNat.Compare
import Azurite.AzNat.DivRecursiveLimbs
import Azurite.AzNat.Parity
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

end Azurite
