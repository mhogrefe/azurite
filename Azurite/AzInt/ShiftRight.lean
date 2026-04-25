import Azurite.AzInt.ShiftRightRound

namespace Azurite.AzInt

/-- Right shift: `z >>> sh`. Rounds toward `−∞` (`Floor`), matching the abstract
`round intSet .Floor (z.toInt / 2^sh)`. For nonnegative `z` this is the plain
magnitude shift; for negative `z` the magnitude is rounded *away* from zero
(equivalent to `−⌈|z|/2^sh⌉`). -/
def shiftRight (z : AzInt) (sh : Nat) : AzInt :=
  (z.shiftRightRound .Floor sh).1

instance : HShiftRight AzInt Nat AzInt := ⟨shiftRight⟩

end Azurite.AzInt
