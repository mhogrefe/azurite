import Azurite.AzInt.Add
import Azurite.AzInt.ToString
import Azurite.AzNat.Pow

/-!
# Exponentiation for AzInt

`a ^ n` for sign-magnitude integers, **delegating the magnitude to `AzNat`'s sliding-window
exponentiation** (`AzNat.pow`). This is the `npow` of the `CommRing` instance, so
`(z : AzInt) ^ n` runs the same fast algorithm and `z.pow n = z ^ n` definitionally.

The sign of `z ^ n` is `z.sign` unless `n` is even — then the result is nonnegative; equivalently
it is negative exactly when `z` is negative and `n` is odd. `mkNorm` fixes up the sign in the
degenerate case where the magnitude is `0`.

## Main definitions

- `Azurite.AzInt.pow z n`.

The `ℤ`-equivalence proofs live in `Azurite.AzInt.Equiv.Pow` (`toInt_pow`, `ofInt_pow`).
-/

namespace Azurite.AzInt

/-- Exponentiation for `AzInt`: the magnitude is `AzNat`'s (sliding-window) power of `z.abs`, and
the result is nonnegative unless `z` is negative and `n` is odd. This is the `CommRing`'s `npow`,
so it is definitionally equal to `z ^ n`. -/
def pow (z : AzInt) (n : ℕ) : AzInt :=
  mkNorm (z.sign || (n % 2 == 0)) (z.abs.pow n)

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

#guard toString ((Int64.toAzInt 2).pow 10) == "1024"
#guard toString ((Int64.toAzInt (-2)).pow 10) == "1024"
#guard toString ((Int64.toAzInt (-2)).pow 11) == "-2048"
#guard toString ((Int64.toAzInt (-3)).pow 3) == "-27"
#guard toString ((Int64.toAzInt (-7)).pow 2) == "49"
#guard toString ((Int64.toAzInt (-5)).pow 0) == "1"
#guard toString ((Int64.toAzInt 0).pow 5) == "0"
#guard toString ((Int64.toAzInt 0).pow 0) == "1"
#guard toString ((Int64.toAzInt (-2)).pow 30) == "1073741824"

end Tests

end Azurite.AzInt
