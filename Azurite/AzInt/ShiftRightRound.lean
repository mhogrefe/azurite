/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzNat.ShiftRightRound

namespace Azurite

/-- Shift `z` right by `sh` bits, rounding according to `mode`. Returns a pair
`(v, ord)` where `v` is the rounded value and `ord` records how it relates to
the true value `z.toInt / 2^sh`: `.lt` if `v < z/2^sh`, `.eq` if equal, `.gt`
if greater.

For nonnegative `z`, this delegates to `AzNat.shiftRightRound` directly. For
negative `z`, the mode is "negated" (Floor↔Ceiling swap; Down/Up/Nearest are
self-dual under sign reversal) and applied to the magnitude; the resulting
ordering is reversed since the inequality flips under negation. -/
def AzInt.shiftRightRound (z : AzInt) (mode : RoundingMode) (sh : Nat) :
    AzInt × Ordering :=
  let (a, ord) := z.abs.shiftRightRound (if z.sign then mode else -mode) sh
  (mkNorm z.sign a, if z.sign then ord else ord.swap)

end Azurite
