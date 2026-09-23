/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzNat.DivRound

namespace Azurite

/-- Divide `a` by `b` rounding according to `mode`. Returns a pair `(v, ord)` where
`v` is the rounded quotient and `ord` records how it relates to the true real value
`a.toInt / b.toInt`: `.lt` if `v < a/b`, `.eq` if equal, `.gt` if greater.

The result sign is `a.sign == b.sign` (positive if `a` and `b` have matching signs).
For a negative result, the rounding mode is "negated" (Floor↔Ceiling swap; the
symmetric modes Down/Up/Nearest are self-dual under sign reversal of the input)
and the ordering is reversed because the inequality flips under negation.

Behavior when `b = 0` is unspecified (delegates to `AzNat.divRound` on a zero
divisor). -/
def AzInt.divRound (a b : AzInt) (mode : RoundingMode) :
    AzInt × Ordering :=
  let resultSign := a.sign == b.sign
  let (q, ord) := a.abs.divRound b.abs (if resultSign then mode else -mode)
  (mkNorm resultSign q, if resultSign then ord else ord.swap)

end Azurite
