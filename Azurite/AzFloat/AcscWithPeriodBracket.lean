/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscBracket
import Azurite.AzFloat.AtanWithPeriodBracket

/-!
## The bracket of `arccsc (x) u / (2π)`

The arccosecant measured in `u`ths of a turn: `acscPeriodApprox neg x en u w` is the pair of
`Roundable`s of the `atanPeriodScale` (the scaling by `u/(2π)`) of `acscBracket x en w`, the
enclosure of `arcsin (1/|x|)`, negated and swapped for `x < 0`.

Like the arcsine in turns, the value is never exponentially close to a nonzero rational one,
and for a huge `x` it is `≈ u/(2πx)` with an irrational factor, enclosed with relative accuracy
(`acscTinyEncl`).  So no exact constant and no orientation are needed.

The proofs are in `Equiv/AcscWithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The bracket of `arccsc (x) u / (2π)` as a pair of `Roundable`s (`neg`: `x < 0`), for a
finite `x` with `|x| > 1` and exponent `en`. -/
def acscPeriodApprox (neg : Bool) (x : AzFloat) (en : Nat) (u : AzNat) (w : Nat) :
    Roundable × Roundable :=
  enclApprox neg (atanPeriodScale (acscBracket x en w) u (w + 64))

end Azurite.AzFloat
