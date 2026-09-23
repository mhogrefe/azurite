/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Basic
import Azurite.AzInt.DivRound
import Azurite.AzInt.Conversion

/-!
# Rounding `AzRat` to `AzInt`

`AzRat.round q mode` rounds the rational `q` to an `AzInt` according to `mode`, by
dividing the signed numerator `(sign q) · num` by the (positive) denominator `den`
with `AzInt.divRound`. The numerator carries `q`'s sign via `AzInt.mkNorm` and the
denominator is lifted with `AzNat.toAzInt`.

The result is a pair `(v, ord)`: the rounded `AzInt` `v` and an `Ordering` `ord`
recording how `v` relates to the true value `toRat q` (`.lt` if `v < toRat q`, `.eq` if
equal, `.gt` if greater), inherited directly from `AzInt.divRound`.
-/

namespace Azurite.AzRat

/-- Round `q : AzRat` to an `AzInt` according to `mode`. Returns `(v, ord)` where `v` is the
rounded value and `ord` records how `v` compares to the true value `toRat q`. -/
def round (q : AzRat) (mode : RoundingMode) : AzInt × Ordering :=
  AzInt.divRound (AzInt.mkNorm q.sign q.num) q.den.toAzInt mode

end Azurite.AzRat
