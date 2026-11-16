/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinBracket
import Azurite.AzFloat.AtanWithPeriodBracket

/-!
## The bracket of `arcsin (x) u / (2π)`

The arcsine measured in `u`ths of a turn.

* `asinAbsEncl x ex w` is an enclosure of `arcsin |x|` with a nonnegative lower end and width at
  most `2^(−w)`: `asinBracket x ex w`, except for a **tiny** argument (`|x| < 2^ex`,
  `2 ex ≤ −(w + 8)`), where it is `[|x|, |x| + |x| 2^(2 ex)]` — from
  `x < arcsin x ≤ x + x³` — at a cost independent of the exponent.
* `asinPeriodApprox neg x ex u w` is the pair of `Roundable`s of its `atanPeriodScale` (the
  scaling by `u/(2π)`) for the Ziv loop of `AzFloat/AsinWithPeriod.lean`, negated and swapped
  for `x < 0`.

Unlike the arctangent, the arcsine in turns is never exponentially close to a rational value:
next to `±1` the distance to the quarter turn is of the order of `√(1 − |x|)`, bounded below
through the precision of `x`.  So no exact constant and no orientation are needed here.

The proofs are in `Equiv/AsinWithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `arcsin |x|` with a nonnegative lower end, for a finite `x` of exponent
`ex ≤ 0` at level `w`: `[|x|, |x| + |x| 2^(2 ex)]` for a tiny argument, `asinBracket`
otherwise. -/
def asinAbsEncl (x : AzFloat) (ex : AzInt) (w : Nat) : Encl :=
  if ex.sign = false ∧ w + 8 ≤ 2 * ex.abs.toNat then
    let xa := x.abs
    (xa, (addPrecRound xa ((xa <<< ex) <<< ex) (w + 64) .Ceiling).1)
  else asinBracket x ex w

/-- The bracket of `arcsin (x) u / (2π)` as a pair of `Roundable`s (`neg`: `x < 0`). -/
def asinPeriodApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (u : AzNat) (w : Nat) :
    Roundable × Roundable :=
  enclApprox neg (atanPeriodScale (asinAbsEncl x ex w) u (w + 64))

end Azurite.AzFloat
