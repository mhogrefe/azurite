/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.AtanRatWithPeriodBracket
import Azurite.AzRat.Div

/-!
## The bracket of `atan2 (y, x)` for rationals

For nonzero rationals `y`, `x` the quotient `t = |y|/|x|` is a rational, so no division of
floats is needed: `atan2RatBracket t xpos w` encloses `φ = atan2 (|y|, x)` — `arctan t` for
`x > 0` (`xpos`), `π − arctan t` for `x < 0` — with width at most `2^(−w)`, from the enclosure
`atanRatAbsEncl` of the arctangent of `t` (if `t ≤ 1`) or of the rational `1/t` (if `t > 1`):

| | `t ≤ 1` | `t > 1` |
|---|---|---|
| `x > 0` | `arctan t` | `π/2 − arctan (1/t)` |
| `x < 0` | `π − arctan t` | `π/2 + arctan (1/t)` |

Only the first needs relative accuracy, which `atanRatAbsEncl` has (with its tiny-argument
path).  `atan2RatApprox y x w` is the pair of `Roundable`s of the **negative** angle `−φ` for the
Ziv loop of `AzFloat/Atan2Rat.lean` (see `AzFloat/Atan2.lean` for the orientation).

The proofs are in `Equiv/Atan2RatBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The bracket of `atan2 (t, ±1)` at Ziv level `w` for a positive rational `t` (`xpos`: the
sign is `+`). -/
def atan2RatBracket (t : AzRat) (xpos : Bool) (w : Nat) : Encl :=
  if t.num ≤ t.den then
    if xpos then atanRatAbsEncl t w
    else piShiftEncl false false (atanRatAbsEncl t (w + 8)) (w + 72)
  else piShiftEncl true (!xpos) (atanRatAbsEncl t⁻¹ (w + 8)) (w + 72)

/-- The bracket of `−atan2 (|y|, x)` as a pair of `Roundable`s, for nonzero rationals. -/
def atan2RatApprox (y x : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox true (atan2RatBracket (y.abs / x.abs) x.sign w)

end Azurite.AzFloat
