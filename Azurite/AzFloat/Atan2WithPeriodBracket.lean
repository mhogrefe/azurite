/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.AtanWithPeriodBracket

/-!
## The bracket of `atan2 (y, x) u / (2π)`

The angle of `(x, y)` measured in `u`ths of a turn.  For finite nonzero floats it is `± ψ` with
the sign of `y`, `ψ = atan2 (|y|, x) u / (2π) ∈ (0, u/2)`, and with
`S = arctan (r) u / (2π)`, `r = min (|y|, |x|) / max (|y|, |x|)`:

| | `|y| ≤ |x|` | `|y| > |x|` |
|---|---|---|
| `x > 0` | `ψ = S` | `ψ = u/4 − S` |
| `x < 0` | `ψ = u/2 − S` | `ψ = u/4 + S` |

The quarter and half turns `u/4`, `u/2` are **exact** floats here, so no error of `π` enters
through them: `π` is used once, in `atanPeriodScale`.

* `turnShift c plus S V`: `c ± S` for an exact float `c` and an enclosure `S`.
* `atan2PeriodBracket y x ey ex xpos u w` encloses `ψ`; `atan2PeriodApprox neg` is the pair of
  `Roundable`s of `± ψ` for the Ziv loop of `AzFloat/Atan2WithPeriod.lean`, which runs it in the
  orientation `atan2PeriodOrient` (an exact end of the enclosure must be the lower one).

The proofs are in `Equiv/Atan2WithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- `c + S` (`plus`) or `c − S` for a float `c` and an enclosure `S`, at precision `V`. -/
def turnShift (c : AzFloat) (plus : Bool) (S : Encl) (V : Nat) : Encl :=
  if plus then ((addPrecRound c S.1 V .Floor).1, (addPrecRound c S.2 V .Ceiling).1)
  else ((subPrecRound c S.2 V .Floor).1, (subPrecRound c S.1 V .Ceiling).1)

/-- The bracket of `atan2 (|y|, x) u / (2π)` at Ziv level `w` for finite nonzero `y`, `x` of
exponents `ey`, `ex`; `xpos`: `x > 0`. -/
def atan2PeriodBracket (y x : AzFloat) (ey ex : AzInt) (xpos : Bool) (u : AzNat) (w : Nat) :
    Encl :=
  let ya := y.abs
  let xa := x.abs
  let V := w + 72
  if le ya xa = true then
    if xpos then atanPeriodScale (atanQuotRel ya xa (ey - ex + AzInt.ofInt 1) w) u V
    else
      turnShift (ofAzNat u <<< AzInt.ofInt (-1)) false
        (atanPeriodScale (atanQuot ya xa (w + 8)) u V) V
  else
    turnShift (ofAzNat u <<< AzInt.ofInt (-2)) (!xpos)
      (atanPeriodScale (atanQuot xa ya (w + 8)) u V) V

/-- The orientation of the Ziv loop: `true` when it must run on the **negative** value `−ψ`.
`roundingPossible` decides a value in `(l, h]`, so an end of the enclosure that can be an exact
float must be the lower one.  For a very unequal pair, `ψ = u/4 − S` and `ψ = u/2 − S` lie just
below the exact floats `u/4`, `u/2` (negative orientation: `−u/4`, `−u/2` are lower ends), and
`ψ = u/4 + S` just above `u/4` (positive orientation).  `ψ = S` is never near an exact end. -/
def atan2PeriodOrient (y x : AzFloat) (xpos : Bool) : Bool := le y.abs x.abs || xpos

/-- The bracket of `± atan2 (|y|, x) u / (2π)` as a pair of `Roundable`s (`neg`: the negative
value). -/
def atan2PeriodApprox (neg : Bool) (y x : AzFloat) (ey ex : AzInt) (xpos : Bool) (u : AzNat)
    (w : Nat) : Roundable × Roundable :=
  enclApprox neg (atan2PeriodBracket y x ey ex xpos u w)

end Azurite.AzFloat
