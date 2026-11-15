/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2RatBracket
import Azurite.AzFloat.Atan2WithPeriodBracket

/-!
## The bracket of `atan2 (y, x) u / (2π)` for rationals

For nonzero rationals `y`, `x` with the rational quotient `t = |y|/|x|`, the value is `± ψ` with
the sign of `y`, and with `S = arctan (s) u / (2π)`, `s = t` or `1/t` in `(0, 1]`:

| | `t ≤ 1` | `t > 1` |
|---|---|---|
| `x > 0` | `ψ = S` | `ψ = u/4 − S` |
| `x < 0` | `ψ = u/2 − S` | `ψ = u/4 + S` |

`S` is `atanPeriodScale` of `atanRatAbsEncl` (no float division); the quarter and half turns are
exact floats (`turnShift`).  `atan2RatPeriodOrient` is the orientation of the Ziv loop, as in
`AzFloat/Atan2WithPeriodBracket.lean`: for a very large or very small `t` the value is next to
the float `u/4` or `u/2`, which must be the lower end of the enclosure.

The proofs are in `Equiv/Atan2RatWithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The bracket of `atan2 (t, ±1) u / (2π)` at Ziv level `w` for a positive rational `t`
(`xpos`: the sign is `+`). -/
def atan2RatPeriodBracket (t : AzRat) (xpos : Bool) (u : AzNat) (w : Nat) : Encl :=
  let V := w + 72
  if t.num ≤ t.den then
    if xpos then atanPeriodScale (atanRatAbsEncl t w) u V
    else
      turnShift (ofAzNat u <<< AzInt.ofInt (-1)) false
        (atanPeriodScale (atanRatAbsEncl t (w + 8)) u V) V
  else
    turnShift (ofAzNat u <<< AzInt.ofInt (-2)) (!xpos)
      (atanPeriodScale (atanRatAbsEncl t⁻¹ (w + 8)) u V) V

/-- The orientation of the Ziv loop: `true` when it runs on the negative value. -/
def atan2RatPeriodOrient (t : AzRat) (xpos : Bool) : Bool := decide (t.num ≤ t.den) || xpos

/-- The bracket of `± atan2 (|y|, x) u / (2π)` as a pair of `Roundable`s, for nonzero rationals
(`neg`: the negative value). -/
def atan2RatPeriodApprox (neg : Bool) (y x : AzRat) (u : AzNat) (w : Nat) :
    Roundable × Roundable :=
  enclApprox neg (atan2RatPeriodBracket (y.abs / x.abs) x.sign u w)

end Azurite.AzFloat
