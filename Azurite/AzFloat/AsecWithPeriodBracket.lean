/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecBracket
import Azurite.AzFloat.AcosWithPeriodBracket

/-!
## The bracket of `arcsec (x) u / (2π)`

The arcsecant measured in `u`ths of a turn, `ψ = arccos (1/x) u / (2π) ∈ (0, u/2)` for
`|x| > 1`.  It is the combination `acosPeriodOf` of `AzFloat/AcosWithPeriodBracket.lean` at
`a = 1/|x|`, with enclosures that never form the reciprocal:

* of `arccos (1/|x|)`: `asecBracket false x` (relative accuracy next to `1`);
* of `arcsin (1/|x|) = π/2 − arccos (1/|x|)`: `asecComplement x w`, the complement in `π/2` of
  that bracket, clamped at `0`.  Its accuracy is only absolute, which is all the combination
  needs: for a huge `x` the value is within `2^(−e)` of the float `u/4`, the enclosure
  `u/4 ∓ S` then has `u/4` itself as one end, and the orientation of the Ziv loop
  (`acosPeriodOrientOf`) makes that end the lower one.

`small` is `|x| ≥ 2`, i.e. `1/|x| ≤ 1/2`.

The proofs are in `Equiv/AsecWithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `arcsin (1/|x|) = π/2 − arccos (1/|x|)` for `|x| > 1`, with a nonnegative
lower end and width at most `2^(−w−8)`. -/
def asecComplement (x : AzFloat) (w : Nat) : Encl :=
  enclClamp0 (piShiftEncl true false (asecBracket false x (w + 9)) (w + 72))

/-- The bracket of `arcsec (x) u / (2π)` at Ziv level `w` for a finite float `|x| > 1`; `xpos`:
`x > 0`. -/
def asecPeriodBracket (xpos : Bool) (x : AzFloat) (u : AzNat) (w : Nat) : Encl :=
  acosPeriodOf (le (one <<< AzInt.ofInt 1) x.abs) xpos (fun _ => asecComplement x w)
    (fun _ => asecBracket false x w) (fun _ => asecBracket false x (w + 8)) u w

/-- The bracket of `± arcsec (x) u / (2π)` as a pair of `Roundable`s (`o`: the negative
value). -/
def asecPeriodApprox (o xpos : Bool) (x : AzFloat) (u : AzNat) (w : Nat) :
    Roundable × Roundable :=
  enclApprox o (asecPeriodBracket xpos x u w)

end Azurite.AzFloat
