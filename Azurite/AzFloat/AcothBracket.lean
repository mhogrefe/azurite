/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscBracket
import Azurite.AzFloat.AcschBracket
import Azurite.AzFloat.AtanhBracket

/-!
## The bracket of `acoth x`

`acoth x = atanh (1/x)`, odd, for `|x| > 1`.  For `a = |x| > 1`,

  `acoth a = (1/2) ln ((a + 1)/(a − 1))`,

so the bracket is half of `lnFloorBracket` at `atanhArg ⌊a + 1⌋ ⌈a − 1⌉` (the float just below
the quotient, `AzFloat/AtanhBracket.lean`); `a − 1` keeps its relative accuracy next to `1`,
where the value is large.

**Huge arguments.**  For a huge `a` the value is `≈ 1/a`, and `y ≤ atanh y ≤ y + y³` at
`y = 1/a` — the bounds of the arcsine — so for an exponent `e` with `2e ≥ w + 16` the bracket
is `acscTinyEncl a w` (`AzFloat/AcscBracket.lean`): two directed divisions.  Its **lower** end
is the correctly rounded `1/a`, exactly `1/a` when `a` is a power of two, the case in which
`acoth a` is exponentially close to a float, from above.  So `acothApprox` brackets
`acoth |x|` itself, and the Ziv loop of `AzFloat/Acoth.lean` always runs on the absolute value.

A rational argument needs none of this: `acoth q = atanh (1/q)` with the exact reciprocal
(`AzFloat/AcothRat.lean`).

The proofs are in `Equiv/AcothBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The bracket of `acoth a = atanh (1/a)` at Ziv level `w` for a finite float `a > 1` of
exponent `e`. -/
def acothBracket (a : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  if w + 16 ≤ 2 * e.abs.toNat then acscTinyEncl a w
  else
    let W := w + 8
    atanhOfArg
      (atanhArg (addPrecRound a one W .Floor).1 (subPrecRound a one W .Ceiling).1 W) w

/-- The bracket of `acoth |x|` as a pair of `Roundable`s. -/
def acothApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox false (acothBracket x.abs e w)

end Azurite.AzFloat
