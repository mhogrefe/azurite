/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosBracket

/-!
## The tiny-argument path of `sin x`

**Tiny arguments** (`sinTiny?`): for `|x| < 2^e`, `e ≤ −(max p q + 72)`, `−sin |x|` lies in
`(−|x|, −|x| + |x|³]`, so it is rounded by one test of `roundingPossible` with the exact end
`−|x|` at the open side (in the negated mode, the result negated, for `x > 0`); the Ziv loop
would need about `2|e|` bits to see the side of `x`.  The bracket `sinBracket` is in
`AzFloat/SinCosBracket.lean`.
-/

namespace Azurite.AzFloat

/-- **The tiny-argument path of `sin`** for a finite `x` of sign `s`, exponent `e` and precision
`q` (see the module documentation).  `none` when the argument is not tiny or the test fails. -/
def sinTiny? (s : Bool) (x : AzFloat) (e : AzInt) (q p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let w := max p q + zivGuardBits
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let nx := -x.abs
    let hi := (addPrecRound nx ((x.abs <<< e) <<< e) (w + 8) .Ceiling).1
    let r := roundingPossible (fun P M => setPrecRound nx P M) (fun P M => setPrecRound hi P M) p
      (if s then -mode else mode)
    if s then r.map fun r => (-r.1, r.2.swap) else r
  else none

end Azurite.AzFloat
