/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanBracket

/-!
## The bracket of `sec x`

`secBracket x ex w` encloses `sec x = 1 / cos x` for a finite float `x` of exponent `ex` at Ziv
level `w`: the quotient step `tanOfSinCos` (`AzFloat/TanBracket.lean`) applied to the exact
numerator `1` and the bracket `cosBracket x ex w` of the cosine alone — two directed divisions at
`w + 12` bits, the sign of the cosine carried over — or the dummy bracket `[−1, 1]` (never
accepted by `roundingPossible`) while the bracket of `cos x` contains `0`.  The secant is even,
so `secApprox` needs no sign.

**Tiny arguments** (`secTiny?`): for `|x| < 2^e`, `e ≤ −(p + 72)`, `sec x` lies in
`(1, 1 + 2^(2e)]` (from `cos x ≥ 1 − x²/2`), so it is rounded from the bracket
`[1, ⌈1 + 2^(2e)⌉_{p+72}]` by one test of `roundingPossible`, the exact end `1` at the open
side.  Nothing is computed from the argument.
-/

namespace Azurite.AzFloat

/-- The bracket of `sec x` at Ziv level `w` for a finite `x` of exponent `ex`, or the dummy
bracket `[−1, 1]` when the bracket of `cos x` contains `0`. -/
def secBracket (x : AzFloat) (ex : AzInt) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (Encl.exact one, cosBracket x ex w) (w + 12)

/-- `secBracket` as a pair of `Roundable`s for the Ziv loop. -/
def secApprox (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  negSwapApprox false (secBracket x ex w)

/-- **The tiny-argument path of `sec`** for an argument below `2^e` in magnitude (see the module
documentation).  `none` when the argument is not tiny or the test fails. -/
def secTiny? (e : AzInt) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let w := p + zivGuardBits
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let hi := (addPrecRound one ((one <<< e) <<< e) (w + 8) .Ceiling).1
    roundingPossible (fun P M => setPrecRound one P M) (fun P M => setPrecRound hi P M) p mode
  else none

end Azurite.AzFloat
