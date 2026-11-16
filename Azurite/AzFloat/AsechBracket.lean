/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcoshBracket

/-!
## The bracket of `asech x`

`asech x = acosh (1/x) = ln ((1 + √((1 − x)(1 + x)))/x)` for `0 < x < 1`.  The reciprocal of a
float is not a float, so the argument of the logarithm is built directly: `asechArg x W` is the
float `⌊⌊1 + ⌊√⌊⌊1 − x⌋ ⌊1 + x⌋⌋⌋⌋ / x⌋` just below `V = (1 + √(1 − x²))/x`
(`y ≤ V ≤ y (1 + 10·2^(−W))`); the product form keeps the relative accuracy of `1 − x` next to
`1`.  `asechBracket x w` is `lnFloorBracket y w` (`AzFloat/LnBracket.lean`) at `W = w + 8`, and
`asechApprox` the pair of `Roundable`s.

Next to `1` the value is `≈ √(2 (1 − x))`, so the Ziv loop of `AzFloat/Asech.lean` starts with
`acoshExtra` more bits (half the leading zero bits of `1 − x`).  For a tiny `x` the value is
`≈ ln (2/x)`, a logarithm like any other.

A rational argument needs none of this: `asech q = acosh (1/q)` with the exact reciprocal
(`AzFloat/AsechRat.lean`).

The proofs are in `Equiv/AsechBracket.lean`.
-/

namespace Azurite.AzFloat

/-- A float just below `(1 + √(1 − x²))/x` for a float `0 < x ≤ 1`, every operation rounded
down at precision `W`. -/
def asechArg (x : AzFloat) (W : Nat) : AzFloat :=
  let dl := (subPrecRound one x W .Floor).1
  let sl := (addPrecRound one x W .Floor).1
  let m := (mulPrecRound dl sl W .Floor).1
  let r := (sqrtPrecRound m W .Floor).1
  let n := (addPrecRound one r W .Floor).1
  (divPrecRound n x W .Floor).1

/-- The bracket of `asech x` at Ziv level `w` for a finite float `0 < x < 1`. -/
def asechBracket (x : AzFloat) (w : Nat) : Encl := lnFloorBracket (asechArg x (w + 8)) w

/-- The bracket of `asech x` as a pair of `Roundable`s. -/
def asechApprox (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  enclApprox false (asechBracket x w)

end Azurite.AzFloat
