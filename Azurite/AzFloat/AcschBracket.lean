/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotBracket
import Azurite.AzFloat.AsinhBracket

/-!
## The bracket of `acsch x`

`acsch x = asinh (1/x)`, odd.  For `a = |x| > 0`,

  `acsch a = ln ((1 + √(1 + a²))/a)`,

the argument of the logarithm being built directly (the reciprocal of a float is not a float):
`acschArg a W` is the float `⌊⌊1 + ⌊√⌊1 + ⌊a²⌋⌋⌋⌋ / a⌋` just below `V = (1 + √(1 + a²))/a`
(`y ≤ V ≤ y (1 + 8·2^(−W))`), and the bracket is `lnFloorBracket y w` at `W = w + 8`.

**Huge arguments.**  For a huge `a` the value is `≈ 1/a`, and `y − y³ ≤ asinh y ≤ y` at
`y = 1/a` — the bounds of the arctangent — so for an exponent `e` with `2e ≥ w + 16` the bracket
is `acotTinyEncl a w` (`AzFloat/AcotBracket.lean`): two directed divisions.  Its **upper** end
is the correctly rounded `1/a`, exactly `1/a` when `a` is a power of two, the case in which
`acsch a` is exponentially close to a float, from below.  So `acschApprox` is the pair of
`Roundable`s of the **negated** enclosure: the Ziv loop of `AzFloat/Acsch.lean` runs on
`−acsch |x|`, with the exact end at the open side.

A rational argument needs none of this: `acsch q = asinh (1/q)` with the exact reciprocal
(`AzFloat/AcschRat.lean`).

The proofs are in `Equiv/AcschBracket.lean`.
-/

namespace Azurite.AzFloat

/-- A float just below `(1 + √(1 + a²))/a` for a float `a > 0`, every operation rounded down
at precision `W`. -/
def acschArg (a : AzFloat) (W : Nat) : AzFloat :=
  let m := (mulPrecRound a a W .Floor).1
  let s := (addPrecRound one m W .Floor).1
  let r := (sqrtPrecRound s W .Floor).1
  let n := (addPrecRound one r W .Floor).1
  (divPrecRound n a W .Floor).1

/-- The bracket of `acsch a = asinh (1/a)` at Ziv level `w` for a positive finite float `a` of
exponent `e`. -/
def acschBracket (a : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  if e.sign = true ∧ e.abs.toNat ≠ 0 ∧ w + 16 ≤ 2 * e.abs.toNat then acotTinyEncl a w
  else lnFloorBracket (acschArg a (w + 8)) w

/-- The bracket of `−acsch |x|` as a pair of `Roundable`s. -/
def acschApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox true (acschBracket x.abs e w)

/-- The extra starting bits of the Ziv loop for an argument of exponent `e` at precision `p`:
`e` for a large argument (the result is `≈ 2^(−e)` and the logarithm is accurate absolutely),
capped where the huge-argument enclosure takes over. -/
def acschExtra (e : AzInt) (p : Nat) : Nat := if e.sign then min e.abs.toNat (p + 96) else 0

end Azurite.AzFloat
