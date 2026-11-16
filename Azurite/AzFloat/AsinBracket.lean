/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.TanBracket
import Azurite.AzFloat.Sqrt

/-!
## The bracket of `arcsin x`

For `0 < a < 1` the half-angle identity

  `arcsin a = 2 arctan t`,  `t = a / (1 + √(1 − a²))`,

reduces the arcsine to the arctangent of an argument `t ∈ (0, 1)` for **every** `a`, with no case
distinction and without `π`: `t = tan (arcsin (a) / 2)`.

* `asinArg a P` encloses `t` by directed roundings at `P` bits: `1 − a` and `1 + a` (correctly
  rounded differences and sums, so `1 − a` keeps its relative accuracy for `a` next to `1`),
  their product `1 − a²`, its square root, `1 + √`, and the quotient (`asinArgOf`, shared
  with the rational variant).  The width is at most `40·2^(−P)`.
* `asinBracket x ex w` is the doubled `atanWiden` of that enclosure, at the level
  `K = atanWork ex w` (`w + 8` plus the number of leading zero bits of `|x|`, so with relative
  accuracy), `V = K + 64`, the argument at `V + 8` bits.  Width at most `2^(−w)`.
* `asinApprox` is the pair of `Roundable`s for the Ziv loop of `AzFloat/Asin.lean` (negated and
  swapped for `x < 0`), and `asinTiny?` the tiny-argument path: `arcsin |x|` lies in
  `(|x|, |x| + |x|³]` just as `tan |x|` does, so it is the test of `tanTiny?`.

The proofs are in `Equiv/AsinBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `√(1 − a²)` for a float `0 < a < 1`, at precision `P`, with relative
accuracy: from the correctly rounded `1 − a` and `1 + a`. -/
def asinSqrt (a : AzFloat) (P : Nat) : Encl :=
  let dl := (subPrecRound one a P .Floor).1
  let dh := (subPrecRound one a P .Ceiling).1
  let el := (addPrecRound one a P .Floor).1
  let eh := (addPrecRound one a P .Ceiling).1
  let pl := (mulPrecRound dl el P .Floor).1
  let ph := (mulPrecRound dh eh P .Ceiling).1
  ((sqrtPrecRound pl P .Floor).1, (sqrtPrecRound ph P .Ceiling).1)

/-- An enclosure of `a / (1 + s)` from floats `al ≤ a ≤ ah` and an enclosure `s` of a number in
`[0, 1]`, at precision `P`. -/
def asinArgOf (al ah : AzFloat) (s : Encl) (P : Nat) : Encl :=
  let ol := (addPrecRound one s.1 P .Floor).1
  let oh := (addPrecRound one s.2 P .Ceiling).1
  ((divPrecRound al oh P .Floor).1, (divPrecRound ah ol P .Ceiling).1)

/-- An enclosure of `a / (1 + √(1 − a²))` for a float `0 < a < 1`, at precision `P`. -/
def asinArg (a : AzFloat) (P : Nat) : Encl := asinArgOf a a (asinSqrt a P) P

/-- The bracket of `arcsin |x|` at Ziv level `w` for a finite `x` of exponent `ex ≤ 0`. -/
def asinBracket (x : AzFloat) (ex : AzInt) (w : Nat) : Encl :=
  let K := atanWork ex w
  let V := K + 64
  let t := asinArg x.abs (V + 8)
  let A := atanWiden t.1 t.2 K V
  (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1)

/-- The bracket of `arcsin x` as a pair of `Roundable`s (`neg`: `x < 0`). -/
def asinApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox neg (asinBracket x ex w)

/-- **The tiny-argument path of `arcsin`** for a finite `x` of sign `s`, exponent `e` and
precision `q`: the test of `tanTiny?` (`|x| < 2^e`, `e ≤ −(max p q + 72)`), valid because
`|x| < arcsin |x| ≤ |x| + |x|³`. -/
def asinTiny? (s : Bool) (x : AzFloat) (e : AzInt) (q p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  tanTiny? s x e q p mode

end Azurite.AzFloat
