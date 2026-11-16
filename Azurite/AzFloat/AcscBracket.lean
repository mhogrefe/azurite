/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosBracket

/-!
## The bracket of `arccsc x`

`arccsc x = arcsin (1/x)` for `|x| ≥ 1`, an odd function.  For `a > 1` the half-angle identity
of the arcsine becomes

  `arccsc a = 2 arctan t`,  `t = 1 / (a + √(a² − 1))`,

with `t ∈ (0, 1)` for every `a`.

* `acscArg a P` encloses `t`: `√(a² − 1) = (a + 1) √((a − 1)/(a + 1))` from `diffQuotSqrt a 1`
  (`AzFloat/AcosBracket.lean`), the sum with `a` (no cancellation) and one division — relative
  accuracy throughout, so the width is at most `40·2^(−P)`.
* `acscTinyEncl a w` is the enclosure for a huge `a`: `1/a < arccsc a ≤ (1/a)(1 + 1/a²)`, so
  two directed divisions and a factor `1 + 2^(−w−14)`.  Its lower end is the correctly rounded
  `1/a` — **exactly** `1/a` when `a` is a power of two, the case in which `arccsc a` is
  exponentially close to a float.
* `acscBracket x en w` encloses `arccsc |x|` for a float of exponent `en ≥ 1` with width at
  most `2^(−w)`: the tiny enclosure when `2 en ≥ w + 16`; otherwise the doubled `atanWiden` at
  the level `w + 8 + en` (relative accuracy: the result is about `2^(−en)`).  So the working
  precision never exceeds about `3w/2`, whatever the exponent.
* `acscApprox` is the pair of `Roundable`s for the Ziv loop of `AzFloat/Acsc.lean`, which
  always runs on `arccsc |x|`, so that the exact end is the lower one.

The proofs are in `Equiv/AcscBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `1 / (a + √(a² − 1))` for a float `a > 1`, of width at most
`40·2^(−P)`. -/
def acscArg (a : AzFloat) (P : Nat) : Encl :=
  let Q := P + 3
  let r := diffQuotSqrt a one Q
  let el := (addPrecRound a one Q .Floor).1
  let eh := (addPrecRound a one Q .Ceiling).1
  let sl := (mulPrecRound el r.1 Q .Floor).1
  let sh := (mulPrecRound eh r.2 Q .Ceiling).1
  let dl := (addPrecRound a sl Q .Floor).1
  let dh := (addPrecRound a sh Q .Ceiling).1
  ((divPrecRound one dh Q .Floor).1, (divPrecRound one dl Q .Ceiling).1)

/-- The enclosure `[1/a, (1/a)(1 + 2^(−w−14))]` (rounded outwards at `w + 16` bits) of
`arcsin (1/a)` for a float `a` with `1/a² ≤ 2^(−w−14)`. -/
def acscTinyEncl (a : AzFloat) (w : Nat) : Encl :=
  let W := w + 16
  let c := (addPrecRound one (one <<< AzInt.ofInt (-((w : Int) + 14))) W .Ceiling).1
  ((divPrecRound one a W .Floor).1,
    (mulPrecRound (divPrecRound one a W .Ceiling).1 c W .Ceiling).1)

/-- The bracket of `arccsc |x| = arcsin (1/|x|)` at Ziv level `w` for a finite `x` with
`|x| > 1` and exponent `en` (`2^(en−1) ≤ |x|`). -/
def acscBracket (x : AzFloat) (en w : Nat) : Encl :=
  if w + 16 ≤ 2 * en then acscTinyEncl x.abs w
  else
    let K := w + 8 + en
    let t := acscArg x.abs (K + 64 + 8)
    let A := atanWiden t.1 t.2 K (K + 64)
    (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1)

/-- The bracket of `arccsc |x|` as a pair of `Roundable`s. -/
def acscApprox (x : AzFloat) (en w : Nat) : Roundable × Roundable :=
  enclApprox false (acscBracket x en w)

end Azurite.AzFloat
