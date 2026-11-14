/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CscBracket
import Azurite.AzFloat.SinCosRatBracket
import Azurite.AzFloat.SinCosWithPeriodBracket

/-!
## The brackets of `cot x`

`cot x = cos x / sin x`.  The brackets are the quotient step `tanOfSinCos`
(`AzFloat/TanBracket.lean`) applied to a joint bracket of the sine and the cosine with its two
components **swapped** (numerator: the cosine; denominator: the sine) — two directed divisions,
or the dummy bracket `[−1, 1]` (never accepted by `roundingPossible`) while the sine bracket
contains `0`:

* `cotBracket x ex w` (a float `x`): over `sinCosBracket x ex w`, enclosing `cot |x|`;
* `cotRatBracket q w` (a rational `q`): over `sinCosRatBracket q w`, enclosing `cot |q|`;
* `cotPeriodBracket r w` (`r ∈ [0, 1)`): over `sinCosPeriodBracket r w`, enclosing `cot (2πr)`.

The `…Approx` functions negate and swap the ends for a negative argument (`cot` is odd).

**Tiny arguments** (`cotTinyCore?`): for `0 < a < 2^e`, `e ≤ 0`, enclosed by floats
`alo ≤ a ≤ ahi`, `1/a − a ≤ cot a < 1/a`, so `−cot a ∈ [−⌈1/alo⌉, −⌊⌊1/ahi⌋ − ahi⌋]` at
`p + 72` bits, decided by one `roundingPossible` test when `2|e| ≥ p + 72`.  The test is always
made on `−cot a` (in the negated mode, the result negated, for a positive argument), so that the
end `−1/a` — exact when `x` is a power of two — sits at the open side of the half-open test.
`cotTiny?`, `cotTinyRat?`, `cotPeriodTiny?` as for the cosecant.
-/

namespace Azurite.AzFloat

/-- The bracket of `cot |x|` at Ziv level `w` for a finite `x` of exponent `ex`, or the dummy
bracket `[−1, 1]` when the bracket of `sin |x|` contains `0`. -/
def cotBracket (x : AzFloat) (ex : AzInt) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (sinCosBracket x ex w).swap (w + 12)

/-- The bracket of `cot x` as a pair of `Roundable`s (negated and swapped when `neg`). -/
def cotApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  negSwapApprox neg (cotBracket x ex w)

/-- The bracket of `cot |q|` at Ziv level `w` for a rational `q`. -/
def cotRatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (sinCosRatBracket q w).swap (w + 12)

/-- The bracket of `cot q` as a pair of `Roundable`s (negated and swapped for `q < 0`). -/
def cotRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  negSwapApprox (!q.sign) (cotRatBracket q w)

/-- The bracket of `cot (2πr)` at Ziv level `w` for a rational `r ∈ [0, 1)`. -/
def cotPeriodBracket (r : AzRat) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (sinCosPeriodBracket r w).swap (w + 12)

/-- The bracket of `± cot (2πr)` as a pair of `Roundable`s (negated and swapped for `neg`). -/
def cotPeriodApprox (neg : Bool) (r : AzRat) (w : Nat) : Roundable × Roundable :=
  negSwapApprox neg (cotPeriodBracket r w)

/-- **The tiny-argument test of the cotangent** for `0 < a < 2^e` enclosed by the floats
`alo ≤ a ≤ ahi` (`neg`: the value is `−cot a`).  `none` when `2|e| < p + 72` or the test
fails. -/
def cotTinyCore? (neg : Bool) (alo ahi : AzFloat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if e.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e.abs.toNat then
    let W := p + zivGuardBits + 8
    let lo := -(divPrecRound one alo W .Ceiling).1
    let hi := -(subPrecRound (divPrecRound one ahi W .Floor).1 ahi W .Floor).1
    let r := roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p
      (if neg then mode else -mode)
    if neg then r else r.map fun r => (-r.1, r.2.swap)
  else none

/-- The tiny-argument path of `cot x` for a finite `x` of sign `s` and exponent `e`. -/
def cotTiny? (s : Bool) (x : AzFloat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  cotTinyCore? (!s) x.abs x.abs e p mode

/-- The tiny-argument path of `cot q` for a rational `q`. -/
def cotTinyRat? (q : AzRat) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let W := p + zivGuardBits + 8
  cotTinyCore? (!q.sign) (ofAzRatRound q.abs W .Floor).1 (ofAzRatRound q.abs W .Ceiling).1
    (ratExpBound q) p mode

/-- The tiny-argument path of `cot (2π x / u)` for `|x| = m 2^E`, `|2πx/u| < 2^e'`
(`neg`: `x < 0`). -/
def cotPeriodTiny? (neg : Bool) (m u : AzNat) (E e' : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let y := periodTinyArg m u E (p + zivGuardBits + 8)
  cotTinyCore? neg y.1 y.2 e' p mode

end Azurite.AzFloat
