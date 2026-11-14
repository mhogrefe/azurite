/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinRatBracket
import Azurite.AzFloat.SinWithPeriodBracket
import Azurite.AzFloat.TanBracket

/-!
## The brackets of `csc x`

`csc x = 1 / sin x`.  The brackets are the quotient step `tanOfSinCos` (`AzFloat/TanBracket.lean`)
applied to the exact numerator `1` and a bracket of the sine — two directed divisions, or the
dummy bracket `[−1, 1]` (never accepted by `roundingPossible`) while the sine bracket contains
`0`:

* `cscBracket x ex w` (a float `x`): over `sinBracket x ex w`, enclosing `csc |x|`;
* `cscRatBracket q w` (a rational `q`): over `sinRatBracket q w`, enclosing `csc |q|`;
* `cscPeriodBracket r w` (`r ∈ [0, 1)`): over `sinPeriodBracket r w`, enclosing `csc (2πr)`.

The `…Approx` functions negate and swap the ends for a negative argument (`csc` is odd).

**Tiny arguments** (`cscTinyCore?`): for `0 < a < 2^e`, `e ≤ 0`, enclosed by floats
`alo ≤ a ≤ ahi`, `1/a < csc a ≤ 1/a + a`, so `csc a ∈ [⌊1/ahi⌋, ⌈⌈1/alo⌉ + ahi⌉]` at `p + 72`
bits: the relative width is about `a²`, and one `roundingPossible` test decides when
`2|e| ≥ p + 72`.  The test is always made on the positive value (in the negated mode, the result
negated, for a negative argument), so that the lower end — which is the exact `1/|x|` when `x` is
a power of two — sits at the open side of the half-open test.  (The Ziv loop on the sine bracket would need about `|e|` bits more than the
target precision.)  `cscTiny?` (a float: `alo = ahi = |x|`), `cscTinyRat?` (the floor and
ceiling of `|q|`), `cscPeriodTiny?` (the floats `periodTinyArg` around `y = 2π m 2^E / u`).
-/

namespace Azurite.AzFloat

/-- The bracket of `csc |x|` at Ziv level `w` for a finite `x` of exponent `ex`, or the dummy
bracket `[−1, 1]` when the bracket of `sin |x|` contains `0`. -/
def cscBracket (x : AzFloat) (ex : AzInt) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (Encl.exact one, sinBracket x ex w) (w + 12)

/-- The bracket of `csc x` as a pair of `Roundable`s (negated and swapped when `neg`). -/
def cscApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  negSwapApprox neg (cscBracket x ex w)

/-- The bracket of `csc |q|` at Ziv level `w` for a rational `q`. -/
def cscRatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (Encl.exact one, sinRatBracket q w) (w + 12)

/-- The bracket of `csc q` as a pair of `Roundable`s (negated and swapped for `q < 0`). -/
def cscRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  negSwapApprox (!q.sign) (cscRatBracket q w)

/-- The bracket of `csc (2πr)` at Ziv level `w` for a rational `r ∈ [0, 1)`. -/
def cscPeriodBracket (r : AzRat) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (Encl.exact one, sinPeriodBracket r w) (w + 12)

/-- The bracket of `± csc (2πr)` as a pair of `Roundable`s (negated and swapped for `neg`). -/
def cscPeriodApprox (neg : Bool) (r : AzRat) (w : Nat) : Roundable × Roundable :=
  negSwapApprox neg (cscPeriodBracket r w)

/-- **The tiny-argument test of the cosecant** for `0 < a < 2^e` enclosed by the floats
`alo ≤ a ≤ ahi` (`neg`: the value is `−csc a`).  `none` when `2|e| < p + 72` or the test
fails. -/
def cscTinyCore? (neg : Bool) (alo ahi : AzFloat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if e.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e.abs.toNat then
    let W := p + zivGuardBits + 8
    let lo := (divPrecRound one ahi W .Floor).1
    let hi := (addPrecRound (divPrecRound one alo W .Ceiling).1 ahi W .Ceiling).1
    let r := roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p
      (if neg then -mode else mode)
    if neg then r.map fun r => (-r.1, r.2.swap) else r
  else none

/-- The tiny-argument path of `csc x` for a finite `x` of sign `s` and exponent `e`. -/
def cscTiny? (s : Bool) (x : AzFloat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  cscTinyCore? (!s) x.abs x.abs e p mode

/-- The tiny-argument path of `csc q` for a rational `q`. -/
def cscTinyRat? (q : AzRat) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let W := p + zivGuardBits + 8
  cscTinyCore? (!q.sign) (ofAzRatRound q.abs W .Floor).1 (ofAzRatRound q.abs W .Ceiling).1
    (ratExpBound q) p mode

/-- Floats `ylo ≤ y ≤ yhi` around `y = 2π m 2^E / u` at precision `W` (the exponent `E` enters
only through exact shifts). -/
def periodTinyArg (m u : AzNat) (E : AzInt) (W : Nat) : AzFloat × AzFloat :=
  let c := AzRat.ofAzNats m u
  let P := piBracket W
  let k := E + AzInt.ofInt 1
  ((mulPrecRound (ofAzRatRound c W .Floor).1 P.1 W .Floor).1 <<< k,
    (mulPrecRound (ofAzRatRound c W .Ceiling).1 P.2 W .Ceiling).1 <<< k)

/-- The tiny-argument path of `csc (2π x / u)` for `|x| = m 2^E`, `|2πx/u| < 2^e'`
(`neg`: `x < 0`). -/
def cscPeriodTiny? (neg : Bool) (m u : AzNat) (E e' : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let y := periodTinyArg m u E (p + zivGuardBits + 8)
  cscTinyCore? neg y.1 y.2 e' p mode

end Azurite.AzFloat
