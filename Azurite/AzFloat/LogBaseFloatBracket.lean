/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseBracket

/-!
# The bracket of `log_b x` for a float base

`log_b x = ln x / ln b`.  The divisor `ln b` may be negative (`b < 1`) or tiny (`b` near `1`), so
its bracket is `lnBaseFloatBracket`: the `lnBracket` ends clamped by the exact-sign bounds
`(b − 1)/b ≤ ln b` (for `b > 1`) and `ln b ≤ b − 1` (for `b < 1`), computed with directed
rounding, so that both ends have the sign of `ln b` at every working precision.
`divBracketByPosBracket` divides a bracket by a bracket with positive ends: the divisor is
shifted by a power of two to `[1/2, ∞)` (`normShift`), `quotientBracket` is applied, and the
quotient is shifted back exactly.  `logBaseFloatQuot` divides any bracket by the bracket of
`ln b`, negating and swapping for `b < 1`; `logBaseFloatApprox` (the `ln x` bracket) and
`logBaseFloatP1Approx` (the `ln (1 + x)` bracket of `lnP1`) are its instances.
-/

namespace Azurite.AzFloat

/-- The larger of two floats by value (`x` when they are not comparable). -/
def maxOf (x y : AzFloat) : AzFloat := if partialCompare x y == some .lt then y else x

/-- The smaller of two floats by value (`x` when they are not comparable). -/
def minOf (x y : AzFloat) : AzFloat := if partialCompare y x == some .lt then y else x

/-- A bracket of `ln b` for a positive float `b ≠ 1` of exponent `eb`, whose ends have the sign
of `ln b`: for `b > 1` the lower end is raised to `⌊⌊b − 1⌋ / b⌋ ≤ (b − 1)/b`, for `b < 1` the
upper end is lowered to `−⌊1 − b⌋ ≥ b − 1`. -/
def lnBaseFloatBracket (b : AzFloat) (eb : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let B := lnBracket b eb w
  if eb.sign = true ∧ eb.abs ≠ 0 then
    let t := (addPrecRound b (-one) w .Floor).1
    (maxOf B.1 (divPrecRound t b w .Floor).1, B.2)
  else
    (B.1, minOf B.2 (-(addPrecRound one (-b) w .Floor).1))

/-- The shift bringing a positive float `c` to at least `1/2`: `−e` for an exponent `e ≤ 0`,
`0` otherwise. -/
def normShift (c : AzFloat) : AzInt :=
  let e := c.exponent?.getD 0
  if e ≤ 0 then -e else 0

/-- A bracket of `L / M` from a bracket `X` of `L` and a bracket `B = (c, d)` of `M` with
`0 < c`: the divisor is shifted to `[1/2, ∞)`, `quotientBracket` is applied, and the quotient is
shifted back. -/
def divBracketByPosBracket (X B : AzFloat × AzFloat) (w : Nat) : AzFloat × AzFloat :=
  let l := normShift B.1
  let Q := quotientBracket X (B.1 <<< l, B.2 <<< l) w
  (Q.1 <<< l, Q.2 <<< l)

/-- A bracket of `L / ln b` from a bracket `X` of `L`, for a positive float `b ≠ 1` of exponent
`eb`: the sign-clamped bracket of `ln b` divides `X` (negated and swapped for `b < 1`). -/
def logBaseFloatQuot (X : AzFloat × AzFloat) (b : AzFloat) (eb : AzInt) (w : Nat) :
    Roundable × Roundable :=
  let B := lnBaseFloatBracket b eb w
  let q :=
    if eb.sign = true ∧ eb.abs ≠ 0 then divBracketByPosBracket X B w
    else
      let Q := divBracketByPosBracket X (-B.2, -B.1) w
      (-Q.2, -Q.1)
  (fun p mode => setPrecRound q.1 p mode, fun p mode => setPrecRound q.2 p mode)

/-- The bracket of `log_b x = ln x / ln b` for positive floats `x` and `b ≠ 1` of exponents `ex`
and `eb`, at working precision `w`. -/
def logBaseFloatApprox (x : AzFloat) (ex : AzInt) (b : AzFloat) (eb : AzInt) (w : Nat) :
    Roundable × Roundable :=
  logBaseFloatQuot (lnBracket x ex w) b eb w

/-- The bracket of `log_b (1 + x) = ln (1 + x) / ln b` for a float `x > −1` and a positive float
`b ≠ 1` of exponent `eb`: the `ln (1 + x)` bracket of `lnP1` divided by the bracket of `ln b`. -/
def logBaseFloatP1Approx (x b : AzFloat) (eb : AzInt) (w : Nat) : Roundable × Roundable :=
  logBaseFloatQuot (lnFloorBracket (addPrecRound one x w .Floor).1 w) b eb w

/-- The bracket of `log_b q = ln q / ln b` for a positive rational `q` and a positive float
`b ≠ 1` of exponent `eb`: the rational `ln` bracket divided by the bracket of `ln b`. -/
def logBaseRatFloatApprox (q : AzRat) (b : AzFloat) (eb : AzInt) (w : Nat) :
    Roundable × Roundable :=
  logBaseFloatQuot (lnFloorBracket (ofAzRatRound q w .Floor).1 w) b eb w

end Azurite.AzFloat
