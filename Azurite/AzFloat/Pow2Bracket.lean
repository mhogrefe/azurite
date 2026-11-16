/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzRat.LogBase
import Azurite.AzRat.Unary

/-!
## The brackets of `2^x`, `2^q`, `2^x − 1` and `2^q − 1`

`2^x = exp (x ln 2)`: `ln2MulBracket x e w` encloses `x ln 2` from `|x|` times the ends of
`ln2Bracket` at the working precision `expWork e w = w + 16 + max(e, 0)` (so that the width is
below `2^(−w)` for `|x| < 2^e`), the ends swapped and negated for `x < 0`; `pow2Bracket` is
`expOfBracket` of it, and `pow2Approx` the pair of `Roundable`s for the Ziv loop.  For a
rational `q`, `ln2MulRatBracket` uses the floats below and above `|q|` at `w + 16 + size (num q)`
bits instead of `|x|`.  `pow2M1Bracket` brackets `2^x − 1` through `expM1OfBracketBy`, the
`exp v − 1` analogue of `expOfBracket` built on `expM1Bracket`, and `pow2M1RatBracket` is its
rational version at the exponent `pow2M1RatExp q = ⌊log₂ |q|⌋ + 1`.
-/

namespace Azurite.AzFloat

/-- The bracket of `|x| ln 2` at precision `W`, from the bracket `L` of `ln 2`. -/
def absLn2Bracket (L : AzFloat × AzFloat) (x : AzFloat) (W : Nat) : AzFloat × AzFloat :=
  ((mulPrecRound x.abs L.1 W .Floor).1, (mulPrecRound x.abs L.2 W .Ceiling).1)

/-- The bracket of `x ln 2` for a float `x` of exponent `e`, at working precision `w`, from the
bracket `L = ln2Bracket (expWork e w)`. -/
def ln2MulBracket (L : AzFloat × AzFloat) (x : AzFloat) (e : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  let P := absLn2Bracket L x (expWork e w)
  if x.isNegative then (-P.2, -P.1) else P

/-- The bracket of `2^x` at working precision `w`.  The bracket of `ln 2` is computed once, at
`expWork e w` bits, and reused by the reduction of the exponential (`ln2Reuse`), which needs it
at no higher precision since `|x ln 2| < |x|`. -/
def pow2Bracket (x : AzFloat) (e : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let W := expWork e w
  let L := ln2Bracket W
  expOfBracketBy (ln2Reuse W L) (ln2MulBracket L x e w) w

/-- `pow2Bracket` as a pair of `Roundable`s for the Ziv loop. -/
def pow2Approx (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := pow2Bracket x e w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `|q| ln 2` at precision `W` for a rational `q`: the floats below and above
`|q|` times the ends of the bracket `L` of `ln 2`. -/
def absLn2RatBracket (L : AzFloat × AzFloat) (q : AzRat) (W : Nat) : AzFloat × AzFloat :=
  let a := (ofAzRatRound q.abs W .Floor).1
  let b := (ofAzRatRound q.abs W .Ceiling).1
  ((mulPrecRound a L.1 W .Floor).1, (mulPrecRound b L.2 W .Ceiling).1)

/-- The bracket of `q ln 2` for a rational `q`, at working precision `w`, from the bracket
`L = ln2Bracket (w + 16 + size (num q))`. -/
def ln2MulRatBracket (L : AzFloat × AzFloat) (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let P := absLn2RatBracket L q (w + 16 + q.num.size)
  if q.sign then P else (-P.2, -P.1)

/-- The bracket of `2^q` at working precision `w`, the bracket of `ln 2` computed once and
reused by the reduction of the exponential. -/
def pow2RatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let W := w + 16 + q.num.size
  let L := ln2Bracket W
  expOfBracketBy (ln2Reuse W L) (ln2MulRatBracket L q w) w

/-- `pow2RatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def pow2RatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := pow2RatBracket q w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `exp v − 1` from a bracket `X` of `v` with `|v| < 2^e` (of width at most
`1`): `expM1Bracket` at the lower end `lo` gives `[a, b] ∋ exp lo − 1`, and the upper end is
widened to `b + ⌈(b + 1) · 2d⌉` for `d = ⌈hi − lo⌉`, since
`exp v − 1 ≤ (exp lo − 1) + exp lo · 2 (v − lo)` and `exp lo ≤ b + 1`.  The brackets of `ln 2`
come from a supplier `F`. -/
def expM1OfBracketBy (F : Nat → AzFloat × AzFloat) (X : AzFloat × AzFloat) (e : AzInt)
    (w : Nat) : AzFloat × AzFloat :=
  let b := expM1BracketBy F X.1 e w
  let d := (subPrecRound X.2 X.1 (w + 8) .Ceiling).1
  let E := (addPrecRound b.2 one (w + 8) .Ceiling).1
  let corr := (mulPrecRound E (d <<< AzInt.ofInt 1) (w + 8) .Ceiling).1
  (b.1, (addPrecRound b.2 corr (w + 8) .Ceiling).1)

/-- The bracket of `2^x − 1` for a finite float `x` of exponent `e`: `expM1OfBracketBy` of the
bracket of `x ln 2` at the compensated working precision `w + max(−e, 0)` (so that its width
`2^(−w) · 2^(min(e, 0))` is a `2^(−w)` fraction of `|x ln 2|`). -/
def pow2M1Bracket (x : AzFloat) (e : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let W := expWork e (w + expM1Comp e)
  let L := ln2Bracket W
  expM1OfBracketBy (ln2Reuse W L) (ln2MulBracket L x e (w + expM1Comp e)) e w

/-- `pow2M1Bracket` as a pair of `Roundable`s for the Ziv loop. -/
def pow2M1Approx (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := pow2M1Bracket x e w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The exponent `⌊log₂ |q|⌋ + 1` of a rational `q ≠ 0` (so `2^(e−1) ≤ |q| < 2^e`), for the
compensation of `2^q − 1`. -/
def pow2M1RatExp (q : AzRat) : AzInt := AzInt.ofInt (AzRat.floorLogBaseAbs 2 q + 1)

/-- The bracket of `2^q − 1` for a rational `q`: `expM1OfBracketBy` of the bracket of `q ln 2` at
the compensated working precision `w + max(−e, 0)`, `e = pow2M1RatExp q`. -/
def pow2M1RatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let e := pow2M1RatExp q
  let W := w + expM1Comp e + 16 + q.num.size
  let L := ln2Bracket W
  expM1OfBracketBy (ln2Reuse W L) (ln2MulRatBracket L q (w + expM1Comp e)) e w

/-- `pow2M1RatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def pow2M1RatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := pow2M1RatBracket q w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
