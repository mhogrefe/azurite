/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzRat.Unary

/-!
## The brackets of `2^x` and `2^q`

`2^x = exp (x ln 2)`: `ln2MulBracket x e w` encloses `x ln 2` from `|x|` times the ends of
`ln2Bracket` at the working precision `expWork e w = w + 16 + max(e, 0)` (so that the width is
below `2^(−w)` for `|x| < 2^e`), the ends swapped and negated for `x < 0`; `exp2Bracket` is
`expOfBracket` of it, and `exp2Approx` the pair of `Roundable`s for the Ziv loop.  For a
rational `q`, `ln2MulRatBracket` uses the floats below and above `|q|` at `w + 16 + size (num q)`
bits instead of `|x|`.
-/

namespace Azurite.AzFloat

/-- The bracket of `|x| ln 2` at precision `W`. -/
def absLn2Bracket (x : AzFloat) (W : Nat) : AzFloat × AzFloat :=
  let L := ln2Bracket W
  ((mulPrecRound x.abs L.1 W .Floor).1, (mulPrecRound x.abs L.2 W .Ceiling).1)

/-- The bracket of `x ln 2` for a float `x` of exponent `e`, at working precision `w`. -/
def ln2MulBracket (x : AzFloat) (e : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let P := absLn2Bracket x (expWork e w)
  if x.isNegative then (-P.2, -P.1) else P

/-- The bracket of `2^x` at working precision `w`. -/
def exp2Bracket (x : AzFloat) (e : AzInt) (w : Nat) : AzFloat × AzFloat :=
  expOfBracket (ln2MulBracket x e w) w

/-- `exp2Bracket` as a pair of `Roundable`s for the Ziv loop. -/
def exp2Approx (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := exp2Bracket x e w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `|q| ln 2` at precision `W` for a rational `q`: the floats below and above
`|q|` times the ends of `ln2Bracket`. -/
def absLn2RatBracket (q : AzRat) (W : Nat) : AzFloat × AzFloat :=
  let L := ln2Bracket W
  let a := (ofAzRatRound q.abs W .Floor).1
  let b := (ofAzRatRound q.abs W .Ceiling).1
  ((mulPrecRound a L.1 W .Floor).1, (mulPrecRound b L.2 W .Ceiling).1)

/-- The bracket of `q ln 2` for a rational `q`, at working precision `w`. -/
def ln2MulRatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let P := absLn2RatBracket q (w + 16 + q.num.size)
  if q.sign then P else (-P.2, -P.1)

/-- The bracket of `2^q` at working precision `w`. -/
def exp2RatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  expOfBracket (ln2MulRatBracket q w) w

/-- `exp2RatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def exp2RatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := exp2RatBracket q w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
