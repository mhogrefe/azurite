/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.LogBaseBracket
import Azurite.AzFloat.LogBaseExact
import Azurite.AzRat.Conversion
import Azurite.AzRat.Mul

/-!
## The brackets of `u^x` and `u^q` for a natural base `u`

`u^x = exp (x ln u)`.  `lnBaseMulBracket x e u w` encloses `x ln u`: `|x|` times the ends of
`lnBaseBracket u` at `expWork e w` bits (`absMulBracket`, directed products), the ends swapped
and negated for `x < 0` (`mulBracketSigned`); `powBaseBracket = expOfBracket` of it and
`powBaseApprox` is the pair of `Roundable`s for the Ziv loop, started at `powBaseStart e u p`
bits so that the proven width bound of the `ln u` bracket times `|x|` is below `1` from the
first iteration.  `powBaseExact? x u` detects a rational `u^x`: with `r` the primitive root of
`u = r^s` (`maxRootBase`), `u^x = r^(s x)` is rational exactly when `s x` is an integer `n`, and
then equals `r^n`; every other `u^x` is irrational (`Equiv/PowBaseBracket.lean`).  The rational
versions `lnBaseMulRatBracket`, `powBaseRatBracket`, `powBaseRatApprox`, `powBaseRatExact?` use
the floats below and above `|q|` at `w + 16 + size (num q)` bits instead of `|x|`.
-/

namespace Azurite.AzFloat

/-- `|x|` times a nonnegative bracket `B`, at precision `W`, rounded outward. -/
def absMulBracket (x : AzFloat) (B : AzFloat × AzFloat) (W : Nat) : AzFloat × AzFloat :=
  ((mulPrecRound x.abs B.1 W .Floor).1, (mulPrecRound x.abs B.2 W .Ceiling).1)

/-- `x` times a nonnegative bracket `B`: `absMulBracket`, swapped and negated for `x < 0`. -/
def mulBracketSigned (x : AzFloat) (B : AzFloat × AzFloat) (W : Nat) : AzFloat × AzFloat :=
  let P := absMulBracket x B W
  if x.isNegative then (-P.2, -P.1) else P

/-- The bracket of `x ln u` for a float `x` of exponent `e` and a base `u ≥ 2`, at working
precision `w`. -/
def lnBaseMulBracket (x : AzFloat) (e : AzInt) (u : UInt64) (w : Nat) : AzFloat × AzFloat :=
  let W := expWork e w
  mulBracketSigned x (lnBaseBracket u W) W

/-- The bracket of `u^x` at working precision `w`. -/
def powBaseBracket (x : AzFloat) (e : AzInt) (u : UInt64) (w : Nat) : AzFloat × AzFloat :=
  expOfBracket (lnBaseMulBracket x e u w) w

/-- `powBaseBracket` as a pair of `Roundable`s for the Ziv loop. -/
def powBaseApprox (x : AzFloat) (e : AzInt) (u : UInt64) (w : Nat) : Roundable × Roundable :=
  let b := powBaseBracket x e u w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The precision from which the width bound of `lnBaseMulBracket` is below `1`:
`128 + max(e, 0) + |exponent of u|`. -/
def powBaseW₀ (e : AzInt) (u : UInt64) : Nat :=
  128 + (if e.sign then e.abs.toNat else 0) + ((baseFloat u).exponent?.getD 0).abs.toNat

/-- The starting precision of the Ziv loop for `u^x` at precision `p`. -/
def powBaseStart (e : AzInt) (u : UInt64) (p : Nat) : Nat := p + zivGuardBits + powBaseW₀ e u

/-- `u^x` as an exact power `(r, n)` with `u^x = r^n`, `r` the primitive root of `u = r^s`,
when `s x` is an integer `n`; `none` otherwise (then `u^x` is irrational). -/
def powBaseExact? (x : AzFloat) (u : AzNat) : Option (AzNat × AzInt) :=
  match x.toAzRat? with
  | some q =>
    let rs := maxRootBase u
    let y := q * (AzNat.ofNat rs.2).toAzRat
    if y.den = 1 then some (rs.1, AzInt.mkNorm y.sign y.num) else none
  | none => none

/-! ### The rational exponent -/

/-- The floats below and above `|q|` times a nonnegative bracket `B`, at precision `W`, rounded
outward. -/
def absMulRatBracket (q : AzRat) (B : AzFloat × AzFloat) (W : Nat) : AzFloat × AzFloat :=
  let a := (ofAzRatRound q.abs W .Floor).1
  let b := (ofAzRatRound q.abs W .Ceiling).1
  ((mulPrecRound a B.1 W .Floor).1, (mulPrecRound b B.2 W .Ceiling).1)

/-- The bracket of `q ln u` for a rational `q` and a base `u ≥ 2`, at working precision `w`:
`absMulRatBracket` at `w + 16 + size (num q)` bits, swapped and negated for `q < 0`. -/
def lnBaseMulRatBracket (q : AzRat) (u : UInt64) (w : Nat) : AzFloat × AzFloat :=
  let W := w + 16 + q.num.size
  let P := absMulRatBracket q (lnBaseBracket u W) W
  if q.sign then P else (-P.2, -P.1)

/-- The bracket of `u^q` at working precision `w`. -/
def powBaseRatBracket (q : AzRat) (u : UInt64) (w : Nat) : AzFloat × AzFloat :=
  expOfBracket (lnBaseMulRatBracket q u w) w

/-- `powBaseRatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def powBaseRatApprox (q : AzRat) (u : UInt64) (w : Nat) : Roundable × Roundable :=
  let b := powBaseRatBracket q u w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The precision from which the width bound of `lnBaseMulRatBracket` is below `1`. -/
def powBaseRatW₀ (q : AzRat) (u : UInt64) : Nat :=
  128 + q.num.size + ((baseFloat u).exponent?.getD 0).abs.toNat

/-- The starting precision of the Ziv loop for `u^q` at precision `p`. -/
def powBaseRatStart (q : AzRat) (u : UInt64) (p : Nat) : Nat :=
  p + zivGuardBits + powBaseRatW₀ q u

/-- `u^q` as an exact power `(r, n)` with `u^q = r^n`, `r` the primitive root of `u = r^s`,
when `s q` is an integer `n`; `none` otherwise (then `u^q` is irrational). -/
def powBaseRatExact? (q : AzRat) (u : AzNat) : Option (AzNat × AzInt) :=
  let rs := maxRootBase u
  let y := q * (AzNat.ofNat rs.2).toAzRat
  if y.den = 1 then some (rs.1, AzInt.mkNorm y.sign y.num) else none

end Azurite.AzFloat
