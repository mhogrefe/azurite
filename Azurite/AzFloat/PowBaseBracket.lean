/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.LogBaseBracket
import Azurite.AzFloat.LogBaseExact
import Azurite.AzFloat.Pow2Bracket
import Azurite.AzRat.Conversion
import Azurite.AzRat.Mul

/-!
## The brackets of `u^x` and `u^q` for a natural base `u`

`u^x = exp (x ln u)`.  `lnBaseMulBracket B x e w` encloses `x ln u`: `|x|` times the ends of
the bracket `B` of `ln u` at `expWork e w` bits (`absMulBracket`, directed products), the ends
swapped and negated for `x < 0` (`mulBracketSigned`); `powBaseBracket` is the exponential of it
(`expOfBracketBy`, with the bracket of `ln 2` shared between the logarithm and the reduction of
the exponential through `powLnConsts`) and
`powBaseApprox` is the pair of `Roundable`s for the Ziv loop, started at `powBaseStart e u p`
bits so that the proven width bound of the `ln u` bracket times `|x|` is below `1` from the
first iteration; that threshold (`lnMulW₀`) is logarithmic in the exponent `e` of `x`, so a huge
`x` costs `e` extra bits once, in the bracket of `x ln u`, and not in the final exponential.
`powBaseExact? x u` detects a rational `u^x`: with `r` the primitive root of
`u = r^s` (`maxRootBase`), `u^x = r^(s x)` is rational exactly when `s x` is an integer `n`, and
then equals `r^n`; every other `u^x` is irrational (`Equiv/PowBaseBracket.lean`).  A float with
more than six fractional bits is rejected from its dyadic structure (`powBaseExactSkip`) without
being converted to a rational.  The rational
versions `lnBaseMulRatBracket`, `powBaseRatBracket`, `powBaseRatApprox`, `powBaseRatExact?` use
the floats below and above `|q|` at `w + 16 + size (num q)` bits instead of `|x|`.
`powBaseM1Bracket` brackets `u^x − 1` through `expM1OfBracketBy` at the exponent `e + 6`, and
`powBaseM1RatBracket` is its rational version at the exponent `pow2M1RatExp q + 6`.
-/

namespace Azurite.AzFloat

/-- `|x|` times a nonnegative bracket `B`, at precision `W`, rounded outward. -/
def absMulBracket (x : AzFloat) (B : AzFloat × AzFloat) (W : Nat) : AzFloat × AzFloat :=
  ((mulPrecRound x.abs B.1 W .Floor).1, (mulPrecRound x.abs B.2 W .Ceiling).1)

/-- `x` times a nonnegative bracket `B`: `absMulBracket`, swapped and negated for `x < 0`. -/
def mulBracketSigned (x : AzFloat) (B : AzFloat × AzFloat) (W : Nat) : AzFloat × AzFloat :=
  let P := absMulBracket x B W
  if x.isNegative then (-P.2, -P.1) else P

/-- The bracket of `x ln u` for a float `x` of exponent `e`, at working precision `w`, from a
bracket `B` of `ln u` at `expWork e w` bits. -/
def lnBaseMulBracket (B : AzFloat × AzFloat) (x : AzFloat) (e : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  mulBracketSigned x B (expWork e w)

/-- The bracket of `u^x` at working precision `w`. -/
def powBaseBracket (x : AzFloat) (e : AzInt) (u : UInt64) (w : Nat) : AzFloat × AzFloat :=
  let W := expWork e w
  let K := powLnConsts W
  expOfBracketBy K.ln2At (lnBaseMulBracket (lnBaseBracketWith K u W) x e w) w

/-- `powBaseBracket` as a pair of `Roundable`s for the Ziv loop. -/
def powBaseApprox (x : AzFloat) (e : AzInt) (u : UInt64) (w : Nat) : Roundable × Roundable :=
  let b := powBaseBracket x e u w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The precision from which the width bound of `lnBaseMulBracket` is below `1`:
`lnMulW₀ (max(e, 0) + |exponent of u|)`, logarithmic in a huge `e`. -/
def powBaseW₀ (e : AzInt) (u : UInt64) : Nat :=
  lnMulW₀ ((if e.sign then e.abs.toNat else 0) + ((baseFloat u).exponent?.getD 0).abs.toNat)

/-- The starting precision of the Ziv loop for `u^x` at precision `p`. -/
def powBaseStart (e : AzInt) (u : UInt64) (p : Nat) : Nat :=
  max (p + zivGuardBits) (powBaseW₀ e u)

/-- `u^x` as an exact power `(r, n)` with `u^x = r^n`, `r` the primitive root of `u = r^s`,
when `s x` is an integer `n`; `none` otherwise (then `u^x` is irrational).  Converts `x` to a
rational. -/
def powBaseExactCore? (x : AzFloat) (u : AzNat) : Option (AzNat × AzInt) :=
  match x.toAzRat? with
  | some q =>
    let rs := maxRootBase u
    let y := q * (AzNat.ofNat rs.2).toAzRat
    if y.den = 1 then some (rs.1, AzInt.mkNorm y.sign y.num) else none
  | none => none

/-- A sufficient test, on the dyadic structure of `x = ±o · 2^i` (`o` odd) alone, that
`powBaseExactCore?` answers `none`: `s x` is an integer only if `2^(−i)` divides `s ≤ 63`, so
never for `i < −6`.  A float with more than six fractional bits — in particular a tiny `x`,
whose rational form has a denominator of `|i|` bits — is never converted. -/
def powBaseExactSkip : AzFloat → Bool
  | finite _ e _ m _ => !(dyadicExp e m).sign && decide (6 < (dyadicExp e m).abs.toNat)
  | _ => false

/-- `u^x` as an exact power `(r, n)` with `u^x = r^n`, `r` the primitive root of `u = r^s`,
when `s x` is an integer `n`; `none` otherwise (then `u^x` is irrational).  The cheap test
`powBaseExactSkip` first, then `powBaseExactCore?`. -/
def powBaseExact? (x : AzFloat) (u : AzNat) : Option (AzNat × AzInt) :=
  if powBaseExactSkip x then none else powBaseExactCore? x u

/-! ### The rational exponent -/

/-- The floats below and above `|q|` times a nonnegative bracket `B`, at precision `W`, rounded
outward. -/
def absMulRatBracket (q : AzRat) (B : AzFloat × AzFloat) (W : Nat) : AzFloat × AzFloat :=
  let a := (ofAzRatRound q.abs W .Floor).1
  let b := (ofAzRatRound q.abs W .Ceiling).1
  ((mulPrecRound a B.1 W .Floor).1, (mulPrecRound b B.2 W .Ceiling).1)

/-- The bracket of `q ln u` for a rational `q`, at working precision `w`, from a bracket `B` of
`ln u` at `W = w + 16 + size (num q)` bits: `absMulRatBracket` at `W` bits, swapped and negated
for `q < 0`. -/
def lnBaseMulRatBracket (B : AzFloat × AzFloat) (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let W := w + 16 + q.num.size
  let P := absMulRatBracket q B W
  if q.sign then P else (-P.2, -P.1)

/-- The bracket of `u^q` at working precision `w`. -/
def powBaseRatBracket (q : AzRat) (u : UInt64) (w : Nat) : AzFloat × AzFloat :=
  let W := w + 16 + q.num.size
  let K := powLnConsts W
  expOfBracketBy K.ln2At (lnBaseMulRatBracket (lnBaseBracketWith K u W) q w) w

/-- `powBaseRatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def powBaseRatApprox (q : AzRat) (u : UInt64) (w : Nat) : Roundable × Roundable :=
  let b := powBaseRatBracket q u w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The precision from which the width bound of `lnBaseMulRatBracket` is below `1`. -/
def powBaseRatW₀ (q : AzRat) (u : UInt64) : Nat :=
  lnMulW₀ (q.num.size + ((baseFloat u).exponent?.getD 0).abs.toNat)

/-- The starting precision of the Ziv loop for `u^q` at precision `p`. -/
def powBaseRatStart (q : AzRat) (u : UInt64) (p : Nat) : Nat :=
  max (p + zivGuardBits) (powBaseRatW₀ q u)

/-- `u^q` as an exact power `(r, n)` with `u^q = r^n`, `r` the primitive root of `u = r^s`,
when `s q` is an integer `n`; `none` otherwise (then `u^q` is irrational). -/
def powBaseRatExact? (q : AzRat) (u : AzNat) : Option (AzNat × AzInt) :=
  let rs := maxRootBase u
  let y := q * (AzNat.ofNat rs.2).toAzRat
  if y.den = 1 then some (rs.1, AzInt.mkNorm y.sign y.num) else none

/-! ### `u^x − 1` -/

/-- The exponent `e + 6` of `x ln u` for `|x| < 2^e` (`ln u < 45 < 64`). -/
def powBaseM1Exp (e : AzInt) : AzInt := e + AzInt.ofInt 6

/-- The bracket of `u^x − 1` for a float `x` of exponent `e`: `expM1OfBracketBy` at the exponent
`e + 6` of the bracket of `x ln u` computed at the compensated precision
`w + max(−e − 6, 0)`. -/
def powBaseM1Bracket (x : AzFloat) (e : AzInt) (u : UInt64) (w : Nat) : AzFloat × AzFloat :=
  let e' := powBaseM1Exp e
  let W := expWork e (w + expM1Comp e')
  let K := powLnConsts W
  expM1OfBracketBy K.ln2At
    (lnBaseMulBracket (lnBaseBracketWith K u W) x e (w + expM1Comp e')) e' w

/-- `powBaseM1Bracket` as a pair of `Roundable`s for the Ziv loop. -/
def powBaseM1Approx (x : AzFloat) (e : AzInt) (u : UInt64) (w : Nat) :
    Roundable × Roundable :=
  let b := powBaseM1Bracket x e u w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The precision from which the bracket of `x ln u` is narrow enough for `expM1OfBracketBy`:
`lnMulW₀ (|e| + |exponent of u|)`. -/
def powBaseM1W₀ (e : AzInt) (u : UInt64) : Nat :=
  lnMulW₀ (e.abs.toNat + ((baseFloat u).exponent?.getD 0).abs.toNat)

/-- The starting precision of the Ziv loop for `u^x − 1` at precision `p`. -/
def powBaseM1Start (e : AzInt) (u : UInt64) (p : Nat) : Nat :=
  max (p + zivGuardBits) (powBaseM1W₀ e u)

/-- The bracket of `u^q − 1` for a rational `q ≠ 0`: `expM1OfBracketBy` at the exponent
`pow2M1RatExp q + 6` of the bracket of `q ln u` computed at the compensated precision. -/
def powBaseM1RatBracket (q : AzRat) (u : UInt64) (w : Nat) : AzFloat × AzFloat :=
  let e' := powBaseM1Exp (pow2M1RatExp q)
  let W := w + expM1Comp e' + 16 + q.num.size
  let K := powLnConsts W
  expM1OfBracketBy K.ln2At
    (lnBaseMulRatBracket (lnBaseBracketWith K u W) q (w + expM1Comp e')) e' w

/-- `powBaseM1RatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def powBaseM1RatApprox (q : AzRat) (u : UInt64) (w : Nat) : Roundable × Roundable :=
  let b := powBaseM1RatBracket q u w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The precision from which the bracket of `q ln u` is narrow enough for `expM1OfBracketBy`:
`lnMulW₀ (|pow2M1RatExp q| + size (num q) + |exponent of u|)`. -/
def powBaseM1RatW₀ (q : AzRat) (u : UInt64) : Nat :=
  lnMulW₀
    ((pow2M1RatExp q).abs.toNat + q.num.size + ((baseFloat u).exponent?.getD 0).abs.toNat)

/-- The starting precision of the Ziv loop for `u^q − 1` at precision `p`. -/
def powBaseM1RatStart (q : AzRat) (u : UInt64) (p : Nat) : Nat :=
  max (p + zivGuardBits) (powBaseM1RatW₀ q u)

end Azurite.AzFloat
