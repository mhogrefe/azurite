/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBracket
import Azurite.AzRat.Div
import Azurite.AzNat.ShiftLeft

/-!
## The bracket of `q^y` for a rational `q > 0` and a float `y`, and the exact powers

`q^y = exp (y ln q)`: `lnRatMulBracket q y ey w` is `y` times the bracket of `ln q` from the float
`⌊q⌋_W` below `q` (`lnFloorBracket`, the bracket of `ln` of a rational) at `W = expWork ey w`
bits, rounded outward for any signs (`mulBracketAny`), and `ratPowBracket` is `expOfBracket`
of it; `ratPowApprox neg` gives the ends as `Roundable`s, negated and swapped for a negative
result.  The width bound is `mulLnEps ey E w` with `E = ratPowE q = 2 (size num + size den) + 2
≥ ⌊2 |ln q|⌋ + 2`, below `1` from `w ≥ ratPowW₀ ey q = 136 + max(ey, 0) + E` on
(`Equiv/RatPowBracket.lean`).

**Exact powers.**  For `q = a/b` in lowest terms and a non-integer `y = N/2^J` (`N` odd),
`q^y` is rational iff `a` and `b` are both `2^J`-th powers (`natPow2Root?`: the odd part by
`oddPow2Root`, the power of two by divisibility of its exponent), and then `q^y = (u/v)^N`
(`ratPowExact?`).  The integer power `(a/b)^n` is cheap when both `powIntCheap a n p` and
`powIntCheap b n p` hold (`ratPowIntCheap`); otherwise its reduced form has an odd denominator
`≥ 3` or an odd numerator part of more than `p + 1` bits, so it is never a rounding boundary.
-/

namespace Azurite.AzFloat

/-- The bracket of `y ln q` for a positive rational `q` and a float `y` of exponent `ey`, at
working precision `w`: `y` times the bracket of `ln q` from `⌊q⌋_W`. -/
def lnRatMulBracket (q : AzRat) (y : AzFloat) (ey : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let W := expWork ey w
  mulBracketAny y (lnFloorBracket (ofAzRatRound q W .Floor).1 W) W

/-- The bracket of `q^y` at working precision `w`. -/
def ratPowBracket (q : AzRat) (y : AzFloat) (ey : AzInt) (w : Nat) : AzFloat × AzFloat :=
  expOfBracket (lnRatMulBracket q y ey w) w

/-- `ratPowBracket` as a pair of `Roundable`s for the Ziv loop, negated and swapped when `neg`. -/
def ratPowApprox (neg : Bool) (q : AzRat) (y : AzFloat) (ey : AzInt) (w : Nat) :
    Roundable × Roundable :=
  let r := ratPowBracket q y ey w
  if neg then (fun p mode => setPrecRound (-r.2) p mode, fun p mode => setPrecRound (-r.1) p mode)
  else (fun p mode => setPrecRound r.1 p mode, fun p mode => setPrecRound r.2 p mode)

/-- A computable bound `E ≥ ⌊2 |ln q|⌋ + 2`: `2 (size num + size den) + 2`. -/
def ratPowE (q : AzRat) : Nat := 2 * (q.num.size + q.den.size) + 2

/-- The precision from which the width bound of `lnRatMulBracket` is below `1`:
`136 + max(ey, 0) + ratPowE q`. -/
def ratPowW₀ (ey : AzInt) (q : AzRat) : Nat :=
  136 + (if ey.sign then ey.abs.toNat else 0) + ratPowE q

/-- The starting precision of the Ziv loop for `q^y` at precision `p`. -/
def ratPowStart (ey : AzInt) (q : AzRat) (p : Nat) : Nat := p + zivGuardBits + ratPowW₀ ey q

/-! ### The exact powers -/

/-- The `2^J`-th root of a natural `m ≥ 1`, if any: `m = m' 2^c` with `m'` odd is a `2^J`-th
power iff `m'` is one (`oddPow2Root`) and `2^J ∣ c`. -/
def natPow2Root? (m : AzNat) (J : Nat) : Option AzNat :=
  let mc := splitOdd m
  match oddPow2Root mc.1 J with
  | some u =>
    if mc.2 = 0 then some u
    else if mc.2.size ≤ J then none
    else if mc.2 % 2 ^ J = 0 then some (u.shiftLeft (mc.2 / 2 ^ J)) else none
  | none => none

/-- For `q = a/b` in lowest terms and a non-integer `y = ±my 2^(ey − size my)`: `some (u, v, N)`
with `q^y = (u/v)^N` exactly when `q^y` is rational (`y = N/2^J`, `a = u^(2^J)`,
`b = v^(2^J)`), `none` when it is irrational. -/
def ratPowExact? (a b : AzNat) (sy : Bool) (ey : AzInt) (my : AzNat) :
    Option (AzNat × AzNat × AzInt) :=
  let nc := splitOdd my
  let J : Nat := ((AzNat.ofNat my.size).toAzInt - (AzNat.ofNat nc.2).toAzInt - ey).abs.toNat
  match natPow2Root? a J, natPow2Root? b J with
  | some u, some v => some (u, v, AzInt.mkNorm sy nc.1)
  | _, _ => none

/-- The exact `(a/b)^n` is cheap and may be a `p`-bit float or a midpoint: both `a^n` and
`b^n` pass `powIntCheap`. -/
def ratPowIntCheap (a b : AzNat) (n : AzInt) (p : Nat) : Bool :=
  powIntCheap a n p && powIntCheap b n p

end Azurite.AzFloat
