/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.LnBracket
import Azurite.AzInt.DivMod
import Azurite.AzInt.TrailingZeros
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.TrailingZeros

/-!
## The bracket of `x^y` for floats `x > 0` and `y`, and the exact dyadic powers

`x^y = exp (y ln x)`.  `lnMulBracket x ex y ey w` is `y` times the bracket `lnBracket x ex W` of
`ln x` at `W = expWork ey w = w + 16 + max(ey, 0)` bits, the products rounded outward
(`mulBracketAny`: floor and ceiling of `y` times the ends, the ends swapped for `y < 0`; the
bracket of `ln x` may have either sign or straddle `0`), and `powBracket` is `expOfBracket` of
it.  `powApprox neg` gives the ends as `Roundable`s, negated and swapped when the result is to be
negated (a negative base with an odd integer exponent).  The width bound of `lnMulBracket` is
the `mulLnEps ey ex w` of the natural-base power, below `1` from `w ≥ powW₀ ey ex = 136 +
max(ey, 0) + |ex|` on (`Equiv/PowBracket.lean`).

**Exact powers.**  For `x = m 2^t > 0` with `m` odd and a non-integer `y = N/2^J` (`N` odd,
`J ≥ 1`), `x^y` is rational iff `2^J ∣ t` and `m = u^(2^J)` is a `2^J`-th power, and then
`x^y = (u 2^(t/2^J))^N`: `powExact?` performs this test (`splitOdd` for the odd parts, `oddPow2Root`
by `J` square roots, impossible as soon as `J ≥ size m` for `m ≥ 3`) and returns the float
`z = u 2^(t/2^J)` and `N`; otherwise `x^y` is irrational.  The integer power `z^N` is computed
exactly by `powIntPrecRound` when it is cheap and may be a float — `|N| (size u − 1) ≤ p + 1`
(`powIntCheap`) — and otherwise through the bracket, with the certificate that a dyadic with an
odd part of more than `p + 1` bits (or a non-dyadic rational) is never a rounding boundary.
-/

namespace Azurite.AzFloat

/-- `y` times a bracket `B` of any signs, at precision `W`, rounded outward: the ends are
swapped for `y < 0`. -/
def mulBracketAny (y : AzFloat) (B : AzFloat × AzFloat) (W : Nat) : AzFloat × AzFloat :=
  if y.isNegative then ((mulPrecRound y B.2 W .Floor).1, (mulPrecRound y B.1 W .Ceiling).1)
  else ((mulPrecRound y B.1 W .Floor).1, (mulPrecRound y B.2 W .Ceiling).1)

/-- The bracket of `y ln b` for a positive float `b` of exponent `eb` and a float `y` of exponent
`ey`, at working precision `w`. -/
def lnMulBracket (b : AzFloat) (eb : AzInt) (y : AzFloat) (ey : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  let W := expWork ey w
  mulBracketAny y (lnBracket b eb W) W

/-- The bracket of `b^y` at working precision `w`. -/
def powBracket (b : AzFloat) (eb : AzInt) (y : AzFloat) (ey : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  expOfBracket (lnMulBracket b eb y ey w) w

/-- `powBracket` as a pair of `Roundable`s for the Ziv loop, negated and swapped when `neg`. -/
def powApprox (neg : Bool) (b : AzFloat) (eb : AzInt) (y : AzFloat) (ey : AzInt) (w : Nat) :
    Roundable × Roundable :=
  let r := powBracket b eb y ey w
  if neg then (fun p mode => setPrecRound (-r.2) p mode, fun p mode => setPrecRound (-r.1) p mode)
  else (fun p mode => setPrecRound r.1 p mode, fun p mode => setPrecRound r.2 p mode)

/-- The precision from which the width bound of `lnMulBracket` is below `1`:
`136 + max(ey, 0) + |eb|`. -/
def powW₀ (ey eb : AzInt) : Nat :=
  136 + (if ey.sign then ey.abs.toNat else 0) + eb.abs.toNat

/-- The starting precision of the Ziv loop for `x^y` at precision `p`. -/
def powStart (ey eb : AzInt) (p : Nat) : Nat := p + zivGuardBits + powW₀ ey eb

/-! ### The exact powers -/

/-- The odd part of a nonzero `m` and its number of trailing zeros: `m = odd · 2^c`. -/
def splitOdd (m : AzNat) : AzNat × Nat :=
  let c := m.trailingZeros.getD 0
  (m.shiftRight c, c)

/-- The `2^J`-th root of `m` by `J` square roots, `none` if some remainder is nonzero. -/
def iterSqrt : AzNat → Nat → Option AzNat
  | m, 0 => some m
  | m, J + 1 =>
    let r := m.sqrtRem
    if r.2 = 0 then iterSqrt r.1 J else none

/-- The `2^J`-th root of an odd `m`: `1` for `m = 1`; none for `m ≥ 3` and `J ≥ size m` (a
root `≥ 3` would have more than `size m` bits); otherwise `iterSqrt`. -/
def oddPow2Root (m : AzNat) (J : Nat) : Option AzNat :=
  if m = AzNat.ofNat 1 then some (AzNat.ofNat 1) else if m.size ≤ J then none else iterSqrt m J

/-- For `x = mx 2^(ex − size mx) > 0` and a non-integer `y = ±my 2^(ey − size my)`: `some (z, N)`
with `x^y = z^N` exactly when `x^y` is rational (`x = m 2^t`, `m` odd, `y = N/2^J`, `N` odd,
`2^J ∣ t`, `m = u^(2^J)`, `z = u 2^(t/2^J)`), `none` when it is irrational. -/
def powExact? (ex : AzInt) (mx : AzNat) (sy : Bool) (ey : AzInt) (my : AzNat) :
    Option (AzFloat × AzInt) :=
  let mc := splitOdd mx
  let t : AzInt := ex - (AzNat.ofNat mx.size).toAzInt + (AzNat.ofNat mc.2).toAzInt
  let nc := splitOdd my
  let J : Nat := ((AzNat.ofNat my.size).toAzInt - (AzNat.ofNat nc.2).toAzInt - ey).abs.toNat
  if t = 0 ∨ J ≤ t.trailingZeros.getD 0 then
    match oddPow2Root mc.1 J with
    | some u =>
      let t' := t.ediv (AzNat.ofNat (2 ^ J)).toAzInt
      some (mkFinite true (t' + (AzNat.ofNat u.size).toAzInt) u.size u, AzInt.mkNorm sy nc.1)
    | none => none
  else none

/-- The exact power `(m 2^t)^n` is cheap to compute and may be a `p`-bit float (or a midpoint):
`|n| (size (odd part of m) − 1) ≤ p + 1`.  Otherwise its odd part has more than `p + 1` bits
(or it is not dyadic), so it is never a rounding boundary. -/
def powIntCheap (m : AzNat) (n : AzInt) (p : Nat) : Bool :=
  decide (n.abs * AzNat.ofNat ((splitOdd m).1.size - 1) ≤ AzNat.ofNat (p + 1))

/-- The exact `r^n − 1` for a natural `r` is cheap and may be a `p`-bit float or a midpoint:
`|n| (size m' − 1) ≤ p + 3 + 2 size r + size |n|` for the odd part `m'` of `r`.  Otherwise the
odd part of `r^n − 1` has more than `p + 1` bits (`n > 0`: `v₂(r^n − 1) ≤ 2 size r + size n`
by lifting the exponent) or `r^n − 1` is not dyadic (`n < 0`), so it is never a rounding
boundary. -/
def natPowM1Cheap (r : AzNat) (n : AzInt) (p : Nat) : Bool :=
  decide (n.abs * AzNat.ofNat ((splitOdd r).1.size - 1)
    ≤ AzNat.ofNat (p + 3 + 2 * r.size + n.abs.size))

end Azurite.AzFloat
