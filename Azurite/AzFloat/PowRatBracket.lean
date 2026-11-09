/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBracket
import Azurite.AzNat.RootInt
import Azurite.AzRat.Basic

/-!
## The bracket of `x^q` for a float `x > 0` and a rational `q`, and the exact powers

`x^q = exp (q ln x)`.  The rational `q` enters through the float `y = ⌊q⌋_W` below it
(`ofAzRatRound q W .Floor`, `|q − y| ≤ 2 |q| 2^(−W)`): `lnMulRatBracket x ex q w` is the bracket
`lnMulBracket x ex y eq w` of `y ln x` (`eq = ratExpBound q`, an exponent bound for `y`) widened
on both sides by the slack `powRatSlack q ex W = 2^(eq + size(|ex| + 1) + 1 − W)`, which covers
`|q − y| |ln x| ≤ 2 |q| 2^(−W) (|ex| + 1)`.  `powRatBracket` is `expOfBracket` of it and
`powRatApprox neg` the ends as `Roundable`s, negated and swapped for a negative result.  The
width is below `1` from `w ≥ powRatW₀ q ex` on (`Equiv/PowRatBracket.lean`).

**Exact powers.**  For `x = m 2^t` with `m` odd and `q = N/D` in lowest terms with `D ≥ 2`, `x^q`
is rational iff `D ∣ t` and `m = u^D` is a `D`-th power (`oddRootD`: `1` for `m = 1`, impossible
for `D ≥ size m` when `m ≥ 3`, otherwise `rootInt` and a check), and then `x^q = (u 2^(t/D))^N`
(`powRatExact?`), an integer power of a float; otherwise `x^q` is irrational.
-/

namespace Azurite.AzFloat

/-- An exponent bound for `|q|`: `|q| < 2^(size num − size den + 1)`, taken with one bit of
margin for the float below `q`. -/
def ratExpBound (q : AzRat) : AzInt :=
  (AzNat.ofNat (q.num.size + 2)).toAzInt - (AzNat.ofNat q.den.size).toAzInt

/-- The slack `2^(eq + size(|ex| + 1) + 1 − W)` covering `|q − ⌊q⌋_W| |ln x|`. -/
def powRatSlack (q : AzRat) (ex : AzInt) (W : Nat) : AzFloat :=
  powerOf2 (ratExpBound q + (AzNat.ofNat (ex.abs + 1).size).toAzInt + 1
    - (AzNat.ofNat W).toAzInt)

/-- The bracket of `q ln b` for a positive float `b` of exponent `eb` and a rational `q`, at
working precision `w`: the bracket of `⌊q⌋_W ln b` widened by the slack. -/
def lnMulRatBracket (b : AzFloat) (eb : AzInt) (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let eq := ratExpBound q
  let W := expWork eq w
  let B := lnMulBracket b eb (ofAzRatRound q W .Floor).1 eq w
  let S := powRatSlack q eb W
  ((subPrecRound B.1 S W .Floor).1, (addPrecRound B.2 S W .Ceiling).1)

/-- The bracket of `b^q` at working precision `w`. -/
def powRatBracket (b : AzFloat) (eb : AzInt) (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  expOfBracket (lnMulRatBracket b eb q w) w

/-- `powRatBracket` as a pair of `Roundable`s for the Ziv loop, negated and swapped when `neg`. -/
def powRatApprox (neg : Bool) (b : AzFloat) (eb : AzInt) (q : AzRat) (w : Nat) :
    Roundable × Roundable :=
  let r := powRatBracket b eb q w
  if neg then (fun p mode => setPrecRound (-r.2) p mode, fun p mode => setPrecRound (-r.1) p mode)
  else (fun p mode => setPrecRound r.1 p mode, fun p mode => setPrecRound r.2 p mode)

/-- The precision from which the width bound of `lnMulRatBracket` is below `1`. -/
def powRatW₀ (q : AzRat) (eb : AzInt) : Nat :=
  powW₀ (ratExpBound q) eb + (eb.abs + 1).size + 1

/-- The starting precision of the Ziv loop for `x^q` at precision `p`. -/
def powRatStart (q : AzRat) (eb : AzInt) (p : Nat) : Nat :=
  max (p + zivGuardBits) (powRatW₀ q eb)

/-! ### The exact powers -/

/-- The `D`-th root of an odd `m`, if `m` is a `D`-th power: `1` for `m = 1`; none for `m ≥ 3`
and `D ≥ size m`; otherwise `rootInt` and a check. -/
def oddRootD (m : AzNat) (D : AzNat) : Option AzNat :=
  if m = AzNat.ofNat 1 then some (AzNat.ofNat 1)
  else if AzNat.ofNat m.size ≤ D then none
  else
    let k := D.toNat
    let r := m.rootInt k
    if r.pow k = m then some r else none

/-- For `x = mx 2^(ex − size mx) > 0` and `q = ±num/den` in lowest terms, `den ≥ 2`: `some (z, N)`
with `x^q = z^N` exactly when `x^q` is rational (`x = m 2^t`, `m` odd, `den ∣ t`,
`m = u^den`, `z = u 2^(t/den)`, `N = ±num`), `none` when it is irrational. -/
def powRatExact? (ex : AzInt) (mx : AzNat) (q : AzRat) : Option (AzFloat × AzInt) :=
  let mc := splitOdd mx
  let t : AzInt := ex - (AzNat.ofNat mx.size).toAzInt + (AzNat.ofNat mc.2).toAzInt
  let D := q.den.toAzInt
  if t.emod D = 0 then
    match oddRootD mc.1 q.den with
    | some u =>
      let t' := t.ediv D
      some (mkFinite true (t' + (AzNat.ofNat u.size).toAzInt) u.size u, AzInt.mkNorm q.sign q.num)
    | none => none
  else none

end Azurite.AzFloat
