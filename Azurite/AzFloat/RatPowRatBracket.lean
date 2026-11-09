/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowRatBracket
import Azurite.AzFloat.RatPowBracket

/-!
## The bracket of `q^r` for rationals `q > 0` and `r`, and the exact powers

`q^r = exp (r ln q)`: the bracket of `ln q` comes from the float `⌊q⌋_W` below `q`
(`lnRatMulBracket`, the rational-base power), the exponent enters through the float `⌊r⌋_W`
below it, and the slack `ratPowRatSlack r q W = 2^(er + size(size num + size den) + 1 − W)`
covers `|r − ⌊r⌋_W| |ln q|` (the rational-exponent power).  `ratPowRatBracket` is
`expOfBracket` of the widened bracket and `ratPowRatApprox neg` the ends as `Roundable`s.

**Exact powers.**  For `q = a/b` in lowest terms and `r = N/D` in lowest terms with `D ≥ 2`,
`q^r` is rational iff `a` and `b` are both `D`-th powers (`natRootD?`: `oddRootD` of the odd part
and `D ∣` the power-of-two exponent), and then `q^r = (u/v)^N` (`ratPowRatExact?`).
-/

namespace Azurite.AzFloat

/-- The slack `2^(er + size(size num_q + size den_q) + 1 − W)` covering `|r − ⌊r⌋_W| |ln q|`. -/
def ratPowRatSlack (r q : AzRat) (W : Nat) : AzFloat :=
  powerOf2 (ratExpBound r + (AzNat.ofNat (q.num.size + q.den.size).size).toAzInt + 1
    - (AzNat.ofNat W).toAzInt)

/-- The bracket of `r ln q` for rationals `q > 0` and `r`, at working precision `w`: the bracket
of `⌊r⌋_W ln q` widened by the slack. -/
def lnRatMulRatBracket (q r : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let er := ratExpBound r
  let W := expWork er w
  let B := lnRatMulBracket q (ofAzRatRound r W .Floor).1 er w
  let S := ratPowRatSlack r q W
  ((subPrecRound B.1 S W .Floor).1, (addPrecRound B.2 S W .Ceiling).1)

/-- The bracket of `q^r` at working precision `w`. -/
def ratPowRatBracket (q r : AzRat) (w : Nat) : AzFloat × AzFloat :=
  expOfBracket (lnRatMulRatBracket q r w) w

/-- `ratPowRatBracket` as a pair of `Roundable`s for the Ziv loop, negated and swapped when
`neg`. -/
def ratPowRatApprox (neg : Bool) (q r : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := ratPowRatBracket q r w
  if neg then (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)
  else (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The precision from which the width bound of `lnRatMulRatBracket` is below `1`. -/
def ratPowRatW₀ (r q : AzRat) : Nat :=
  ratPowW₀ (ratExpBound r) q + (q.num.size + q.den.size).size + 1

/-- The starting precision of the Ziv loop for `q^r` at precision `p`. -/
def ratPowRatStart (r q : AzRat) (p : Nat) : Nat := p + zivGuardBits + ratPowRatW₀ r q

/-! ### The exact powers -/

/-- The `D`-th root of a natural `m ≥ 1`, if any: `m = m' 2^c` with `m'` odd is a `D`-th power
iff `m'` is one (`oddRootD`) and `D ∣ c`. -/
def natRootD? (m : AzNat) (D : AzNat) : Option AzNat :=
  let mc := splitOdd m
  match oddRootD mc.1 D with
  | some u =>
    if mc.2 = 0 then some u
    else if AzNat.ofNat mc.2 < D then none
    else if mc.2 % D.toNat = 0 then some (u.shiftLeft (mc.2 / D.toNat)) else none
  | none => none

/-- For `q = a/b` and `r = ±num/den` in lowest terms, `den ≥ 2`: `some (u, v, N)` with
`q^r = (u/v)^N` exactly when `q^r` is rational (`a = u^den`, `b = v^den`), `none` when it is
irrational. -/
def ratPowRatExact? (a b : AzNat) (r : AzRat) : Option (AzNat × AzNat × AzInt) :=
  match natRootD? a r.den, natRootD? b r.den with
  | some u, some v => some (u, v, AzInt.mkNorm r.sign r.num)
  | _, _ => none

end Azurite.AzFloat
