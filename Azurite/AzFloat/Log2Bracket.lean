/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBracket

/-!
## The bracket of `log₂ x`

`log₂ x = ln x / ln 2`: the quotient of the bracket of `ln x` (`lnBracket`, one AGM run) by the
bracket of `ln 2` (`ln2Bracket`), with directed rounding (`log2Quotients`).  The sign of the
numerator decides which end of the `ln 2` bracket makes the quotient an outer bound: for the
lower end `⌊a/d⌋` if `a ≥ 0` and `⌊a/c⌋` if `a < 0` (`c ≤ ln 2 ≤ d`), symmetrically for the upper
end.  `log2Approx` takes the `ln x` bracket of a float, `log2RatApprox` that of a rational
(`lnFloorBracket` of `⌊q⌋_w`).  Exact powers of two are handled by the drivers and never reach
the brackets.
-/

namespace Azurite.AzFloat

/-- The quotient of a bracket `b` of `ln x` by the bracket of `ln 2`, rounded outward: the sign of
each end of `b` selects the end of the `ln 2` bracket that makes the quotient an outer bound. -/
def log2Quotients (b : AzFloat × AzFloat) (w : Nat) : AzFloat × AzFloat :=
  let c := ln2Bracket w
  (if b.1.isNegative then (divPrecRound b.1 c.1 w .Floor).1 else (divPrecRound b.1 c.2 w .Floor).1,
    if b.2.isNegative then (divPrecRound b.2 c.2 w .Ceiling).1
    else (divPrecRound b.2 c.1 w .Ceiling).1)

/-- The bracket of `log₂ x` for a positive finite float `x` of exponent `e` at working precision
`w`. -/
def log2Approx (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := log2Quotients (lnBracket x e w) w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `log₂ q` for a positive rational `q` at working precision `w`: the quotient
of the bracket of `ln q` from the float `⌊q⌋_w` (`lnFloorBracket`) by the bracket of `ln 2`. -/
def log2RatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := log2Quotients (lnFloorBracket (ofAzRatRound q w .Floor).1 w) w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `log₂ (1 + x)` for a float `x > −1` at working precision `w`: the quotient of
the bracket of `ln (1 + x)` from the float `⌊1 + x⌋_w` (`lnFloorBracket`) by the bracket of
`ln 2`. -/
def log2P1Approx (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  let b := log2Quotients (lnFloorBracket (addPrecRound one x w .Floor).1 w) w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- Whether `1 + x` is exactly a power of two `2^k`, and then `k`: the floor and the ceiling of
`1 + x` at precision `w` coincide (so the sum is exact) and the significand is a power of two
(so the sum is `2^(e−1)`).  A power of two is representable at every precision `w ≥ 1`, so `none`
means that `1 + x` is not a power of two (`onePlusPow2Exponent?_none`). -/
def onePlusPow2Exponent? (x : AzFloat) (w : Nat) : Option AzInt :=
  let sLo := (addPrecRound one x w .Floor).1
  let sHi := (addPrecRound one x w .Ceiling).1
  match sLo with
  | finite true e _ m _ => if eqIEEE sLo sHi && m.isPowerOfTwo then some (e - 1) else none
  | _ => none

end Azurite.AzFloat
