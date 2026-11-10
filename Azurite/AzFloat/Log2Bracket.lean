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
def log2QuotientsWith (c b : AzFloat × AzFloat) (w : Nat) : AzFloat × AzFloat :=
  (if b.1.isNegative then (divPrecRound b.1 c.1 w .Floor).1 else (divPrecRound b.1 c.2 w .Floor).1,
    if b.2.isNegative then (divPrecRound b.2 c.2 w .Ceiling).1
    else (divPrecRound b.2 c.1 w .Ceiling).1)

/-- `log2QuotientsWith` with the bracket of `ln 2` computed at `w`. -/
def log2Quotients (b : AzFloat × AzFloat) (w : Nat) : AzFloat × AzFloat :=
  log2QuotientsWith (ln2Bracket w) b w

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
  let b := log2Quotients (lnP1BracketOf lnFloorBracket x w) w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-! ### The same with precomputed constants -/

/-- `log2Approx` with the constants `c` (the brackets of `ln x` and of `ln 2`). -/
def log2ApproxWith (c : LnConsts) (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := log2QuotientsWith (c.ln2At w) (lnBracketWith c x e w) w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- `log2RatApprox` with the constants `c`. -/
def log2RatApproxWith (c : LnConsts) (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := log2QuotientsWith (c.ln2At w) (lnFloorBracketWith c (ofAzRatRound q w .Floor).1 w) w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- `log2P1Approx` with the constants `c`. -/
def log2P1ApproxWith (c : LnConsts) (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  let b := log2QuotientsWith (c.ln2At w) (lnP1BracketOf (lnFloorBracketWith c) x w) w
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

/-- The rounding test for a value `v ∈ (K/k, K/k + 2^(1−K)]` with `k > 0`: `roundingPossible` on
the exact quotient `K/k` (given by its rounding procedure) and the float
`⌈⌈K/k⌉ + 2^(1−K)⌉` at `p + 72` bits. -/
def pow2P1Core (K k : AzInt) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let w := p + zivGuardBits + 8
  let a := ofAzInt K
  let b := ofAzInt k
  let c := (divPrecRound a b w .Ceiling).1
  let hi := (addPrecRound c (one <<< (AzInt.ofInt 1 - K)) w .Ceiling).1
  roundingPossible (fun P M => divPrecRound a b P M) (fun P M => setPrecRound hi P M) p mode

/-- The rounding of `(K + ε)/k` for `0 < ε ≤ 2^(1−K)` and `k ≠ 0`, when the test of
`pow2P1Core` decides it (for `k < 0`: the test on the negated value in the negated mode). -/
def pow2P1Fast? (K k : AzInt) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  if k.sign then pow2P1Core K k p mode
  else (pow2P1Core K (-k) p (-mode)).map fun r => (-r.1, r.2.swap)

/-- **The power-of-two path of `log₂ (1 + x) / k`**: for `x = 2^K` exactly,
`log₂ (1 + x) = K + ε` with `0 < ε = log₂ (1 + 2^(−K)) ≤ 2^(1−K)`, so the value is `K/k` plus a
tiny one-sided perturbation.  When `K/k` is a rounding boundary (always for `k = ±1`) the Ziv
loop would need about `K` bits to see the side; `pow2P1Fast?` decides it at `p + 72` bits, at a
cost independent of `K`.  `none` when `x` is not a positive power of two or the test fails. -/
def log2P1Pow2Fast? (x : AzFloat) (k : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  match x with
  | finite true e _ m _ => if m.isPowerOfTwo then pow2P1Fast? (e - 1) k p mode else none
  | _ => none

end Azurite.AzFloat
