/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2Bracket
import Azurite.AzFloat.Conversion

/-!
# The bracket of `log_b x` for a natural base

`logBaseApprox x e b w` brackets `log_b x = ln x / ln b` for a positive finite float `x` of
exponent `e` and a base `b : UInt64` (`b ≥ 2`): the quotient of the bracket of `ln x`
(`lnBracket`) by a bracket of `ln b`, rounded outward (`quotientBracket`, the shape of
`log2Quotients` with an arbitrary divisor bracket).  The bracket of `ln b` is `lnBracket` of
the float `b`, its lower end raised to `1/2` (`lnBaseBracket`) so that the divisor is provably
positive at every working precision.
-/

namespace Azurite.AzFloat

/-- The quotient of a bracket `bx` of `L` by a positive bracket `cd` of `M`, rounded outward:
the sign of each end picks the divisor end that moves the quotient outward. -/
def quotientBracket (bx cd : AzFloat × AzFloat) (w : Nat) : AzFloat × AzFloat :=
  (if bx.1.isNegative then (divPrecRound bx.1 cd.1 w .Floor).1
    else (divPrecRound bx.1 cd.2 w .Floor).1,
    if bx.2.isNegative then (divPrecRound bx.2 cd.2 w .Ceiling).1
    else (divPrecRound bx.2 cd.1 w .Ceiling).1)

/-- The float `1/2`. -/
def halfFloat : AzFloat := powerOf2 (-(1 : AzInt))

/-- `z` raised to `1/2` if below it. -/
def clampHalf (z : AzFloat) : AzFloat :=
  if partialCompare z halfFloat == some .lt then halfFloat else z

/-- The base as a float. -/
def baseFloat (b : UInt64) : AzFloat := ofAzNat (AzNat.ofNat b.toNat)

/-- A bracket of `ln b` for `b ≥ 2` at working precision `w`, with lower end at least `1/2`. -/
def lnBaseBracket (b : UInt64) (w : Nat) : AzFloat × AzFloat :=
  let y := baseFloat b
  let B := lnBracket y (y.exponent?.getD 0) w
  (clampHalf B.1, B.2)

/-- The bracket of `log_b x` for a positive finite float `x` of exponent `e` at working
precision `w`. -/
def logBaseApprox (x : AzFloat) (e : AzInt) (b : UInt64) (w : Nat) : Roundable × Roundable :=
  let q := quotientBracket (lnBracket x e w) (lnBaseBracket b w) w
  (fun p mode => setPrecRound q.1 p mode, fun p mode => setPrecRound q.2 p mode)

/-- The bracket of `log_b q` for a positive rational `q` at working precision `w`: the rational
`ln` bracket (`lnFloorBracket` of the floor-rounded `q`) divided by the bracket of `ln b`. -/
def logBaseRatApprox (q : AzRat) (b : UInt64) (w : Nat) : Roundable × Roundable :=
  let qb := quotientBracket (lnFloorBracket (ofAzRatRound q w .Floor).1 w) (lnBaseBracket b w) w
  (fun p mode => setPrecRound qb.1 p mode, fun p mode => setPrecRound qb.2 p mode)

/-- The bracket of `log_b (1 + x)` at working precision `w`: the `ln (1 + x)` bracket of `lnP1`
(`lnFloorBracket` of the floor-rounded sum `1 + x`) divided by the bracket of `ln b`. -/
def logBaseP1Approx (x : AzFloat) (b : UInt64) (w : Nat) : Roundable × Roundable :=
  let qb := quotientBracket (lnP1BracketOf lnFloorBracket x w) (lnBaseBracket b w) w
  (fun p mode => setPrecRound qb.1 p mode, fun p mode => setPrecRound qb.2 p mode)

/-! ### Precomputed constants for a natural base -/

/-- **Precomputed constants for `log_b`** with a natural base `b`: the constants of `ln`
(`LnConsts`, the brackets of `π` and `ln 2`) and the bracket of `ln b` at the same working
precision `ln.W`; `LogBaseConsts.make b W` builds them (`LogBaseConsts.forPrecision b p` in
`LogBase.lean`).  The proof field pins `lnB` to `lnBaseBracket b ln.W` and is erased at runtime. -/
structure LogBaseConsts where
  /-- The base. -/
  base : UInt64
  /-- The constants of `ln` (and of `log₂`, for a power-of-two base). -/
  ln : LnConsts
  /-- The bracket of `ln base` at precision `ln.W`. -/
  lnB : AzFloat × AzFloat
  lnB_eq : lnB = lnBaseBracket base ln.W

/-- The constants for `log_b` at working precision `W`. -/
def LogBaseConsts.make (b : UInt64) (W : Nat) : LogBaseConsts :=
  ⟨b, LnConsts.make W, lnBaseBracket b W, rfl⟩

/-- The bracket of `ln base` for working precision `w`: from the constants when their precision
suffices, computed otherwise. -/
def LogBaseConsts.lnBAt (cb : LogBaseConsts) (w : Nat) : AzFloat × AzFloat :=
  if w ≤ cb.ln.W then cb.lnB else lnBaseBracket cb.base w

/-- `logBaseApprox` with the constants `cb` (base `cb.base`). -/
def logBaseApproxWith (cb : LogBaseConsts) (x : AzFloat) (e : AzInt) (w : Nat) :
    Roundable × Roundable :=
  let q := quotientBracket (lnBracketWith cb.ln x e w) (cb.lnBAt w) w
  (fun p mode => setPrecRound q.1 p mode, fun p mode => setPrecRound q.2 p mode)

/-- `logBaseRatApprox` with the constants `cb`. -/
def logBaseRatApproxWith (cb : LogBaseConsts) (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let qb := quotientBracket (lnFloorBracketWith cb.ln (ofAzRatRound q w .Floor).1 w)
    (cb.lnBAt w) w
  (fun p mode => setPrecRound qb.1 p mode, fun p mode => setPrecRound qb.2 p mode)

/-- `logBaseP1Approx` with the constants `cb`. -/
def logBaseP1ApproxWith (cb : LogBaseConsts) (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  let qb := quotientBracket (lnP1BracketOf (lnFloorBracketWith cb.ln) x w)
    (cb.lnBAt w) w
  (fun p mode => setPrecRound qb.1 p mode, fun p mode => setPrecRound qb.2 p mode)

end Azurite.AzFloat
