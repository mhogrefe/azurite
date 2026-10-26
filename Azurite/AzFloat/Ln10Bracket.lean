/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBracket
import Azurite.AzFloat.LogBaseFloatBracket

/-!
## Brackets of `ln 10`, `log₁₀ e`, `log₂ 10` and `log₁₀ 2`

`ln10Bracket w` is `lnFloorBracket` at the float `10` (one AGM run of `lnBracket`; the floor is
exact), its lower end raised to `2 < ln 10` so that the proven width bound never pushes it below
zero.  The three derived constants are quotients of brackets by `divBracketByPosBracket`:
`log₁₀ e = 1/ln 10`, `log₂ 10 = ln 10 / ln 2`, `log₁₀ 2 = ln 2 / ln 10`.  Each comes as a pair
of `Roundable`s for the Ziv loop.
-/

namespace Azurite.AzFloat

/-- The float `10`. -/
def tenF : AzFloat := ofAzNat (AzNat.ofNat 10)

/-- The bracket of `ln 10`, lower end at least `2`. -/
def ln10Bracket (w : Nat) : AzFloat × AzFloat :=
  let b := lnFloorBracket tenF w
  (maxOf b.1 two, b.2)

/-- The two ends of the `ln 10` bracket, rounded at any requested precision. -/
def ln10Approx (w : Nat) : Roundable × Roundable :=
  let b := ln10Bracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `log₁₀ e = 1/ln 10`. -/
def log10EBracket (w : Nat) : AzFloat × AzFloat :=
  divBracketByPosBracket (one, one) (ln10Bracket w) w

/-- The two ends of the `log₁₀ e` bracket, rounded at any requested precision. -/
def log10EApprox (w : Nat) : Roundable × Roundable :=
  let b := log10EBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `log₂ 10 = ln 10 / ln 2`. -/
def log2TenBracket (w : Nat) : AzFloat × AzFloat :=
  divBracketByPosBracket (ln10Bracket w) (ln2Bracket w) w

/-- The two ends of the `log₂ 10` bracket, rounded at any requested precision. -/
def log2TenApprox (w : Nat) : Roundable × Roundable :=
  let b := log2TenBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `log₁₀ 2 = ln 2 / ln 10`. -/
def log10TwoBracket (w : Nat) : AzFloat × AzFloat :=
  divBracketByPosBracket (ln2Bracket w) (ln10Bracket w) w

/-- The two ends of the `log₁₀ 2` bracket, rounded at any requested precision. -/
def log10TwoApprox (w : Nat) : Roundable × Roundable :=
  let b := log10TwoBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
