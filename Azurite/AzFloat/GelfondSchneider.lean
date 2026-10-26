/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.Sqrt

/-!
## The Gelfond–Schneider constant `2^√2`

`sqrt2Ln2Bracket w` encloses `√2 ln 2` (the floats below and above `√2` times the ends of
`ln2Bracket w`, directed products) and `gelfondSchneiderBracket w = expOfBracket` of it
(`AzFloat/ExpApprox`).  The Ziv loop (`zivLoop`) has fuel `gelfondSchneiderFuel p` and the
specification is "correctly rounded or `NaN`" (`Equiv/GelfondSchneider.lean`): the termination
certificate would need the irrationality of `2^√2` — the Gelfond–Schneider theorem itself (1934),
not available in Mathlib (see the pending-irrationality ledger in `docs/azfloat_plan.md`).  The
fuel is exhausted only if `2^√2` lies within about `2^(−16p)` of a rounding boundary.
-/

namespace Azurite.AzFloat

/-- The bracket of `√2 ln 2` at working precision `w`. -/
def sqrt2Ln2Bracket (w : Nat) : AzFloat × AzFloat :=
  let L := ln2Bracket w
  let a := (sqrtPrecRound two w .Floor).1
  let b := (sqrtPrecRound two w .Ceiling).1
  ((mulPrecRound a L.1 w .Floor).1, (mulPrecRound b L.2 w .Ceiling).1)

/-- The bracket of `2^√2` at working precision `w`. -/
def gelfondSchneiderBracket (w : Nat) : AzFloat × AzFloat :=
  expOfBracket (sqrt2Ln2Bracket w) w

/-- The two ends of the `2^√2` bracket, rounded at any requested precision. -/
def gelfondSchneiderApprox (w : Nat) : Roundable × Roundable :=
  let b := gelfondSchneiderBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The fuel of the Ziv loop for `2^√2`: enough doublings to reach `16 (p + 64)` bits. -/
def gelfondSchneiderFuel (p : Nat) : Nat := zivFuel (16 * (p + zivGuardBits))

/-- `2^√2` rounded to precision `p` with `mode`, and the comparison with the exact value
(`NaN` at precision `0` or if the fuel runs out). -/
def gelfondSchneiderPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else zivLoop gelfondSchneiderApprox p mode (gelfondSchneiderFuel p) (p + zivGuardBits)

/-- `2^√2` rounded to nearest at precision `p`. -/
def gelfondSchneider (p : Nat) : AzFloat := (gelfondSchneiderPrecRound p .Nearest).1

end Azurite.AzFloat
