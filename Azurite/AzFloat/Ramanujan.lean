/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gelfond
import Azurite.AzFloat.SqrtPiBracket

/-!
## Ramanujan's constant `e^(π √163)`

`piSqrt163Bracket w` multiplies the bracket of `π` by the bracket of `√163` (`sqrtBracket` at the
exact float `163`) with directed rounding; `ramanujanBracket w = expOfBracket` of it.  The Ziv
loop (`zivLoop`) has fuel `ramanujanFuel p` and the specification is "correctly rounded or
`NaN`" (`Equiv/Ramanujan.lean`): the termination certificate would need the irrationality of
`e^(π √163)` — Gelfond–Schneider, not available in Mathlib (see the pending-irrationality ledger
in `docs/azfloat_plan.md`).  `e^(π √163) = 262537412640768743.99999999999925…` is within
`7.5 · 10^(−13)` of the integer `640320³ + 744`, so the first Ziv level succeeds only from
precision about `100` on; the loop doubles the working precision until it does.
-/

namespace Azurite.AzFloat

/-- The bracket of `π √163` at working precision `w`. -/
def piSqrt163Bracket (w : Nat) : AzFloat × AzFloat :=
  let P := piBracket w
  let S := sqrtBracket (ofAzNat (AzNat.ofNat 163), ofAzNat (AzNat.ofNat 163)) w
  ((mulPrecRound P.1 S.1 w .Floor).1, (mulPrecRound P.2 S.2 w .Ceiling).1)

/-- The bracket of `e^(π √163)` at working precision `w`. -/
def ramanujanBracket (w : Nat) : AzFloat × AzFloat := expOfBracket (piSqrt163Bracket w) w

/-- The two ends of the `e^(π √163)` bracket, rounded at any requested precision. -/
def ramanujanApprox (w : Nat) : Roundable × Roundable :=
  let b := ramanujanBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The fuel of the Ziv loop for `e^(π √163)`: enough doublings to reach `16 (p + 64)` bits. -/
def ramanujanFuel (p : Nat) : Nat := zivFuel (16 * (p + zivGuardBits))

/-- `e^(π √163)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`NaN` at precision `0` or if the fuel runs out). -/
def ramanujanPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else zivLoop ramanujanApprox p mode (ramanujanFuel p) (p + zivGuardBits)

/-- `e^(π √163)` rounded to nearest at precision `p`. -/
def ramanujan (p : Nat) : AzFloat := (ramanujanPrecRound p .Nearest).1

end Azurite.AzFloat
