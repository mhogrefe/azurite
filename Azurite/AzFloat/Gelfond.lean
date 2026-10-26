/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.PiBracket

/-!
## Gelfond's constant `e^π`

`gelfondBracket w` encloses `e^π`: `expBracketAt` at the lower end `lo` of the bracket of `π`
gives `[a, b] ∋ exp lo`, and the upper end is widened to `b + ⌈b · 2d⌉` for `d = ⌈hi − lo⌉`,
since `exp π ≤ exp lo · exp (π − lo) ≤ exp lo · (1 + 2d)`.  The Ziv loop (`zivLoop`) has fuel
`gelfondFuel p` and the specification is "correctly rounded or `NaN`" (`Equiv/Gelfond.lean`):
the termination certificate would need the irrationality of `e^π` — Gelfond's theorem (1929),
not available in Mathlib (see the pending-irrationality ledger in `docs/azfloat_plan.md`).
The fuel is exhausted only if `e^π` lies within about `2^(−16p)` of a rounding boundary.
-/

namespace Azurite.AzFloat

/-- The bracket of `e^π` at working precision `w`. -/
def gelfondBracket (w : Nat) : AzFloat × AzFloat :=
  let P := piBracket w
  let b := expBracketAt P.1 w
  let d := (subPrecRound P.2 P.1 (w + 8) .Ceiling).1
  let corr := (mulPrecRound b.2 (d <<< AzInt.ofInt 1) (w + 8) .Ceiling).1
  (b.1, (addPrecRound b.2 corr (w + 8) .Ceiling).1)

/-- The two ends of the `e^π` bracket, rounded at any requested precision. -/
def gelfondApprox (w : Nat) : Roundable × Roundable :=
  let b := gelfondBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The fuel of the Ziv loop for `e^π`: enough doublings to reach `16 (p + 64)` bits. -/
def gelfondFuel (p : Nat) : Nat := zivFuel (16 * (p + zivGuardBits))

/-- `e^π` rounded to precision `p` with `mode`, and the comparison with the exact value
(`NaN` at precision `0` or if the fuel runs out). -/
def gelfondPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq) else zivLoop gelfondApprox p mode (gelfondFuel p) (p + zivGuardBits)

/-- `e^π` rounded to nearest at precision `p`. -/
def gelfond (p : Nat) : AzFloat := (gelfondPrecRound p .Nearest).1

end Azurite.AzFloat
