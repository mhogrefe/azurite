/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PiBracket
import Azurite.AzFloat.LogBaseFloatBracket
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.Rsqrt

/-!
## Brackets of `√π`, `1/√π` and `1/√τ`

`sqrtBracket B w` takes the square roots of the two ends of a bracket with directed rounding,
and `rsqrtBracket B w` the reciprocal square roots (swapping the ends): one `sqrtPrecRound` or
`rsqrtPrecRound` per end, no division.  `sqrtPiBracket` applies the former to the bracket of
`π` with the lower end raised to `2` (`piBracket2`), `oneDivSqrtPiBracket` the latter, and
`oneDivSqrtTauBracket` the latter to the same bracket shifted by one bit (`τ = 2π`).  Each
comes with its pair of `Roundable`s for the Ziv loop; `2/√π` is an exact shift
(`AzFloat/PiConstants`).
-/

namespace Azurite.AzFloat

/-- The square roots of the ends of a bracket, rounded outward at precision `w`. -/
def sqrtBracket (B : AzFloat × AzFloat) (w : Nat) : AzFloat × AzFloat :=
  ((sqrtPrecRound B.1 w .Floor).1, (sqrtPrecRound B.2 w .Ceiling).1)

/-- The reciprocal square roots of the ends of a bracket (swapped), rounded outward at
precision `w`. -/
def rsqrtBracket (B : AzFloat × AzFloat) (w : Nat) : AzFloat × AzFloat :=
  ((rsqrtPrecRound B.2 w .Floor).1, (rsqrtPrecRound B.1 w .Ceiling).1)

/-- The bracket of `π` with the lower end raised to `2`. -/
def piBracket2 (w : Nat) : AzFloat × AzFloat :=
  let b := piBracket w
  (maxOf b.1 two, b.2)

/-- The bracket of `√π`. -/
def sqrtPiBracket (w : Nat) : AzFloat × AzFloat := sqrtBracket (piBracket2 w) w

/-- The two ends of the `√π` bracket, rounded at any requested precision. -/
def sqrtPiApprox (w : Nat) : Roundable × Roundable :=
  let b := sqrtPiBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `1/√π`. -/
def oneDivSqrtPiBracket (w : Nat) : AzFloat × AzFloat := rsqrtBracket (piBracket2 w) w

/-- The two ends of the `1/√π` bracket, rounded at any requested precision. -/
def oneDivSqrtPiApprox (w : Nat) : Roundable × Roundable :=
  let b := oneDivSqrtPiBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `1/√τ = 1/√(2π)`. -/
def oneDivSqrtTauBracket (w : Nat) : AzFloat × AzFloat :=
  let b := piBracket2 w
  rsqrtBracket (b.1 <<< AzInt.ofInt 1, b.2 <<< AzInt.ofInt 1) w

/-- The two ends of the `1/√τ` bracket, rounded at any requested precision. -/
def oneDivSqrtTauApprox (w : Nat) : Roundable × Roundable :=
  let b := oneDivSqrtTauBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
