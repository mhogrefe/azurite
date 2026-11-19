/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.PiBracket
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.SqrtPiBracket
import Azurite.AzFloat.Ziv

/-!
## The brackets of `e^π`, `2^√2` and `e^(π √163)`

Each is the exponential of a bracket (`expOfBracket`, `AzFloat/ExpApprox.lean`): of `π`, of
`√2 ln 2` and of `π √163`.  The three values are irrational by the Gelfond–Schneider theorem
(`Transcendental/GelfondSchneider.lean`), and the brackets converge, so the Ziv loops of
`AzFloat/Gelfond.lean`, `AzFloat/GelfondSchneider.lean` and `AzFloat/Ramanujan.lean` have
termination certificates (`Equiv/GelfondBracket.lean`).
-/

namespace Azurite.AzFloat

/-- The bracket of `e^π` at working precision `w`. -/
def gelfondBracket (w : Nat) : AzFloat × AzFloat := expOfBracket (piBracket w) w

/-- The two ends of the `e^π` bracket, rounded at any requested precision. -/
def gelfondApprox (w : Nat) : Roundable × Roundable :=
  let b := gelfondBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

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

end Azurite.AzFloat
