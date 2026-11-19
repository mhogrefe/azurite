/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Agm
import Azurite.AzFloat.Cbrt
import Azurite.AzFloat.Constants
import Azurite.AzFloat.Div
import Azurite.AzFloat.Interval
import Azurite.AzFloat.LnGammaBracket
import Azurite.AzFloat.PiBracket

/-!
## The enclosures of the constants computed with the AGM

`Γ(1/4)`, `Γ(1/3)` (`gammaOneQuarterEncl`, `gammaOneThirdEncl`: one interval AGM, the bracket
of `π` and a few roots), Gauss's constant `G = 1/AGM(1, √2)` (`gaussBracket`) and the
lemniscate constant `ϖ = π G` (`lemniscateBracket`), with the square root, the cube root and
the AGM on enclosures (`Encl.sqrt`, `Encl.cbrt`, `Encl.agm`).

The four values are irrational — by Chudnovsky's theorem (`Azurite/Chudnovsky`: `π` and
`Γ(1/4)`, and `π` and `Γ(1/3)`, are algebraically independent) — and the enclosures converge
(`Equiv/EnclConv.lean`), so the Ziv loops of `AzFloat/GammaConstants.lean`,
`AzFloat/GaussConstant.lean` and `AzFloat/Lemniscate.lean` have termination certificates
(`Equiv/AgmConstants.lean`).
-/

namespace Azurite.AzFloat

namespace Encl

/-- `√[a]` for a nonnegative enclosure. -/
def sqrt (w : Nat) (a : Encl) : Encl :=
  ((sqrtPrecRound a.1 w .Floor).1, (sqrtPrecRound a.2 w .Ceiling).1)

/-- `∛[a]` for a nonnegative enclosure. -/
def cbrt (w : Nat) (a : Encl) : Encl :=
  ((cbrtPrecRound a.1 w .Floor).1, (cbrtPrecRound a.2 w .Ceiling).1)

/-- `AGM([a], [b])` for positive enclosures: the interval iteration from the four ends, at
least one step, until the bracket `[b_n, a_n]` is narrow.  Should the lower end not come out
positive, it is replaced by the smaller of the two lower ends, which is below the AGM too. -/
def agm (w : Nat) (a b : Encl) : Encl :=
  let s := agmIter w (w + 4) (agmStep w ⟨a.1, a.2, b.1, b.2⟩)
  (if lt zero s.bLo then s.bLo else if le a.1 b.1 then a.1 else b.1, s.aHi)

end Encl

/-- An enclosure of `Γ(1/4) = √(2π √(2π) / AGM(1, √2))` at Ziv level `w`. -/
def gammaOneQuarterEncl (w : Nat) : Encl :=
  let W := w + 32
  let M := Encl.agm W (Encl.exact one) (Encl.sqrt W (Encl.nat 2))
  let T := Encl.mul W (Encl.nat 2) (Encl.pi W)
  Encl.sqrt W (Encl.div W (Encl.mul W T (Encl.sqrt W T)) M)

/-- An enclosure of `Γ(1/3) = ∛(2 ∛2 π² / AGM(√((√3 + 3/2)/2), √√3))` at Ziv level `w`. -/
def gammaOneThirdEncl (w : Nat) : Encl :=
  let W := w + 32
  let r := Encl.sqrt W (Encl.nat 3)
  let A := Encl.sqrt W (Encl.half (Encl.add W r (Encl.half (Encl.nat 3))))
  let M := Encl.agm W A (Encl.sqrt W r)
  let P := Encl.pi W
  let N := Encl.mul W (Encl.mul W (Encl.nat 2) (Encl.cbrt W (Encl.nat 2))) (Encl.mul W P P)
  Encl.cbrt W (Encl.div W N M)

/-- The bracket of `Γ(1/4)` as a pair of `Roundable`s, the lower end strictly below it. -/
def gammaOneQuarterApprox (w : Nat) : Roundable × Roundable :=
  lnGammaApproxOf (gammaOneQuarterEncl w) w

/-- The bracket of `Γ(1/3)` as a pair of `Roundable`s, the lower end strictly below it. -/
def gammaOneThirdApprox (w : Nat) : Roundable × Roundable :=
  lnGammaApproxOf (gammaOneThirdEncl w) w

/-- The two ends of the bracket of `G = 1/AGM(1, √2)` at working precision `w`. -/
def gaussBracket (w : Nat) : AzFloat × AzFloat :=
  let s2lo := (sqrt2PrecRound w .Floor).1
  let s2hi := (sqrt2PrecRound w .Ceiling).1
  let s := agmIter w (w + 4) (agmStep w ⟨one, one, s2lo, s2hi⟩)
  ((divPrecRound one s.aHi w .Floor).1, (divPrecRound one s.bLo w .Ceiling).1)

/-- The bracket of `G` at working precision `w`, as a pair of `Roundable`s. -/
def gaussApprox (w : Nat) : Roundable × Roundable :=
  let b := gaussBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The two ends of the bracket of `ϖ = π · G` at working precision `w`. -/
def lemniscateBracket (w : Nat) : AzFloat × AzFloat :=
  let pb := piBracket w
  let gb := gaussBracket w
  ((mulPrecRound pb.1 gb.1 w .Floor).1, (mulPrecRound pb.2 gb.2 w .Ceiling).1)

/-- The bracket of `ϖ` at working precision `w`, as a pair of `Roundable`s. -/
def lemniscateApprox (w : Nat) : Roundable × Roundable :=
  let b := lemniscateBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
