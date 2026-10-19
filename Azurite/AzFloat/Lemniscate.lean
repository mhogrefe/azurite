/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GaussConstant
import Azurite.AzFloat.PiBracket

/-!
## The lemniscate constant

`ϖ = 2 ∫₀¹ dt/√(1 − t⁴) = π · G = π/AGM(1, √2) = 2.62205755429211981046483958989111941368…`
(`Chapter4/Lemniscate.lean`).  The bracket is the product of the brackets of `π`
(`piBracket`) and of Gauss's constant `G` (`gaussBracket`) at the working precision, rounded
outwards (`lemniscateBracket`), and Ziv's loop rounds it.

Termination: `ϖ = Γ(1/4)²/(2√(2π))` is transcendental (Schneider 1937: the periods of an
elliptic curve with algebraic invariants are transcendental; `ϖ` is the real period of
`y² = x³ − x`), but nothing of the kind is in Mathlib, so — as for `G` and the AGM — the loop
has fuel (`agmFuel p`) and the specification is "correctly rounded or `NaN`"
(`Equiv/Lemniscate.lean`).
-/

namespace Azurite.AzFloat

/-- The two ends of the bracket of `ϖ = π · G` at working precision `w`. -/
def lemniscateBracket (w : Nat) : AzFloat × AzFloat :=
  let pb := piBracket w
  let gb := gaussBracket w
  ((mulPrecRound pb.1 gb.1 w .Floor).1, (mulPrecRound pb.2 gb.2 w .Ceiling).1)

/-- The bracket of `ϖ` at working precision `w`, as a pair of `Roundable`s. -/
def lemniscateApprox (w : Nat) : Roundable × Roundable :=
  let b := lemniscateBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- **The lemniscate constant** `ϖ` rounded to precision `p` with `mode`, and the comparison
with the exact value (`NaN` if the fuel runs out). -/
def lemniscateConstantPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  zivLoop lemniscateApprox p mode (agmFuel p) (p + zivGuardBits)

/-- The lemniscate constant rounded to nearest at precision `p`. -/
def lemniscateConstant (p : Nat) : AzFloat := (lemniscateConstantPrecRound p .Nearest).1

end Azurite.AzFloat
