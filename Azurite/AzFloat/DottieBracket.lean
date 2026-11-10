/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cos
import Azurite.AzFloat.Float64
import Azurite.AzFloat.Sqrt

/-!
## The bracket of the Dottie number

The Dottie number `d = 0.739085…` is the solution of `cos x = x`.  `dottieBracket w` encloses it
at Ziv level `w` (working precision `W = w + 8`):

* **Verification.**  For any float `n ∈ [0, 1]`, `|n − d| ≤ |n − cos n|` (`cos` decreases on
  `[0, 1]`), so `dottieMvt n W = [n − δ, n + δ]` with `δ ≥ |n − cos n|` from `cosBracket n`
  encloses `d`, with width about `4 |n − d|`.
* **Candidate (unverified).**  Newton's iteration for `x − cos x = 0`,
  `x ← x − (x − cos x)/(1 + sin x)` with `sin x = √(1 − cos² x)`, from a `Float` seed, the
  precision doubling (`dottieRefine`: precisions `P + 16`, `2P + 16`, … from `P = 64`, so that
  every step is saturated), then clamped into `[0, 1]`.  The bracket around it is used when its
  width is at most `2^(−w)`.
* **Fallback (proven convergence).**  Otherwise `8W` steps of `x ← cos x` (the lower end of
  `cosBracket`, clamped into `[0, 1]`) from `1/2`: the iteration contracts by `9/10` per step,
  so the bracket around the result has width `O(2^(−W))`.  This is what makes the width bound,
  and with it the Ziv certificate, provable; it never runs in practice.

`dottieApprox` is the pair of `Roundable`s for the Ziv loop (`AzFloat/Dottie.lean`).
-/

namespace Azurite.AzFloat

/-- A float clamped into `[0, 1]` (`1/2` when it is not finite). -/
def dottieClamp (x : AzFloat) : AzFloat :=
  if x.isFinite then maxOf zero (minOf one x) else oneHalf

/-- The verified bracket `[n − δ, n + δ] ∋ d` around a float `n ∈ [0, 1]`, with
`δ ≥ |n − cos n|` from the bracket of `cos n` at precision `W`. -/
def dottieMvt (n : AzFloat) (W : Nat) : AzFloat × AzFloat :=
  let C := cosBracket n (AzInt.ofInt 1) W
  let δ := maxOf (subPrecRound C.2 n W .Ceiling).1 (subPrecRound n C.1 W .Ceiling).1
  ((subPrecRound n δ W .Floor).1, (addPrecRound n δ W .Ceiling).1)

/-- One Newton step for `x − cos x = 0` at precision `P`. -/
def dottieNewtonStep (x : AzFloat) (P : Nat) : AzFloat :=
  let c := (cosPrecRound x P .Nearest).1
  let s := (sqrtPrecRound (subPrecRound one (mulPrecRound c c P .Nearest).1 P .Nearest).1 P
    .Nearest).1
  let f := (subPrecRound x c P .Nearest).1
  (subPrecRound x (divPrecRound f (addPrecRound one s P .Nearest).1 P .Nearest).1 P .Nearest).1

/-- Newton steps at precisions `P + 16, 2P + 16, …` while `P < W`, then one at `W + 16`.  A step
at precision `P'` from `a` correct bits gives about `min(2a, P')`, so with `a ≥ P/2 + 16` on
entry every step is saturated (`2a ≥ P + 32`), and the last one, from `a ≥ W/2 + 16`, reaches
`W + 16`. -/
def dottieRefine (x : AzFloat) (P W : Nat) : Nat → AzFloat
  | 0 => x
  | fuel + 1 =>
    if W ≤ P then dottieNewtonStep x (W + 16)
    else dottieRefine (dottieNewtonStep x (P + 16)) (2 * P) W fuel

/-- The unverified candidate at working precision `W`, in `[0, 1]`. -/
def dottieCandidate (W : Nat) : AzFloat :=
  dottieClamp (dottieRefine (ofFloat64 0.7390851332151607) 64 W (W + 2))

/-- One step of the contracting iteration `x ← cos x`: the lower end of the bracket of `cos x`,
clamped into `[0, 1]`. -/
def dottieIterStep (W : Nat) (x : AzFloat) : AzFloat :=
  dottieClamp (cosBracket x (AzInt.ofInt 1) W).1

/-- `k` steps of the contracting iteration. -/
def dottieIter (W : Nat) : Nat → AzFloat → AzFloat
  | 0, x => x
  | k + 1, x => dottieIterStep W (dottieIter W k x)

/-- The bracket of the Dottie number at Ziv level `w`. -/
def dottieBracket (w : Nat) : AzFloat × AzFloat :=
  let W := w + 8
  let I := dottieMvt (dottieCandidate W) W
  if le (subPrecRound I.2 I.1 64 .Ceiling).1 (one <<< AzInt.ofInt (-(w : Int))) then I
  else dottieMvt (dottieIter W (8 * W) oneHalf) W

/-- `dottieBracket` as a pair of `Roundable`s for the Ziv loop. -/
def dottieApprox (w : Nat) : Roundable × Roundable :=
  let b := dottieBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
