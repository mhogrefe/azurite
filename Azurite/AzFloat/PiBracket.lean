/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Agm
import Azurite.AzFloat.Constants
import Azurite.AzFloat.Div
import Azurite.AzInt.Instances
import Azurite.BrentZimmermann.Chapter4.BrentSalamin

/-!
## The Brent–Salamin bracket of `π`

The Gauss–Legendre / Brent–Salamin iteration (MCA §4.8.2, `BrentSalamin.lean`):
`a₀ = 1`, `b₀ = 1/√2`, `s₀ = 1/2`, `a' = (a + b)/2`, `b' = √(ab)`,
`s' = s − 2^(n+1) ((a − b)/2)²`, and `π_N = 2 a_{N+1}²/s_N` with `|π_N − π| ≤ 2^(−w)` for
`N = piSteps w = ⌊lg w⌋ + 1` (`abs_salaminApprox_piSteps_sub_pi_le`).

The iteration runs on a **single triple** `(a, b, s)` at working precision `w`, every operation
rounded down (`piStep`; the shifts are exact), with an a priori error analysis instead of an
interval iteration: after `n` steps the computed values are within `2^(2n+4) 2^(−w)` of `a_n`,
`b_n` and within `2^(3n+7) 2^(−w)` of `s_n` (`PiPoint`, `piPoint_step` in `Equiv/PiBracket.lean`:
the roundings are absolutely small and the step is Lipschitz with constants `≤ 4` and `≤ 8`).
The final `q = ⌊2 ⌊a_{N+1}²⌋/s_N⌋` is within `2^(3N+12) 2^(−w)` of `π_N`, and the raw bracket is
`[⌊q − E⌋_w, ⌈q + E⌉_w]` with the exact float `E = piErr w = 2^(3N+13) 2^(−w)` (`piBracketAt`),
of width at most `2^(3N+16) 2^(−w)` (`piBracketAt_spec`).  Since the a priori slack is a true
loss of `3N + 16 ≈ 3 lg w` bits (the interval iteration it replaces was much tighter than its
proven bound, and Ziv's loop for `ln` would need a second pass at high precision), `piBracket w`
runs the iteration at the working precision `piWork w = w + 3N + 16`: its width is at most
`2^(3−w) ≤ piEps w = 2^19 w³ 2^(−w)` and the lower end is strictly below `π` (`piBracket_spec`),
so Ziv's loop needs no fuel (`Pi.lean`).  Half the work of the former interval iteration.
-/

namespace Azurite.AzFloat

/-- `max(x, 0)` for a lower bound of a nonnegative quantity (used by the interval exponential,
`Interval.lean`). -/
def clampNonneg (x : AzFloat) : AzFloat := if x.isNegative then zero else x

/-- The computed Brent–Salamin triple `(a_n, b_n, s_n)`. -/
structure PiPt where
  a : AzFloat
  b : AzFloat
  s : AzFloat

/-- One Brent–Salamin step from index `n` at working precision `w`, every operation rounded
down: `a' = ⌊a + b⌋/2`, `b' = ⌊√⌊ab⌋⌋`, `s' = ⌊s − 2^(n−1) ⌊⌊a − b⌋²⌋⌋`. -/
def piStep (w n : Nat) (p : PiPt) : PiPt :=
  let d := (subPrecRound p.a p.b w .Floor).1
  let t := (sqrPrecRound d w .Floor).1 <<< ((n : AzInt) - 1)
  { a := (addPrecRound p.a p.b w .Floor).1 >>> (1 : Nat)
    b := (sqrtPrecRound (mulPrecRound p.a p.b w .Floor).1 w .Floor).1
    s := (subPrecRound p.s t w .Floor).1 }

/-- Steps `0, …, n − 1`. -/
def piIter (w : Nat) : Nat → PiPt → PiPt
  | 0, p => p
  | n + 1, p => piStep w n (piIter w n p)

/-- `a₀ = 1`, `b₀ = ⌊1/√2⌋_w`, `s₀ = 1/2`. -/
def piInit (w : Nat) : PiPt := ⟨one, (sqrt2Over2PrecRound w .Floor).1, oneHalf⟩

/-- The a priori error `E = 2^(3N + 13 − w)`, `N = piSteps w`, of the computed `π_N` (including
the truncation error `2^(−w)` of `π_N` itself), as an exact float. -/
def piErr (w : Nat) : AzFloat :=
  powerOf2 (((3 * BZ.piSteps w + 13 : Nat) : AzInt) - (w : AzInt))

/-- The two ends of the raw bracket of `π` at working precision `w`: `π_N` computed with every
operation rounded down, widened by `piErr w` on both sides (width `≤ 2^(3N+16) 2^(−w)`). -/
def piBracketAt (w : Nat) : AzFloat × AzFloat :=
  let p := piIter w (BZ.piSteps w) (piInit w)
  let a := (addPrecRound p.a p.b w .Floor).1 >>> (1 : Nat)
  let n := (sqrPrecRound a w .Floor).1 <<< (1 : Nat)
  let q := (divPrecRound n p.s w .Floor).1
  let e := piErr w
  ((subPrecRound q e w .Floor).1, (addPrecRound q e w .Ceiling).1)

/-- The working precision of the iteration behind `piBracket w`: `3 piSteps w + 16` guard bits
absorb the a priori error, so that the bracket has width at most `2^(3−w)`. -/
def piWork (w : Nat) : Nat := w + 3 * BZ.piSteps w + 16

/-- The two ends of the bracket of `π` at working precision `w` (the raw bracket at `piWork w`,
width `≤ 2^(3−w)`). -/
def piBracket (w : Nat) : AzFloat × AzFloat := piBracketAt (piWork w)

/-- The bracket of `π` at working precision `w`, as a pair of `Roundable`s. -/
def piApprox (w : Nat) : Roundable × Roundable :=
  let b := piBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
