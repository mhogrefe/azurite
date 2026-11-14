/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Interval
import Azurite.AzFloat.Rem
import Azurite.AzFloat.Ziv

/-!
## Shared tools of the brackets of `cos x` and `sin x`

`cosWork ex w = w + 12 + max(ex, 0)` (the reduction precision at Ziv level `w` for an argument
of exponent `ex`), `enclClamp0`, `enclAbs`, the double-angle step `cosDouble`
(`cos 2θ = 2 cos² θ − 1`), and the tiny-argument path `cosTiny?`.  The bracket `cosBracket` is in
`AzFloat/SinCosBracket.lean` (MCA Algorithm 4.4; until 2026-11-13 it was an interval Taylor
series of `cos (r/8)` with `O(w)` terms, defined here).
-/

namespace Azurite.AzFloat

/-- The working precision of `cos` at Ziv level `w` for an argument of exponent `ex`. -/
def cosWork (ex : AzInt) (w : Nat) : Nat := w + 12 + (if ex.sign then ex.abs.toNat else 0)

/-- The enclosure with its lower end clamped at `0` (for a value known to be nonnegative). -/
def enclClamp0 (a : Encl) : Encl := (clampNonneg a.1, a.2)

/-- The absolute value of an enclosure `[lo, hi]`: `[max(0, lo, −hi), max(hi, −lo)]`. -/
def enclAbs (a : Encl) : Encl := (clampNonneg (maxOf a.1 (-a.2)), maxOf a.2 (-a.1))

/-- The double-angle step `2[a]² − 1` for a nonnegative enclosure `a` of `cos θ`. -/
def cosDouble (W : Nat) (a : Encl) : Encl :=
  Encl.sub W (Encl.mul W (Encl.nat 2) (Encl.mul W a a)) (Encl.exact one)

/-- **The tiny-argument path of `cos`** for an argument below `2^e` in magnitude: when
`e ≤ −(p + 72)`, `−cos x` lies in `(−1, −1 + 2^(2e)]` (from `cos x ≥ 1 − x²/2`), so it is rounded
in the negated mode from the bracket `[−1, ⌈−1 + 2^(2e)⌉_{p+72}]` by the test of
`roundingPossible`, and the result is negated.  (The negation puts the exact end `1`, a rounding
boundary, at the open side of the half-open test.)  Nothing is computed from the argument, so the
cost is independent of `e`; the Ziv loop would need about `2|e|` bits.  `none` when the argument
is not tiny or the test fails. -/
def cosTiny? (e : AzInt) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let w := p + zivGuardBits
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let hi := (addPrecRound (-one) ((one <<< e) <<< e) (w + 8) .Ceiling).1
    (roundingPossible (fun P M => setPrecRound (-one) P M) (fun P M => setPrecRound hi P M) p
      (-mode)).map fun r => (-r.1, r.2.swap)
  else none

end Azurite.AzFloat
