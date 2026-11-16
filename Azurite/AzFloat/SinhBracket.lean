/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.TanBracket

/-!
## The bracket of `sinh x`

With `u = exp a − 1` for `a = |x| > 0`,

  `sinh a = (e^a − e^(−a)) / 2 = (u + u / (1 + u)) / 2`,

a sum of positive terms, increasing in `u`: no cancellation, whatever the size of `a`.
`sinhOfExpM1 u W` evaluates it on an enclosure of `u` with outward rounding at `W` bits (one
division), and `sinhBracket a e w` applies it to `expM1Bracket a e w`, which has relative
accuracy for a small `a` (compensated working precision, or `[a, a + a 2^e]` for a tiny `a`).
`sinhApprox` is the pair of `Roundable`s for the Ziv loop of `AzFloat/Sinh.lean`, negated and
swapped for `x < 0`.

**Tiny arguments**: `|x| < sinh |x| ≤ |x| + |x|³` for `|x| ≤ 1`, the bounds of the tangent, so
the tiny-argument test is that of `tanTiny?` (exact end `|x|` at the open side).

The proofs are in `Equiv/SinhBracket.lean`.
-/

namespace Azurite.AzFloat

/-- `(u + u/(1 + u))/2` on an enclosure of `u ≥ 0`, rounded outwards at precision `W`. -/
def sinhOfExpM1 (u : Encl) (W : Nat) : Encl :=
  let ul := clampNonneg u.1
  let d1 := (addPrecRound one ul W .Ceiling).1
  let q1 := (divPrecRound ul d1 W .Floor).1
  let s1 := (addPrecRound ul q1 W .Floor).1
  let d2 := (addPrecRound one u.2 W .Floor).1
  let q2 := (divPrecRound u.2 d2 W .Ceiling).1
  let s2 := (addPrecRound u.2 q2 W .Ceiling).1
  (s1 <<< AzInt.ofInt (-1), s2 <<< AzInt.ofInt (-1))

/-- The bracket of `sinh a` at Ziv level `w` for a positive finite float `a < 2^e`. -/
def sinhBracket (a : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  sinhOfExpM1 (expM1Bracket a e w) (w + 16)

/-- The bracket of `sinh x` as a pair of `Roundable`s: that of `sinh |x|`, negated and swapped
when `neg` (`x < 0`). -/
def sinhApprox (neg : Bool) (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox neg (sinhBracket x.abs e w)

end Azurite.AzFloat
