/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanRatBracket
import Azurite.AzFloat.Compare

/-!
## The bracket of `atan2 (y, x)`

For finite nonzero floats `y`, `x`, the angle of the point `(x, y)` is `± φ` with the sign of `y`
and `φ = atan2 (|y|, x) ∈ (0, π)`.  With `A = arctan r`, `r = min (|y|, |x|) / max (|y|, |x|)`
in `(0, 1]`:

| | `|y| ≤ |x|` | `|y| > |x|` |
|---|---|---|
| `x > 0` | `φ = A` | `φ = π/2 − A` |
| `x < 0` | `φ = π − A` | `φ = π/2 + A` |

so the levels of `AzFloat/AtanBracket.lean` always run on an argument in `(0, 1]`.

* `atanQuot n d K`: `arctan (n/d)` for floats `0 < n ≤ d`, the quotient enclosed by two
  divisions and `atanWiden` at level `K`.
* `atanQuotRel n d e w`: the same with relative accuracy for `n/d < 2^e` — the level
  `atanWork e w`, or, for a tiny quotient (`2e ≤ −(w + 8)`), `[q − q 2^(2e), q']` with the two
  rounded quotients, at a cost independent of `e`.  Only `φ = A` needs it.
* `piShiftEncl half plus A V`: `π ± A` or `π/2 ± A` with `π` from `piBracket V`.
* `atan2Bracket y x ey ex xpos w` encloses `φ` with width at most `2^(−w)`; `atan2Approx` is the
  pair of `Roundable`s for the Ziv loop of `AzFloat/Atan2.lean` (negated and swapped for
  `y < 0`), an instance of `enclApprox`.

The proofs are in `Equiv/Atan2Bracket.lean`.
-/

namespace Azurite.AzFloat

/-- The pair of `Roundable`s of the ends of an enclosure, negated and swapped when `neg`. -/
def enclApprox (neg : Bool) (b : Encl) : Roundable × Roundable :=
  if neg then (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)
  else (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- `π ± A` (`half = false`) or `π/2 ± A` (`half = true`) for a nonnegative enclosure `A`, the
sign `+` when `plus`, at precision `V`. -/
def piShiftEncl (half plus : Bool) (A : Encl) (V : Nat) : Encl :=
  let P := piBracket V
  let pl := if half then P.1 <<< AzInt.ofInt (-1) else P.1
  let ph := if half then P.2 <<< AzInt.ofInt (-1) else P.2
  if plus then ((addPrecRound pl A.1 V .Floor).1, (addPrecRound ph A.2 V .Ceiling).1)
  else ((subPrecRound pl A.2 V .Floor).1, (subPrecRound ph A.1 V .Ceiling).1)

/-- An enclosure of `arctan (n/d)` for floats `0 < n ≤ d`, of width at most
`(3/4) 2^(−K) + 14·2^(−K−64)`. -/
def atanQuot (n d : AzFloat) (K : Nat) : Encl :=
  let V := K + 64
  atanWiden (divPrecRound n d V .Floor).1 (divPrecRound n d V .Ceiling).1 K V

/-- An enclosure of `arctan (n/d)` for floats `0 < n ≤ d` with `n/d < 2^e`, with relative
accuracy `2^(−w)`. -/
def atanQuotRel (n d : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  if e.sign = false ∧ w + 8 ≤ 2 * e.abs.toNat then
    let V := w + 64
    let l := (divPrecRound n d V .Floor).1
    let h := (divPrecRound n d V .Ceiling).1
    (clampNonneg (subPrecRound l ((l <<< e) <<< e) V .Floor).1, h)
  else atanQuot n d (atanWork e w)

/-- The bracket of `atan2 (|y|, x)` at Ziv level `w` for finite nonzero `y`, `x` of exponents
`ey`, `ex`; `xpos`: `x > 0`. -/
def atan2Bracket (y x : AzFloat) (ey ex : AzInt) (xpos : Bool) (w : Nat) : Encl :=
  let ya := y.abs
  let xa := x.abs
  if le ya xa = true then
    if xpos then atanQuotRel ya xa (ey - ex + AzInt.ofInt 1) w
    else piShiftEncl false false (atanQuot ya xa (w + 8)) (w + 72)
  else piShiftEncl true (!xpos) (atanQuot xa ya (w + 8)) (w + 72)

/-- The bracket of `atan2 (y, x)` as a pair of `Roundable`s (`neg`: `y < 0`). -/
def atan2Approx (neg : Bool) (y x : AzFloat) (ey ex : AzInt) (xpos : Bool) (w : Nat) :
    Roundable × Roundable :=
  enclApprox neg (atan2Bracket y x ey ex xpos w)

/-- The bracket of `3π/4 = π/2 + π/4` as a pair of `Roundable`s. -/
def piThreeQuartersApprox (w : Nat) : Roundable × Roundable :=
  let P := piBracket (w + 64)
  enclApprox false
    (piShiftEncl true true (P.1 <<< AzInt.ofInt (-2), P.2 <<< AzInt.ofInt (-2)) (w + 64))

end Azurite.AzFloat
