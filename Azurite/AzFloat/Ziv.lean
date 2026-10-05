/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Add
import Azurite.AzFloat.Compare
import Azurite.AzFloat.Precision

/-!
# Ziv's strategy

Correct rounding of a value that is not computed exactly, after Brent and Zimmermann, *Modern
Computer Arithmetic*, §3.1.10 (Ziv's strategy) and Algorithm 3.1 (`RoundingPossible`).  An
operation whose exact result `v` is expensive or impossible to materialize is replaced by a
sequence of cheap approximations: at a working precision `w` it produces a float `y` and an
error bound `ε ≥ 0` with `y ≤ v ≤ y + ε`, where moreover `ε = 0` whenever `y = v` — the
approximations are truncations, which know whether they were exact (`truncError`), so the exact
value lies in the half-open interval `(y, y + ε]` unless it is `y` itself.

Rounding to `p` bits is possible when that interval contains no *boundary* of the rounding —
no float of precision `p` and no midpoint between two of them, i.e. no float of precision
`p + 1` — because `roundVal` is constant between consecutive boundaries (the cell lemma
`roundVal_congr_cell`).  `roundingPossible` tests this with one truncation: the greatest
boundary at or below `y + ε` (the `(p + 1)`-bit floor of `y + ε`) must be at or below `y`.
Both the test and the result `round_p (y + ε)` are additions of two floats, so they cost
nothing compared with the approximation.  Otherwise the working precision is doubled
(`zivLoop`).

The loop carries fuel, and `Equiv/Ziv.lean` shows that with the fuel each operation computes
from its inputs the loop never runs out: a sufficient working precision exists because the
exact value, when it is not a boundary itself, is at a positive computable distance from every
boundary, while the error bound shrinks geometrically.  No exact fallback is needed.

* `truncError r`: the error of a truncation `r` (result and comparison tag), one ulp of the
  result, `0` for an exact truncation.
* `roundingPossible y ε p mode`: `some` of the rounding when it is determined, `none` otherwise.
* `zivLoop approx p mode fuel w`: Ziv's loop, doubling `w`, `fuel + 1` attempts.
* `zivGuardBits`, `zivFuel`: the starting guard bits and the fuel reaching a given precision.
-/

namespace Azurite.AzFloat

/-- The error of a truncation (a rounding toward `−∞`) with result `r.1` and comparison tag
`r.2`: one ulp of the result, `0` when the truncation was exact or the result is `0`. -/
def truncError (r : AzFloat × Ordering) : AzFloat :=
  if r.2 = .eq then zero else (ulp? r.1).getD zero

/-- MCA Algorithm 3.1: when the exact value lies in `(y, y + ε]` (or is `y` with `ε = 0`), its
rounding to precision `p` is determined as soon as no boundary — no float of precision `p + 1`
— lies in that interval, which is tested by truncating `y + ε` to `p + 1` bits; the rounding is
then that of `y + ε`. -/
def roundingPossible (y ε : AzFloat) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if ((addPrecRound y ε (p + 1) .Floor).1).le y then some (addPrecRound y ε p mode) else none

/-- Ziv's loop: `approx w` is an approximation `(y, ε)` computed at working precision `w`; the
working precision doubles until rounding is possible, for `fuel + 1` attempts.  The `NaN` after
the last attempt is never reached with the fuel the operations compute (`zivLoop_eq`). -/
def zivLoop (approx : Nat → AzFloat × AzFloat) (p : Nat) (mode : RoundingMode) (fuel w : Nat) :
    AzFloat × Ordering :=
  match roundingPossible (approx w).1 (approx w).2 p mode with
  | some r => r
  | none =>
    match fuel with
    | 0 => (nan, .eq)
    | fuel + 1 => zivLoop approx p mode fuel (2 * w)

/-- The guard bits of the first working precision, `p + zivGuardBits`: a word, so that the
first attempt fails with probability about `2^-64` on generic inputs. -/
def zivGuardBits : Nat := 64

/-- The fuel with which `zivLoop`, started at any positive working precision, reaches a
working precision of at least `W` bits: `⌊log₂ W⌋ + 1` doublings. -/
def zivFuel (W : Nat) : Nat := W.log2 + 1

end Azurite.AzFloat
