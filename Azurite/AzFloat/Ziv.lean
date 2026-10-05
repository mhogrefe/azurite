/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Add
import Azurite.AzFloat.Precision

/-!
# Ziv's strategy

Correct rounding of a value that is not computed exactly, after Brent and Zimmermann, *Modern
Computer Arithmetic*, §3.1.10 (Ziv's strategy) and Algorithm 3.1 (`RoundingPossible`).  An
operation whose exact result `v` is expensive or impossible to materialize is replaced by a
sequence of cheap approximations: at a working precision `w` it brackets `v` between two exact
values `l ≤ v ≤ h`, with `h = l` whenever the approximation happens to be exact.  The ends are
not materialized either (for `x + q` they are `x + l'` and `x + h'` with `l'`, `h'` the `w`-bit
truncation of `q` and its successor, dyadic numbers as long as the exponent gap); they are given
by their *rounding procedures*, `Roundable`: a function returning the correct rounding of the
end at any precision and in any mode, which the exact operations of the library provide
cheaply in every regime.

Rounding to `p` bits is possible when the half-open interval `(l, h]` contains no *boundary* of
the rounding — no float of precision `p` and no midpoint between two of them, i.e. no float of
precision `p + 1` — because `roundVal` is constant between consecutive boundaries (the cell
lemma `roundVal_congr_cell`).  `roundingPossible` tests this by comparing the `(p + 1)`-bit
truncations of the two ends; the result is then the rounding of `h`.  Otherwise the working
precision is doubled (`zivLoop`).

The loop carries fuel, and `Equiv/Ziv.lean` shows that with the fuel each operation computes
from its inputs the loop never runs out: a sufficient working precision exists because the
exact value, when it is not a boundary itself, is at a positive computable distance from every
boundary, while the bracket shrinks geometrically.  No exact fallback is needed.

* `Roundable`: an exact real given by its rounding procedure.
* `truncError r`: the error of a truncation `r` (result and comparison tag), one ulp of the
  result, `0` for an exact truncation; the successor of the truncation is its sum with this.
* `roundingPossible l h p mode`: `some` of the rounding when it is determined, `none` otherwise.
* `zivLoop approx p mode fuel w`: Ziv's loop, doubling `w`, `fuel + 1` attempts.
* `zivGuardBits`, `zivFuel`: the starting guard bits and the fuel reaching a given precision.
-/

namespace Azurite.AzFloat

/-- An exact real number given by its rounding procedure: the correct rounding at any precision
in any mode, with the comparison tag. -/
abbrev Roundable := Nat → RoundingMode → AzFloat × Ordering

/-- The error of a truncation (a rounding toward `−∞`) with result `r.1` and comparison tag
`r.2`: one ulp of the result, `0` when the truncation was exact or the result is `0`.  The
truncation plus its error is the next float up, so the two bracket the truncated value. -/
def truncError (r : AzFloat × Ordering) : AzFloat :=
  if r.2 = .eq then zero else (ulp? r.1).getD zero

/-- MCA Algorithm 3.1: when the exact value lies in `(l, h]` (or is `l = h`), its rounding to
precision `p` is determined as soon as no boundary — no float of precision `p + 1` — lies in
that interval, which holds exactly when the two ends have the same `(p + 1)`-bit truncation;
the rounding is then that of `h`. -/
def roundingPossible (l h : Roundable) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if (l (p + 1) .Floor).1 = (h (p + 1) .Floor).1 then some (h p mode) else none

/-- Ziv's loop: `approx w` brackets the exact value at working precision `w`; the working
precision doubles until rounding is possible, for `fuel + 1` attempts.  The `NaN` after the
last attempt is never reached with the fuel the operations compute (`zivLoop_eq`). -/
def zivLoop (approx : Nat → Roundable × Roundable) (p : Nat) (mode : RoundingMode)
    (fuel w : Nat) : AzFloat × Ordering :=
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
working precision of at least `W` bits: the bit length of `W` doublings. -/
def zivFuel (W : Nat) : Nat := (AzNat.ofNat W).size

end Azurite.AzFloat
