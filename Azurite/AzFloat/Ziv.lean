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
sequence of cheap approximations: at a working precision `w` it produces a float `y` and an
error bound `ε ≥ 0` with `y ≤ v ≤ y + ε`.  Rounding is possible when the two ends of this
interval round to the same float *with the same comparison tag* (`roundingPossible`): the
rounding of a dyadic endpoint is a shift, so the test costs nothing compared with the
approximation, and every value between the ends then rounds the same way
(`Rounding/Between.lean`).  Otherwise the working precision is doubled (`zivLoop`).  The loop
carries fuel; when it runs out, an exact fallback computes the result directly, so the result is
correct unconditionally and the fuel only bounds the work of the approximation phase.

The test with both ends asks for the *closed* interval to lie in one open rounding cell, which
is stricter than MCA's `RoundingPossible` at the cell boundaries; it is what the comparison tag
needs (a value exactly on a boundary rounds the same way as its neighbors on one side but gets a
different tag).

* `roundingPossible y ε p mode`: `some` of the rounding when the ends agree, `none` otherwise.
* `zivLoop approx exact p mode fuel w`: Ziv's loop, doubling `w`.
* `zivGuardBits`, `zivFuel`: the starting guard bits and the fuel.
-/

namespace Azurite.AzFloat

/-- MCA Algorithm 3.1 in the form of two cheap roundings: when `y ≤ v ≤ y + ε`, the rounding
of `v` to precision `p` is determined as soon as `y` and `y + ε` round to the same float with
the same comparison tag. -/
def roundingPossible (y ε : AzFloat) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let r := setPrecRound y p mode
  if r = addPrecRound y ε p mode then some r else none

/-- Ziv's loop: `approx w` is an approximation `(y, ε)` with `y ≤ v ≤ y + ε` computed at
working precision `w`; the working precision doubles until rounding is possible, and after
`fuel` attempts `exact ()` computes the result directly. -/
def zivLoop (approx : Nat → AzFloat × AzFloat) (exact : Unit → AzFloat × Ordering) (p : Nat)
    (mode : RoundingMode) : Nat → Nat → AzFloat × Ordering
  | 0, _ => exact ()
  | fuel + 1, w =>
    let a := approx w
    match roundingPossible a.1 a.2 p mode with
    | some r => r
    | none => zivLoop approx exact p mode fuel (2 * w)

/-- The guard bits of the first working precision, `p + zivGuardBits`: a word, so that the
first attempt fails with probability about `2^-64` on generic inputs. -/
def zivGuardBits : Nat := 64

/-- The fuel for `zivLoop` at destination precision `p` with inputs of `n` bits: enough
doublings to take the working precision far beyond `(p + n)²`, after which the exact fallback
is cheaper than another attempt. -/
def zivFuel (p n : Nat) : Nat := (p + n).log2 + 8

/-- The error of a truncation (a rounding toward `−∞`) with a given result: one ulp of the
result, `0` for a zero result (whose truncation was exact). -/
def truncError (f : AzFloat) : AzFloat := (ulp? f).getD zero

end Azurite.AzFloat
