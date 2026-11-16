/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.Sqrt

/-!
## The bracket of `arccos x`

For `0 < a < 1` the half-angle identity

  `arccos a = 2 arctan t`,  `t = √((1 − a)/(1 + a))`,

gives an arctangent argument `t ∈ (0, 1)`; and `arccos (−a) = π − arccos a`.

* `diffQuot x y P` encloses `(x − y)/(x + y)` and `diffQuotSqrt x y P` its square root for
  floats `0 < y < x` (shared with the arcsecant); `acosQuot a P`, `acosArg a P` are the
  instances `x = 1`, `y = a`, by directed
  roundings at `P` bits of the correctly rounded `1 − a` and `1 + a`, their quotient and its
  square root.  All errors are relative, so `t` keeps its relative accuracy for `a` next to
  `1`, where `arccos a ≈ √(2 (1 − a))` is small.  The width is at most `40·2^(−P)`.
* `acosWork a w` is the level of the arctangent for `x > 0`: `w + 8` plus half the number of
  leading zero bits of `1 − a` (read off a 64-bit rounding), i.e. relative accuracy for the
  small result next to `1`.
* `acosBracket neg x w` encloses `arccos x` (`neg`: `x < 0`): the doubled `atanWiden` of
  `acosArg |x|`, subtracted from `π` (`piShiftEncl`) for `x < 0`.  Width at most `2^(−w)`.
* `acosApprox` is the pair of `Roundable`s for the Ziv loop of `AzFloat/Acos.lean`.

A tiny `x` needs nothing special: `arccos x` is next to the irrational `π/2`, and no working
precision grows with the exponent.

The proofs are in `Equiv/AcosBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `(x − y)/(x + y)` for floats `0 < y < x`, at precision `P`, with relative
accuracy: from the correctly rounded difference and sum. -/
def diffQuot (x y : AzFloat) (P : Nat) : Encl :=
  let dl := (subPrecRound x y P .Floor).1
  let dh := (subPrecRound x y P .Ceiling).1
  let el := (addPrecRound x y P .Floor).1
  let eh := (addPrecRound x y P .Ceiling).1
  ((divPrecRound dl eh P .Floor).1, (divPrecRound dh el P .Ceiling).1)

/-- An enclosure of `√((x − y)/(x + y))` for floats `0 < y < x`, at precision `P`. -/
def diffQuotSqrt (x y : AzFloat) (P : Nat) : Encl :=
  let q := diffQuot x y P
  ((sqrtPrecRound q.1 P .Floor).1, (sqrtPrecRound q.2 P .Ceiling).1)

/-- An enclosure of `(1 − a)/(1 + a)` for a float `0 < a < 1`, at precision `P`. -/
def acosQuot (a : AzFloat) (P : Nat) : Encl := diffQuot one a P

/-- An enclosure of `√((1 − a)/(1 + a))` for a float `0 < a < 1`, at precision `P`. -/
def acosArg (a : AzFloat) (P : Nat) : Encl := diffQuotSqrt one a P

/-- The level of the arctangent for `arccos a`, `0 < a < 1`, at Ziv level `w`. -/
def acosWork (a : AzFloat) (w : Nat) : Nat :=
  w + 8 + match (subPrecRound one a 64 .Ceiling).1.exponent? with
    | some e => if e.sign then 0 else e.abs.toNat / 2
    | none => 0

/-- The bracket of `arccos x` at Ziv level `w` for a finite `x` with `0 < |x| < 1`; `neg`:
`x < 0`. -/
def acosBracket (neg : Bool) (x : AzFloat) (w : Nat) : Encl :=
  let a := x.abs
  let K := if neg then w + 8 else acosWork a w
  let t := acosArg a (K + 64 + 8)
  let A := atanWiden t.1 t.2 K (K + 64)
  let A2 : Encl := (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1)
  if neg then piShiftEncl false false A2 (w + 72) else A2

/-- The bracket of `arccos x` as a pair of `Roundable`s. -/
def acosApprox (neg : Bool) (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  enclApprox false (acosBracket neg x w)

end Azurite.AzFloat
