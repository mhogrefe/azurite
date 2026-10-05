/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Compare
import Azurite.AzNat.Parity
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Sub
import Azurite.AzNat.TrailingZeros
import Azurite.AzNat.ToStringBase

namespace Azurite.AzNat

/-!
## Binary GCD (Stein's algorithm) — limb-level

Implements Algorithm 1.18 (BinaryGcd) from "Modern Computer Arithmetic" (Brent
& Zimmermann), with the optimisation that each "shift out trailing zeros" step
uses hardware `ctz` per limb + a single bulk right-shift, rather than repeated
shift-by-one.
-/

/-- Right-shift a limb array by its trailing zeros count, then trim.
    The input must represent a positive number (nonempty, at least one
    nonzero limb).  The result is odd. -/
def makeOddLimbs (a : Array UInt64) : Array UInt64 :=
  trimTrailingZeros (shrLimbs a (trailingZerosLimbs a))

/-! ### Limb-level GCD loop -/

/-- Core binary GCD loop on two trimmed, odd, positive limb arrays.
    Returns the limb array of their GCD (without the common power-of-two
    factor, which the caller must shift back in).

    `fuel` bounds the number of iterations; `64 * (a.size + b.size)` is a
    safe upper bound since each step strictly reduces the bit length of
    one operand. -/
def gcdOddLimbs (a b : Array UInt64) (fuel : Nat)
    (ha : 0 < a.size) (hb : 0 < b.size) : Array UInt64 :=
  match fuel with
  | 0 => a
  | fuel' + 1 =>
    if h_eqsz : a.size = b.size then
      match compareLimbs a b 0 0 a.size (by omega) (by omega) with
      | Ordering.eq => a
      | Ordering.gt =>
        let sub := subSameLengthLimbs a b 0 0 a.size (by omega) (by omega)
        let diff := makeOddLimbs sub.1
        if hd : 0 < diff.size then gcdOddLimbs diff b fuel' hd hb
        else b
      | Ordering.lt =>
        let sub := subSameLengthLimbs b a 0 0 b.size (by omega) (by omega)
        let diff := makeOddLimbs sub.1
        if hd : 0 < diff.size then gcdOddLimbs a diff fuel' ha hd
        else a
    else if h_gt : a.size > b.size then
      let sub := subGeqLimbs a b 0 a.size 0 b.size
        (by omega) (by omega) (Nat.le_of_lt h_gt) ha hb
      let diff := makeOddLimbs (trimTrailingZeros sub.1)
      if hd : 0 < diff.size then gcdOddLimbs diff b fuel' hd hb
      else b
    else
      have h_lt : b.size > a.size := by omega
      let sub := subGeqLimbs b a 0 b.size 0 a.size
        (by omega) (by omega) (Nat.le_of_lt h_lt) hb ha
      let diff := makeOddLimbs (trimTrailingZeros sub.1)
      if hd : 0 < diff.size then gcdOddLimbs a diff fuel' ha hd
      else a

/-! ### Limb-level entry point -/

/-- Limb-level binary GCD.  Takes two limb arrays (sub-arrays of a shared
    buffer, specified by `(lo, len)` pairs) and returns the GCD as a
    fresh limb array.

    Handles the shared power-of-two factor: extracts the common trailing
    zeros, makes both operands odd, runs the GCD loop, and shifts the
    result back.  Returns an empty array if both inputs are zero-length. -/
def gcdLimbs (buf : Array UInt64) (loA lenA loB lenB : Nat)
    (_hA : loA + lenA ≤ buf.size) (_hB : loB + lenB ≤ buf.size) :
    Array UInt64 :=
  let a := trimTrailingZeros (buf.extract loA (loA + lenA))
  let b := trimTrailingZeros (buf.extract loB (loB + lenB))
  if _ha : a.size = 0 then b
  else if _hb : b.size = 0 then a
  else
    let tzA := trailingZerosLimbs a
    let tzB := trailingZerosLimbs b
    let commonTz := min tzA tzB
    let aOdd := makeOddLimbs (shrLimbs a commonTz)
    let bOdd := makeOddLimbs (shrLimbs b commonTz)
    let fuel := 64 * (a.size + b.size)
    if haO : 0 < aOdd.size then
      if hbO : 0 < bOdd.size then
        let result := gcdOddLimbs aOdd bOdd fuel haO hbO
        if commonTz = 0 then result
        else (shiftLeft (ofLimbs result) commonTz).limbs
      else a
    else b

/-! ### AzNat-level entry point -/

/-- Euclid's algorithm on single limbs with a fuel counter, so that it is structurally recursive
and evaluates under `decide` and `rfl`.  Two consecutive steps at least halve the second argument,
so `2 * 64 + 2` units of fuel always suffice for `UInt64` inputs. -/
def gcdUInt64.go : Nat → UInt64 → UInt64 → UInt64
  | 0, a, _ => a
  | fuel + 1, a, b => if b = 0 then a else gcdUInt64.go fuel b (a % b)

/-- Euclid's algorithm on single limbs, with hardware division: the base case and the fast path
for operands of at most one limb (`gcdUInt64 a 0 = a`). -/
def gcdUInt64 (a b : UInt64) : UInt64 := gcdUInt64.go 130 a b

/-- Quadratic GCD of two `AzNat`s.  Operands of at most one limb each go through Euclid's
algorithm on `UInt64` (`gcdUInt64`); otherwise the binary GCD (MCA Algorithm 1.18).  `AzNat.gcd`
dispatches here below `halfBinaryGcdThreshold` bits and uses it as the exact fallback above.

    Special cases: `gcd(0, b) = b`, `gcd(a, 0) = a`.  Otherwise extracts
    the common power-of-two factor, makes both operands odd, runs the
    limb-level binary GCD loop, and shifts the result back. -/
def gcdBinary (a b : AzNat) : AzNat :=
  if a.limbs.size ≤ 1 ∧ b.limbs.size ≤ 1 then
    (gcdUInt64 (a.limbs.getD 0 0) (b.limbs.getD 0 0)).toAzNat
  else if a.limbs.size = 0 then b
  else if b.limbs.size = 0 then a
  else
    let tzA := trailingZerosLimbs a.limbs
    let tzB := trailingZerosLimbs b.limbs
    let commonTz := min tzA tzB
    let aOdd := makeOddLimbs (shrLimbs a.limbs commonTz)
    let bOdd := makeOddLimbs (shrLimbs b.limbs commonTz)
    let fuel := 64 * (a.limbs.size + b.limbs.size)
    if haO : 0 < aOdd.size then
      if hbO : 0 < bOdd.size then
        let result := gcdOddLimbs aOdd bOdd fuel haO hbO
        ofLimbs result <<< commonTz
      else a
    else b

end Azurite.AzNat
