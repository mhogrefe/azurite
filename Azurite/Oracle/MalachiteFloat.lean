/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Basic
import Azurite.AzInt.Compare
import Azurite.AzFloat.Precision
import Azurite.AzNat.LowMask
import Azurite.AzNat.Pow2

/-!
# Malachite's exponent range, applied to an `AzFloat`

An `AzFloat` has an unbounded exponent, so nothing it computes overflows or underflows. A
Malachite `Float` has raw exponents in `[-(2^30 - 1), 2^30 - 1]`, and a result outside that range
becomes `±∞`, the largest finite value of the result's precision, zero, or the smallest positive
value, depending on the rounding mode. This file emulates that, from Malachite's documentation of
the rule (the "Overflow and underflow" sections of its `Float` operations), so that the oracle can
compare an Azurite result with a Malachite one:

* a result with exponent above `2^30 - 1` is `±∞` under `Nearest`, `Up`, and the directed mode
  pointing away from zero (`Ceiling` for positive, `Floor` for negative), and otherwise the largest
  finite value `(1 - 2^-p) · 2^(2^30 - 1)` with the result's sign;
* a result with exponent below `-(2^30 - 1)` is zero under `Down` and the directed mode pointing
  toward zero, the smallest positive value `2^(-2^30)` under `Up` and the mode pointing away, and
  under `Nearest` zero when the exact result is at most half of that smallest value and the
  smallest value otherwise. The exact result is not available, only its rounding `r` and the
  `Ordering` of `r` against it, but that is enough: the exact value is at most half the smallest
  value when `r` is below it, or equal to it with `r` not below the exact value (the tie goes to
  zero).

The `Ordering` returned is the one Malachite documents for an overflow or underflow: `∞` and the
smallest positive value are above the exact result, the largest finite value and zero below it.
Zero has no sign in Azurite, so an underflow to zero loses Malachite's `-0.0`; the oracle compares
zeros regardless of sign.
-/

namespace Azurite.Oracle

open Azurite

/-- Malachite's `Float::MAX_EXPONENT`, `2^30 - 1`, the largest raw exponent. -/
def maxExponent : AzInt := (AzNat.ofNat (2 ^ 30 - 1)).toAzInt

/-- Malachite's `Float::MIN_EXPONENT`, `-(2^30 - 1)`, the smallest raw exponent. -/
def minExponent : AzInt := -maxExponent

/-- Malachite's largest finite `Float` of precision `p`, `(1 - 2^-p) · 2^(2^30 - 1)`, with sign
`s`; `Float::max_finite_value_with_prec` when `s` is `true`. -/
def maxFinite (s : Bool) (p : Nat) : AzFloat := AzFloat.mkFinite s maxExponent p (AzNat.lowMask p)

/-- Malachite's smallest positive `Float` of precision `p`, `2^(-2^30)`, with sign `s`;
`Float::min_positive_value_prec` when `s` is `true`. -/
def minPositive (s : Bool) (p : Nat) : AzFloat := AzFloat.mkFinite s minExponent p 1

/-- Does an overflowing result of sign `s` round to `±∞` in `mode`, rather than to the largest
finite value? -/
def overflowsToInfinity (s : Bool) : RoundingMode → Bool
  | .Nearest | .Up => true
  | .Down => false
  | .Ceiling => s
  | .Floor => !s

/-- Does an underflowing result of sign `s` round to zero in `mode`, rather than to the smallest
positive value? Under `Nearest` this needs the rounded result `r` (its exponent `e`, precision `p`,
and significand `m`) and the `Ordering` `o` of `r` against the exact value. -/
def underflowsToZero (s : Bool) (e : AzInt) (p : Nat) (m : AzNat) (o : Ordering) :
    RoundingMode → Bool
  | .Down => true
  | .Up => false
  | .Floor => s
  | .Ceiling => !s
  | .Nearest =>
    -- below half the smallest positive value, or equal to it with the exact value not beyond it
    e < minExponent - 1 ||
      ((AzFloat.coreSignificand p m).isPowerOfTwo && (if s then o != .lt else o != .gt))

/-- Malachite's exponent range applied to a result `r` that Azurite rounded with an unbounded
exponent in `mode`, where `o` compares `r` with the exact value: the Malachite result and its
`Ordering` against the exact value. -/
def clamp (r : AzFloat) (o : Ordering) (mode : RoundingMode) : AzFloat × Ordering :=
  match r with
  | .finite s e p m _ =>
    if maxExponent < e then
      if overflowsToInfinity s mode then (.infinity s, if s then .gt else .lt)
      else (maxFinite s p, if s then .lt else .gt)
    else if e < minExponent then
      if underflowsToZero s e p m o mode then (.zero, if s then .lt else .gt)
      else (minPositive s p, if s then .gt else .lt)
    else (r, o)
  | _ => (r, o)

/-- `clamp` for an operation whose exact result Azurite computed exactly (an `Ordering` of
`Equal`). -/
def clampExact (r : AzFloat) (mode : RoundingMode) : AzFloat := (clamp r .eq mode).1

end Azurite.Oracle
