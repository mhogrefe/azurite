/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Precision
import Azurite.AzInt.Compare
import Azurite.AzInt.ShiftRightRound
import Azurite.AzNat.IsMultipleOfPow2

/-!
# Rounding to an integer

`roundToIntegerPrecRound x p mode` rounds `x` to an integer representable at precision `p`, in
the direction given by `mode`, with a single rounding: if the integer part of `x` needs more
than `p` bits, no intermediate integer is formed (`10.5` to nearest at `2` bits is `12`, the
nearer of the two-bit integers `8` and `12`, not `10` rounded again).  `Floor` and `Ceiling` are
the floor and ceiling, `Down` truncates, `Up` rounds away from zero, and `Nearest` rounds to the
nearest with ties to even.  The result comes with an `Ordering` comparing it with `x` and a
`Bool` saying whether `x` was an integer: `(.eq, true)` is an integer representable at `p`
bits, returned unchanged; `(.lt, true)`/`(.gt, true)` an integer that had to be rounded to fit;
`(.lt, false)`/`(.gt, false)` a non-integer; `(.eq, false)` cannot occur.  `NaN`, the infinities
and zero are returned unchanged with `.eq`; of these only zero is an integer.

The specification is the rounding target `intPrecisionSet p` of `Rounding/IntPrecision`
(`Equiv/RoundToInteger.lean`).  The implementation: when the exponent is at least `p` (or the
float is already an integer), the `p`-bit rounding `setPrecRound` is the answer, since every
`p`-bit value near `x` is then an integer; otherwise `|x| < 2^(p−1)`, every integer near `x` is
representable, and the integer rounding is the rounded shift `AzInt.shiftRightRound`.

`roundToIntegerThenPrecRound x irm p rm` is the composition of two roundings instead (MPFR's
`mpfr_rint_`-prefixed functions): the exact integer rounding of `x` in `irm` first, then that
integer correctly rounded to precision `p` in `rm`, with the comparison against the exact
integer.  With both modes `Nearest`, `10.5` becomes `10` and then `8` at 2 bits, where the
single rounding gives `12`.  The first step is `roundToIntegerPrecRound` at the float's own
precision, which is always exact (`toVal_roundToIntegerPrecRound_self`); the specials pass
through the final rounding only.
-/

namespace Azurite.AzFloat

/-- Is the float an integer?  Zero is; `NaN` and the infinities are not. -/
def isInteger : AzFloat → Bool
  | zero => true
  | finite _ e q m _ =>
    (AzNat.ofNat q).toAzInt ≤ e ||
      (coreSignificand q m).isMultipleOfPow2 ((AzNat.ofNat q).toAzInt - e).abs.toNat
  | _ => false

/-- `x` rounded in `mode` to an integer representable at precision `p`, with the comparison
against `x` and whether `x` was an integer. -/
def roundToIntegerPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering × Bool :=
  match x with
  | nan => (nan, .eq, false)
  | infinity s => (infinity s, .eq, false)
  | zero => (zero, .eq, true)
  | finite s e q m hv =>
    if (AzNat.ofNat p).toAzInt ≤ e || (AzNat.ofNat q).toAzInt ≤ e then
      -- the integer part needs at least `p` bits, or `x` is already an integer
      let r := setPrecRound (finite s e q m hv) p mode
      (r.1, r.2, isInteger (finite s e q m hv))
    else
      -- `|x| < 2^(p−1)`: the integer rounding of `x` is representable
      let r := AzInt.shiftRightRound (AzInt.mkNorm s (coreSignificand q m)) mode
        ((AzNat.ofNat q).toAzInt - e).abs.toNat
      ((setPrecRound (ofAzInt r.1) p mode).1, r.2, decide (r.2 = .eq))

/-- `x` rounded to nearest (ties to even) to an integer representable at precision `p`. -/
def roundToIntegerPrec (x : AzFloat) (p : Nat) : AzFloat :=
  (roundToIntegerPrecRound x p .Nearest).1

/-- `x` rounded in `mode` to an integer at its own precision. -/
def roundToIntegerRound (x : AzFloat) (mode : RoundingMode) : AzFloat :=
  (roundToIntegerPrecRound x (x.precision?.getD 1) mode).1

/-- `x` rounded to the nearest integer (ties to even) at its own precision. -/
def roundToInteger (x : AzFloat) : AzFloat := roundToIntegerRound x .Nearest

/-- `x` rounded to an integer in `irm` (exactly), then that integer rounded to precision `p` in
`rm`, with the comparison of the result against the exact integer. -/
def roundToIntegerThenPrecRound (x : AzFloat) (irm : RoundingMode) (p : Nat)
    (rm : RoundingMode) : AzFloat × Ordering :=
  setPrecRound (roundToIntegerPrecRound x (x.precision?.getD 1) irm).1 p rm

/-- `x` rounded to an integer in `irm`, then to nearest at precision `p`. -/
def roundToIntegerThenPrec (x : AzFloat) (irm : RoundingMode) (p : Nat) : AzFloat :=
  (roundToIntegerThenPrecRound x irm p .Nearest).1

end Azurite.AzFloat
