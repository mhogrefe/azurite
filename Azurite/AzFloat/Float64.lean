/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Precision
import Azurite.AzInt.Compare
import Azurite.AzInt.ShiftLeft
import Azurite.AzInt.ShiftRightRound

/-!
# Conversions with Lean's `Float` (IEEE binary64)

Lean's `Float` is a wrapper around its logical model `Float.Model`, a valid binary64 bit
pattern, which unpacks (`Float.Model.unpack`) into `UnpackedFloat`: `NaN`, a signed infinity, a
signed zero, or `± m · 2^e` with `0 < m`.  Both directions go through that unpacked form, so
everything but the opaque `Float` operations themselves is ordinary computable code.

* `ofFloat64 f` is exact: a finite `Float` becomes a precision-53 float of the same value (both
  signed zeros become `zero`).
* `toFloat64 x mode` rounds `x` to binary64 in `mode`: to 53 bits in the normal range
  `[2^-1022, 2^1024)`, to a multiple of `2^-1074` below it (subnormals and zero), and on overflow
  to `±∞` or to the largest finite value, following IEEE 754 (`Nearest`, `Up`, and the directed
  mode pointing away from zero give `±∞`; the others the largest finite value).  The rounding is
  done with the proven `AzInt.shiftRightRound`, and the result is packed with the model's `pack`.
-/

namespace Azurite.AzFloat

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-- A Lean `Int` as an `AzInt`. -/
def azIntOfInt : Int → AzInt
  | .ofNat n => (AzNat.ofNat n).toAzInt
  | .negSucc n => -(AzNat.ofNat (n + 1)).toAzInt

/-- The value of an `AzNat` that fits in one limb (`0` otherwise is unspecified). -/
def smallToNat (n : AzNat) : Nat := (n.limbs.getD 0 0).toNat

/-- The sign of a `Bool` sign (`true` is positive). -/
def signOfBool (s : Bool) : Sign := if s then .positive else .negative

/-- An unpacked binary64 value as a float, exactly, at precision 53 (or the mantissa's bit
length if larger). -/
def ofUnpacked : UnpackedFloat → AzFloat
  | .notANumber => nan
  | .infinity s => infinity (decide (s = .positive))
  | .zero _ => zero
  | .finite s m e _ =>
    let M := AzNat.ofNat m
    mkFinite (decide (s = .positive)) (azIntOfInt e + (AzNat.ofNat M.size).toAzInt) 53 M

/-- A `Float` as a float, exactly. -/
def ofFloat64 (f : Float) : AzFloat := ofUnpacked f.toModel.unpack

/-- Does an overflowing value of sign `s` (`true` positive) round to `±∞` in `mode`, rather than
to the largest finite value?  `Nearest` and `Up` always do; `Down` never; `Ceiling` for positive
and `Floor` for negative values. -/
def overflowToInfinity (s : Bool) : RoundingMode → Bool
  | .Nearest => true
  | .Up => true
  | .Down => false
  | .Ceiling => s
  | .Floor => !s

/-- The largest finite binary64 value, `(2^53 − 1) · 2^971`. -/
def maxFinite64 (sign : Sign) : UnpackedFloat :=
  .finite sign (2 ^ 53 - 1) 971 (by decide)

/-- Assemble the unpacked result from the rounded integer `r` (`|r| ≤ 2^53`) at exponent `t`:
a carry to `2^53` is halved, an exponent above `971` overflows. -/
def finishUnpacked (s : Bool) (r : AzInt) (t : AzInt) (mode : RoundingMode) : UnpackedFloat :=
  let sign := signOfBool s
  if r.abs = 0 then .zero sign
  else
    let carry := r.abs.size = 54
    let M := if carry then r.abs.shiftRight 1 else r.abs
    let t' := if carry then t + 1 else t
    if azIntOfInt 971 < t' then
      if overflowToInfinity s mode then .infinity sign else maxFinite64 sign
    else
      let n := smallToNat M
      if h : 0 < n then .finite sign n t'.toInt h else .zero sign

/-- `x` rounded to a binary64 value in `mode`, unpacked. -/
def toUnpacked (x : AzFloat) (mode : RoundingMode) : UnpackedFloat :=
  match x with
  | nan => .notANumber
  | infinity s => .infinity (signOfBool s)
  | zero => .zero .positive
  | finite s e p m _ =>
    -- `x = ±core · 2^(e − p)` with `2^(e−1) ≤ |x| < 2^e`; the IEEE target exponent is
    -- `t = max (e − 53) (−1074)`, and `x / 2^t = ±core · 2^k`
    let core := coreSignificand p m
    let t : AzInt := max (e - (AzNat.ofNat 53).toAzInt) (azIntOfInt (-1074))
    let k : AzInt := e - (AzNat.ofNat p).toAzInt - t
    let r : AzInt :=
      if k.sign then (AzInt.mkNorm s core).shiftLeft k.abs.toNat
      else (AzInt.shiftRightRound (AzInt.mkNorm s core) mode k.abs.toNat).1
    finishUnpacked s r t mode

/-- `x` rounded to a `Float` in `mode`. -/
def toFloat64 (x : AzFloat) (mode : RoundingMode := .Nearest) : Float :=
  Float.ofModel (Float.Model.pack (toUnpacked x mode))

end Azurite.AzFloat
