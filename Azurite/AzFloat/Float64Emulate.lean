/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Float64
import Azurite.AzNat.ShiftRightNearestTernary

/-!
# Correctly rounded `Float` functions through `AzFloat`

Every `AzFloat` operation `fPrecRound x p mode` returns its result together with a ternary, the
comparison of the result with the exact value.  Computing at precision 53 in round-to-nearest
and converting the result to a `Float` with `toFloat64` would be correct in the normal range of
binary64, but below it the conversion rounds a second time (to a multiple of `2^-1074`), and the
double rounding can be off by one unit in the last place.  The ternary repairs this: an exact
tie seen by the second rounding was not a tie of the exact value unless the ternary is `.eq`,
and the ternary says on which side the exact value lies.

* `toUnpackedTernary x o` is `toUnpacked x .Nearest` with the subnormal shift resolved by the
  ternary `o` (`AzInt.shiftRightNearestTernary`).
* `emulateFinish (x, o)` packs that into a `Float`; `emulate`, `emulate₂`, `emulate₃`,
  `emulateRat` and `emulateList` wrap a 53-bit round-to-nearest computation of an `AzFloat`
  function between `ofFloat64` and `emulateFinish`.
* Each emulated function lives next to the `AzFloat` operation it wraps (`sumFloat64` in
  `AzFloat/Sum`, say); this file holds only the shared machinery.

A result that is exactly zero becomes `+0.0`: `AzFloat` has a single zero, so the IEEE sign of
an exact zero result (`−0.0` for `(−0.0) + (−0.0)`, say) is not reproduced.  Everything else,
including subnormal results, overflow to `±∞`, and `NaN`, follows IEEE 754 round-to-nearest
ties-to-even, as the specification `roundBinary64` in `Equiv/Float64Emulate` states.
-/

namespace Azurite.AzFloat

open Float.Model (UnpackedFloat)

/-- `x` rounded to a binary64 value (nearest, ties to even) and unpacked, where `x` is itself
the 53-bit nearest rounding of an exact value and `o` compares `x` with that value.  In the
normal range `x` is already representable; below it the shift to a multiple of `2^-1074` is
resolved by `o`, so the result is the binary64 rounding of the exact value. -/
def toUnpackedTernary (x : AzFloat) (o : Ordering) : UnpackedFloat :=
  match x with
  | nan => .notANumber
  | infinity s => .infinity (signOfBool s)
  | zero => .zero .positive
  | finite s e p m _ =>
    let core := coreSignificand p m
    let t : AzInt := max (e - (AzNat.ofNat 53).toAzInt) (azIntOfInt (-1074))
    let k : AzInt := e - (AzNat.ofNat p).toAzInt - t
    let r : AzInt :=
      if k.sign then (AzInt.mkNorm s core).shiftLeft k.abs.toNat
      else AzInt.shiftRightNearestTernary (AzInt.mkNorm s core) o k.abs.toNat
    finishUnpacked s r t .Nearest

/-- The `Float` of a 53-bit round-to-nearest result with its ternary. -/
def emulateFinish (r : AzFloat × Ordering) : Float :=
  Float.ofModel (Float.Model.pack (toUnpackedTernary r.1 r.2))

/-- A correctly rounded `Float` function from an `AzFloat` operation on one argument. -/
def emulate (f : AzFloat → Nat → RoundingMode → AzFloat × Ordering) (x : Float) : Float :=
  emulateFinish (f (ofFloat64 x) 53 .Nearest)

/-- A correctly rounded `Float` function from an `AzFloat` operation on two arguments. -/
def emulate₂ (f : AzFloat → AzFloat → Nat → RoundingMode → AzFloat × Ordering)
    (x y : Float) : Float :=
  emulateFinish (f (ofFloat64 x) (ofFloat64 y) 53 .Nearest)

/-- A correctly rounded `Float` function from an `AzFloat` operation on three arguments. -/
def emulate₃
    (f : AzFloat → AzFloat → AzFloat → Nat → RoundingMode → AzFloat × Ordering)
    (x y z : Float) : Float :=
  emulateFinish (f (ofFloat64 x) (ofFloat64 y) (ofFloat64 z) 53 .Nearest)

/-- A correctly rounded `Float` from an `AzFloat` operation on a rational argument. -/
def emulateRat (f : AzRat → Nat → RoundingMode → AzFloat × Ordering) (q : AzRat) : Float :=
  emulateFinish (f q 53 .Nearest)

/-- A correctly rounded `Float` function from an `AzFloat` operation on a list. -/
def emulateList (f : List AzFloat → Nat → RoundingMode → AzFloat × Ordering)
    (xs : List Float) : Float :=
  emulateFinish (f (xs.map ofFloat64) 53 .Nearest)

end Azurite.AzFloat
