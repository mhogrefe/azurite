/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.PiConstants

/-!
## `atan2 (y, x)`

`atan2PrecRound y x p mode` is the angle of the point `(x, y)` measured from the positive
`x`-axis, in `(−π, π]`, correctly rounded to precision `p` in `mode`, with the comparison against
the exact value; `atan2 y x` rounds to nearest at the larger of the precisions of the arguments.

There is no negative zero, so a zero argument behaves as `+0` in the IEEE 754 table:

* `NaN` in either argument gives `NaN`;
* `y = 0`: `0` for `x ≥ 0` or `x = +∞`, and `π` for `x < 0` or `x = −∞`;
* `x = 0`, `y ≠ 0`: `±π/2` with the sign of `y`;
* `y = ±∞`: `±π/2` for a finite `x`, `±π/4` for `x = +∞`, `±3π/4` for `x = −∞`;
* `y` finite and nonzero: `0` for `x = +∞`, `±π` for `x = −∞`.

The zeros are the only exact results.  For finite nonzero `y`, `x` the value is `± φ` with the
sign of `y`, `φ = atan2 (|y|, x)`, enclosed by `atan2Bracket` (`AzFloat/Atan2Bracket.lean`): the
arctangent of the smaller of `|y|`, `|x|` over the larger, shifted by `π/2` or `π` according to
the octant.  It is irrational (its tangent `y/x` is rational, and the tangent of a nonzero
rational is not), which certifies the Ziv loop (`zivLoopCertified`, no fuel).  Extreme ratios
cost nothing extra: a tiny `y/x` with `x > 0` is enclosed from `q − q³ ≤ arctan q ≤ q`.

The loop always runs on the **negative** angle `−φ` (for `y > 0` in the negated mode, the result
negated).  `roundingPossible` decides a value in `(l, h]`, and for a tiny quotient `q` that is a
float, the enclosure of `φ` is `[q − q 2^(2e), q]` with the end `q` exact: as the upper end it
would never be separated from the value, as the lower end `−q` of the enclosure of `−φ` it is
harmless.

The specification `atan2PrecRound_eq_liftVal₂` (against `Complex.arg (x + iy)`) is in
`Equiv/Atan2.lean`.
-/

namespace Azurite.AzFloat

/-- `3π/4` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def piThreeQuartersPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified piThreeQuartersApprox p mode (p + zivGuardBits)
      (piThreeQuartersApprox_isSome_exists p mode (p + zivGuardBits)
        (by unfold zivGuardBits; omega))

/-- `± c` for a positive constant `c` given by its rounding function (`pos`: the sign is
positive): the negative one rounds `c` in the negated mode. -/
def signedRound (pos : Bool) (c : Nat → RoundingMode → AzFloat × Ordering) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if pos then c p mode
  else
    let r := c p (-mode)
    (-r.1, r.2.swap)

/-- `atan2 (y, x)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `p = 0` unless the value is `0`). -/
def atan2PrecRound (y x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match y with
  | nan => (nan, .eq)
  | zero =>
    match x with
    | nan => (nan, .eq)
    | zero => (zero, .eq)
    | infinity sx => if sx then (zero, .eq) else piPrecRound p mode
    | finite sx _ _ _ _ => if sx then (zero, .eq) else piPrecRound p mode
  | infinity sy =>
    match x with
    | nan => (nan, .eq)
    | infinity sx =>
      if sx then signedRound sy piDiv4PrecRound p mode
      else signedRound sy piThreeQuartersPrecRound p mode
    | _ => signedRound sy piDiv2PrecRound p mode
  | finite sy ey qy my hvy =>
    match x with
    | nan => (nan, .eq)
    | zero => signedRound sy piDiv2PrecRound p mode
    | infinity sx => if sx then (zero, .eq) else signedRound sy piPrecRound p mode
    | finite sx ex qx mx hvx =>
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        let r := zivLoopCertified
          (atan2Approx true (finite sy ey qy my hvy) (finite sx ex qx mx hvx) ey ex sx) p
          (if sy then -mode else mode) (p + zivGuardBits)
          (atan2Approx_isSome_exists p _ true (toVal_finite sy ey qy my hvy)
            (toVal_finite sx ex qx mx hvx) (finiteVal_ne_zero sy ey hvy)
            (finiteVal_ne_zero sx ex hvx) (finiteVal_sign_iff sx ex hvx)
            (abs_finiteVal_bounds sy ey hvy).2 (abs_finiteVal_bounds sx ex hvx).1
            (p + zivGuardBits) (by unfold zivGuardBits; omega))
        if sy then (-r.1, r.2.swap) else r

/-- `atan2 (y, x)` rounded to nearest at the larger of the precisions of `y` and `x`. -/
def atan2 (y x : AzFloat) : AzFloat :=
  (atan2PrecRound y x (max (y.precision?.getD 1) (x.precision?.getD 1)) .Nearest).1

end Azurite.AzFloat
