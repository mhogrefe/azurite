/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Instances
import Azurite.AzNat.TestBit
import Azurite.AzNat.ShiftRight

/-!
# Arithmetic on `y² = x³ + ax + b` over `ℤ/n`, in Jacobian coordinates

The computable side of elliptic curve primality proving (`docs/ecpp_plan.md`, layer 2): points
are triples `(X, Y, Z)` of `AzZMod n`, with no division.

* `jacDbl a P`: doubling — `M = 3X² + aZ⁴`, `S = 4XY²`, `X₃ = M² − 2S`,
  `Y₃ = M(S − X₃) − 8Y⁴`, `Z₃ = 2YZ`.
* `jacAddMixed u v P`: `P + (u, v)` for an affine point `(u, v)`, the usual mixed addition
  with `Z₃ = Z·(uZ² − X)`.  It is **not** a complete addition: when `P = ±(u, v)` modulo a
  prime factor of `n` the result is not the sum there, and `Z₃` vanishes modulo that prime.
* `jacMul a u v fuel k`: `k · (u, v)` by halving `k`.  Every step multiplies `Z` by a
  factor that must be a unit, so one gcd of the final `Z` with `n` certifies all of them.

The specifications (equality with the functions of `Theory/Ladder.lean` through
`AzZMod.toZMod`) are in `Equiv/Curve.lean`.
-/

namespace Azurite.ECPP

open AzZMod

variable {n : AzNat} [NeZero n.toNat]

/-- A point in Jacobian coordinates over `ℤ/n`: `(X, Y, Z)` for `(X/Z², Y/Z³)`. -/
abbrev JacPoint (n : AzNat) : Type := AzZMod n × AzZMod n × AzZMod n

/-- **Doubling** on `y² = x³ + ax + b` over `ℤ/n` in Jacobian coordinates. -/
def jacDbl (a : AzZMod n) (P : JacPoint n) : JacPoint n :=
  let x2 := Square.square P.1
  let y2 := Square.square P.2.1
  let z2 := Square.square P.2.2
  let m := x2 + x2 + x2 + a * Square.square z2
  let s := P.1 * y2
  let s2 := s + s
  let s4 := s2 + s2
  let x3 := Square.square m - (s4 + s4)
  let y4 := Square.square y2
  let y42 := y4 + y4
  let y44 := y42 + y42
  (x3, m * (s4 - x3) - (y44 + y44), (P.2.1 + P.2.1) * P.2.2)

/-- **Mixed addition**: `P + (u, v)` for an affine point `(u, v)` — `H = uZ² − X`,
`r = vZ³ − Y`, `X₃ = r² − H³ − 2XH²`, `Y₃ = r(XH² − X₃) − YH³`, `Z₃ = ZH`. -/
def jacAddMixed (u v : AzZMod n) (P : JacPoint n) : JacPoint n :=
  let z2 := Square.square P.2.2
  let h := u * z2 - P.1
  let r := v * (P.2.2 * z2) - P.2.1
  let h2 := Square.square h
  let h3 := h * h2
  let w := P.1 * h2
  let x3 := Square.square r - h3 - (w + w)
  (x3, r * (w - x3) - P.2.1 * h3, P.2.2 * h)

/-- **`k · (u, v)` on `y² = x³ + ax + b` over `ℤ/n`** by halving `k`; `none` if the fuel runs
out or `k = 0` (the fuel `k.size + 1` suffices).  The `Z`-coordinate of the result is the
product of the `Z`-coordinates of all the steps. -/
def jacMul (a u v : AzZMod n) : Nat → AzNat → Option (JacPoint n)
  | 0, _ => none
  | fuel + 1, k =>
    if k = AzNat.ofNat 1 then some (u, v, 1)
    else
      (jacMul a u v fuel (k.shiftRight 1)).map fun T =>
        let d := jacDbl a T
        if k.testBit 0 then jacAddMixed u v d else d

end Azurite.ECPP
