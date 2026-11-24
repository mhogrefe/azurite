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
* `jacAddAffine a b u v P`: `P + (u, v)` for an affine point `(u, v)`, in the representative
  with `Z₃ = X − uZ²` (the one whose correctness needs no side condition on the curve
  equation; see `Theory/Ladder.lean`).  It is **not** a complete addition: when `P = ±(u, v)`
  modulo a prime factor of `n` the result is not the sum there, and `Z₃` vanishes modulo that
  prime.
* `jacMulAcc a b u v fuel k`: `k · (u, v)` by halving `k`, together with the product of the
  `Z₃` of all additions — one gcd of that product with `n` then certifies every addition.

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

/-- **Addition of the affine point `(u, v)`** to a Jacobian point on `y² = x³ + ax + b` over
`ℤ/n`; the `Z`-coordinate of the result is `X − uZ²`. -/
def jacAddAffine (a b u v : AzZMod n) (P : JacPoint n) : JacPoint n :=
  let x := P.1
  let y := P.2.1
  let z := P.2.2
  let z2 := Square.square z
  let z3 := z * z2
  let z4 := Square.square z2
  let z6 := Square.square z3
  let u2 := Square.square u
  let x2 := Square.square x
  let yvz := y * v * z
  let bz4 := b * z4
  let x' := x * (u2 * z2) - (yvz + yvz) + x2 * u + a * (u * z4 + x * z2) + (bz4 + bz4)
  -- the constants of the base point
  let v2 := Square.square v
  let c1 := v2 + v2 + a * u + (b + b) - u * u2
  let c2 := u2 + u2 + u2 + a
  let y2 := Square.square y
  let bz6 := b * z6
  let inner := (x2 + x2 + x2) * (u * z2) - x * x2 + (y2 + y2) + a * (u * z6 + x * z4)
    + (bz6 + bz6)
  let negY := y * z3 * c1 - v * inner + x * y * z * c2
  (x', -negY, x - u * z2)

/-- **`k · (u, v)` on `y² = x³ + ax + b` over `ℤ/n`** by halving `k`, with the product of
the `Z`-coordinates of all additions; `none` if the fuel runs out or `k = 0` (the fuel
`k.size + 1` suffices). -/
def jacMulAcc (a b u v : AzZMod n) : Nat → AzNat → Option (JacPoint n × AzZMod n)
  | 0, _ => none
  | fuel + 1, k =>
    if k = AzNat.ofNat 1 then some ((u, v, 1), 1)
    else
      (jacMulAcc a b u v fuel (k.shiftRight 1)).map fun s =>
        let d := jacDbl a s.1
        if k.testBit 0 then
          let r := jacAddAffine a b u v d
          (r, s.2 * r.2.2)
        else (d, s.2)

end Azurite.ECPP
