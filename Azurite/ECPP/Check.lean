/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.CurveMont
import Azurite.AzNat.IsPrimeAprcl
import Azurite.AzNat.Gcd
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Size
import Azurite.AzNat.Sub

/-!
# Elliptic curve primality proving: the certificate and its checker

A certificate for `n` is a list of steps (`StepCert`): a curve `y² = x³ + ax + b` over
`ℤ/n`, a point `(u, v)` on it, and a number `q` — the claim being that `(u, v)` has order `q`
modulo every prime factor of `n`, which for `q` prime and `q > (n^(1/4) + 1)²` forces `n`
prime (Goldwasser–Kilian).  The next step is a certificate for `q`; after the last step the
remaining number is settled by `AzNat.isPrimeAprcl`.

`checkStep n c` tests, with `s = ⌊√n⌋`:

* `n > 1`, `gcd(n, 6) = 1`; `s + 1 < q` and `4s < (q − s − 1)²`;
* `gcd(4a³ + 27b², n) = 1` and `v² = u³ + au + b`;
* `V = (q − 1) · (u, v)` by `jacMul`: `gcd(Z_V, n) = 1` (which certifies every step of the
  multiplication), and `V = −(u, v)`, i.e. `X_V = u Z_V²`, `Y_V = −v Z_V³`.

`check n cert` runs the chain.  Soundness: `Equiv/Check.lean`
(`check n cert = true → Nat.Prime n.toNat`).

The certificate carries the point of order `q` itself; the order `m` of the curve and the
cofactor `m/q` are the business of the generator.
-/

namespace Azurite.ECPP

open AzZMod

/-- **One step of a certificate** for a number `n`: the coefficients `a`, `b` of a curve over
`ℤ/n`, a point `(u, v)` on it, and the next number `q` (all as residues or naturals; the
first four are reduced modulo `n`). -/
structure StepCert where
  a : AzNat
  b : AzNat
  u : AzNat
  v : AzNat
  q : AzNat

/-- **The check of one step** of a certificate for `n`. -/
def checkStep (n : AzNat) (c : StepCert) : Bool :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    let one := AzNat.ofNat 1
    let s := AzNat.sqrt n
    let t := c.q - s - one
    let a := ofAzNat n c.a
    let b := ofAzNat n c.b
    let u := ofAzNat n c.u
    let v := ofAzNat n c.v
    let a3 := a * Square.square a
    let a3x2 := a3 + a3
    let b2 := Square.square b
    let b2x3 := b2 + b2 + b2
    let b2x9 := b2x3 + b2x3 + b2x3
    let disc := (a3x2 + a3x2) + (b2x9 + b2x9 + b2x9)
    decide (AzNat.gcd n (AzNat.ofNat 6) = one) && decide (s + one < c.q)
      && decide (AzNat.ofNat 4 * s < t * t)
      && decide (AzNat.gcd disc.val n = one)
      && decide (Square.square v = u * Square.square u + a * u + b)
      && match jacMul a u v (c.q.size + 1) (c.q - one) with
        | none => false
        | some V =>
          decide (AzNat.gcd V.2.2.val n = one)
            && decide (V.1 = u * Square.square V.2.2)
            && decide (V.2.1 = -(v * (V.2.2 * Square.square V.2.2)))
  else false

/-- **The checker of a certificate**: the steps in a chain, and `AzNat.isPrimeAprcl` on the number
that remains. -/
def check : AzNat → List StepCert → Bool
  | n, [] => n.isPrimeAprcl
  | n, c :: cs => checkStep n c && check c.q cs

end Azurite.ECPP
