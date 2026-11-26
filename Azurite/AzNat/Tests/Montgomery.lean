/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Montgomery
import Azurite.AzNat.Pow
import Azurite.AzNat.Equiv.Basic

/-!
# Tests for Montgomery reduction on `AzNat`
-/

namespace Azurite.AzNat.Tests.Montgomery

open Azurite Azurite.AzNat

/-- Product, square and `one` through Montgomery form against `%`, for the modulus `m` with
`extra` additional limbs. -/
def agrees (m a b : AzNat) (extra : Nat) : Bool :=
  let c := MontCtx.make m extra
  let x := c.toMont (a % m)
  let y := c.toMont (b % m)
  c.fromMont (c.mul x y) == (a * b) % m && c.fromMont (c.sqr x) == (a * a) % m
    && c.fromMont c.one == 1 % m && c.fromMont (c.toMont (a % m)) == a % m

#guard montNegInv 1 == 0 - 1
#guard 12345678901234567891 * montNegInv 12345678901234567891 + 1 == (0 : UInt64)

-- one limb, two limbs, an odd and an even number of limbs, a full top limb, `m = 1`, `m = 3`
#guard (List.range 12).all fun i =>
  let a := AzNat.pow (AzNat.ofNat 7) (40 * i + 3)
  let b := AzNat.pow (AzNat.ofNat 11) (37 * i + 1)
  [AzNat.ofNat 1, AzNat.ofNat 3, AzNat.ofNat 1000003,
    AzNat.pow (AzNat.ofNat 2) 64 - AzNat.ofNat 59, AzNat.pow (AzNat.ofNat 2) 127 - AzNat.ofNat 1,
    AzNat.pow (AzNat.ofNat 2) 192 - AzNat.ofNat 237, AzNat.pow (AzNat.ofNat 2) 255 - AzNat.ofNat 19,
    AzNat.pow (AzNat.ofNat 2) 320 - AzNat.ofNat 197, AzNat.pow (AzNat.ofNat 2) 521 - AzNat.ofNat 1,
    AzNat.pow (AzNat.ofNat 3) 500].all fun m =>
      agrees m a b 0 && agrees m a b 1 && agrees m a b 2

-- a sum of products below `2^128 m²` is reduced with two extra limbs
#guard
  let m := AzNat.pow (AzNat.ofNat 2) 192 - AzNat.ofNat 237
  let c := MontCtx.make m 2
  let a := m - AzNat.ofNat 5
  let t := AzNat.ofNat 1000 * (a * a)
  c.fromMont (c.fromMont (c.toMont (c.toMont (c.redc t % m)))) == c.redc t % m
    && c.fromMont (c.toMont (c.redc t)) == c.redc t

end Azurite.AzNat.Tests.Montgomery
