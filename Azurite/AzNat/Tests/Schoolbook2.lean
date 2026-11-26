/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div
import Azurite.AzNat.Pow
import Azurite.AzNat.Equiv.Basic

/-!
# Tests for the schoolbook division with two quotient limbs per pass

The compiled `/` and `%` run `schoolbookDivModLimbsFast` (`schoolbookDivModLimbs_eq_fast`);
the results are compared with `Nat` division.
-/

namespace Azurite.AzNat.Tests.Schoolbook2

open Azurite Azurite.AzNat

/-- Quotient and remainder agree with `Nat`. -/
def agrees (u v : AzNat) : Bool :=
  (u / v).toNat == u.toNat / v.toNat && (u % v).toNat == u.toNat % v.toNat

/-- `2^k`. -/
def p2 (k : Nat) : AzNat := AzNat.pow (AzNat.ofNat 2) k

-- trial digits `2^128 − 1` (the top limbs of the dividend equal those of the divisor) and
-- all-ones divisors, for 2 to 9 limbs and even and odd quotient lengths
#guard (List.range 8).all fun i =>
  let n := i + 2
  let v := p2 (64 * n) - 1
  (List.range 6).all fun m =>
    agrees (v * (p2 (64 * (m + 1)) - 1) + (v - 1)) v
      && agrees (v * (p2 (64 * (m + 1)) - 1)) v
      && agrees (p2 (64 * (n + m + 1)) - 1) v
      && agrees (p2 (64 * (n + m))) v

-- divisors `2^(64 n − 1) + small` (the trial digit overshoots most, two add-backs)
#guard (List.range 8).all fun i =>
  let n := i + 2
  (List.range 5).all fun c =>
    let v := p2 (64 * n - 1) + AzNat.ofNat (c + 1) * p2 (64 * (n - 2)) - 1
    (List.range 6).all fun m =>
      agrees (p2 (64 * (n + m + 1)) - 1) v
        && agrees (v * (p2 (64 * (m + 2)) - AzNat.ofNat 3) + (v - 1)) v
        && agrees ((p2 (64 * (n + m + 1)) - 1) - p2 (64 * (n + m))) v

-- pseudo-random operands, 2 to 40 limbs
#guard (List.range 60).all fun i =>
  let u := AzNat.pow (AzNat.ofNat 1000003) (13 * i + 9) + AzNat.ofNat (i * i)
  let v := AzNat.pow (AzNat.ofNat 999983) (5 * i + 7) + AzNat.ofNat (7 * i + 1)
  agrees u v && agrees (u * v + (v - 1)) v && agrees (u * u) (v + 1)

end Azurite.AzNat.Tests.Schoolbook2
