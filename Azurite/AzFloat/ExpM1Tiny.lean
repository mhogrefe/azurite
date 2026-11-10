/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ExpApprox

/-!
## The tiny-exponent path of `b^x − 1`

For `v = x · λ` (`λ = ln b > 0` given by a bracket `L`, `x` by floats `xlo ≤ x ≤ xhi` of its
sign) with `|v| < 2^E`, `E ≤ −(p + 72)`: `v < exp v − 1 ≤ v + v²`, so `exp v − 1` lies in
`(⌊xλ⌋, ⌈⌈xλ⌉ + 2^(2E)⌉]` with the products rounded outward at `p + 72` bits, and one test of
`roundingPossible` decides the rounding.  The relative width is about `2^(−p−72)`, at a working
precision independent of `E`; the brackets of `2^x − 1`, `u^x − 1` compute `x ln b` to an
absolute accuracy and need `|E|` more bits (`2^x − 1`) or start their Ziv loop above `|E|` bits
(`u^x − 1`).  `none` when `E` is not small enough or the test fails.
-/

namespace Azurite.AzFloat

/-- The test for `exp v − 1 ∈ (lo, ⌈h₀ + 2^(2E)⌉]`, given floats `lo ≤ v ≤ h₀`, `|v| < 2^E`. -/
def expM1TinyCore (lo h₀ : AzFloat) (E : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let hi := (addPrecRound h₀ ((one <<< E) <<< E) (p + zivGuardBits + 8) .Ceiling).1
  roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p mode

/-- The rounding of `exp (x λ) − 1` for a tiny `x λ` (see the module documentation):
`pos` is the sign of `x`, `[xlo, xhi] ∋ x`, `L` brackets `λ > 0`, `|x λ| < 2^E`. -/
def expM1Tiny? (pos : Bool) (xlo xhi : AzFloat) (L : AzFloat × AzFloat) (E : AzInt) (p : Nat)
    (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let w := p + zivGuardBits + 8
  if E.sign = false ∧ w ≤ E.abs.toNat then
    if pos then
      expM1TinyCore (mulPrecRound xlo L.1 w .Floor).1 (mulPrecRound xhi L.2 w .Ceiling).1 E p mode
    else
      expM1TinyCore (mulPrecRound xlo L.2 w .Floor).1 (mulPrecRound xhi L.1 w .Ceiling).1 E p mode
  else none

/-- `expM1Tiny?` for a rational `x = q`: the floats `⌊q⌋`, `⌈q⌉` at `p + 72` bits. -/
def expM1TinyRat? (q : AzRat) (L : AzFloat × AzFloat) (E : AzInt) (p : Nat)
    (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  if q.num = 0 then none
  else
    expM1Tiny? q.sign (ofAzRatRound q (p + zivGuardBits + 8) .Floor).1
      (ofAzRatRound q (p + zivGuardBits + 8) .Ceiling).1 L E p mode

end Azurite.AzFloat
