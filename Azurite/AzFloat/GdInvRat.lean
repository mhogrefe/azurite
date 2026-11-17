/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.GdInvBracket
import Azurite.AzFloat.LnP1

/-!
## The inverse Gudermannian of a rational

`gdInvRatPrecRound q p mode` is `gd⁻¹ q` for an `AzRat` with `|q| < π/2`, correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `gdInvRat q p` rounds to
nearest.

A certified Ziv loop (no fuel) on `gdInvRatApprox` (`AzFloat/GdInvBracket.lean`): the step of
the float bracket on the joint rational sine–cosine bracket.  `gd⁻¹ q` is irrational for every
rational `q ≠ 0` in the domain (`irrational_gdInv_rat`).  A tiny `q` is rounded by one test
(`tanTinyRat?`); a small one starts with as many more bits as it has leading zeros.

**The domain.**  `|q| < π/2` is decided exactly (`gdInvRatInDomain`): `|q| ≤ 1` is inside,
`|q| ≥ 2` outside, and in between the sign of `cos q` decides, read off its correctly rounded
value at one bit.  Outside the domain the result is `NaN`; `gd⁻¹ 0 = 0` exactly.
-/

namespace Azurite.AzFloat

/-- `gd⁻¹ q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|q| > π/2`, and for `p = 0` unless `q = 0`). -/
def gdInvRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hd : gdInvRatInDomain q = true then
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match tanTinyRat? q p mode with
      | some r => r
      | none =>
        zivLoopCertified (gdInvRatApprox q) p mode
          (p + zivGuardBits + leadingZeroBits (ratExpBound q))
          (gdInvRatApprox_isSome_exists p mode q h0 ((gdInvRatInDomain_iff q h0).mp hd) _
            (by unfold zivGuardBits; omega))
  else (nan, .eq)

/-- `gd⁻¹ q` rounded to nearest at precision `p`. -/
def gdInvRat (q : AzRat) (p : Nat) : AzFloat := (gdInvRatPrecRound q p .Nearest).1

end Azurite.AzFloat
