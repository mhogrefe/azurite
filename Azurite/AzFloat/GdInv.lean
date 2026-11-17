/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.GdInvBracket
import Azurite.AzFloat.LnP1

/-!
## The inverse Gudermannian `gd⁻¹ x`

`gdInvPrecRound x p mode` is `gd⁻¹ x = ∫₀ˣ sec t dt = ln ((1 + sin x)/cos x)` (DLMF
4.23.41–42) of a float `x` with `|x| < π/2`, correctly rounded to precision `p` in `mode`,
with the comparison against the exact value; `gdInv x` rounds to nearest at the precision of
`x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `gdInvApprox`
(`AzFloat/GdInvBracket.lean`): one joint sine–cosine evaluation and one logarithm.  The loop
terminates because `gd⁻¹ x` is irrational for every nonzero float in the domain
(`irrational_gdInv_rat`, from the irrationality of the Gudermannian of a nonzero rational).

**Extreme arguments.**  A tiny `x` (`|x| < 2^e`, `e ≤ −(max p q + 72)`) is rounded by one test
(`tanTiny?`: `|x| < gd⁻¹ |x| ≤ |x| + |x|³`); a small `x` above that starts with as many more
bits as it has leading zeros.  Next to `±π/2` the value is about `−ln (π/2 − |x|)`: the bracket
is rejected until the working precision exceeds the number of leading zero bits of `π/2 − |x|`
(at most about the precision of `x`), so the loop runs a step or two longer.

**The domain.**  `gd⁻¹` is defined on `(−π/2, π/2)`; a float is never equal to `±π/2`, and the
test `|x| < π/2` is exact (`gdInvInDomain`).  Special values: `gd⁻¹ NaN = NaN`;
`gd⁻¹ x = NaN` for `|x| > π/2`, in particular for `±∞`; `gd⁻¹ 0 = 0` exactly.  The function is
odd.
-/

namespace Azurite.AzFloat

/-- `gd⁻¹ x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|x| > π/2`, and for `p = 0` unless `x = 0`). -/
def gdInvPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hd : gdInvInDomain (finite s e q m hv) e q = true then
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        match tanTiny? s (finite s e q m hv) e q p mode with
        | some r => r
        | none =>
          zivLoopCertified (gdInvApprox (!s) (finite s e q m hv) e) p mode
            (p + zivGuardBits + leadingZeroBits e)
            (gdInvApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
              (finiteVal_ne_zero s e hv) ((gdInvInDomain_iff s e hv).mp hd)
              (finiteVal_neg_iff s e hv) (abs_finiteVal_bounds s e hv).2 _
              (by unfold zivGuardBits; omega))
    else (nan, .eq)

/-- `gd⁻¹ x` rounded to nearest at the precision of `x`. -/
def gdInv (x : AzFloat) : AzFloat := (gdInvPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
