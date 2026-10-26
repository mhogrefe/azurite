/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.ExpApprox

/-!
## The exponential function

`exp x` by argument reduction and bit-burst binary splitting (MCA §4.3.1, §4.9): `x = k ln 2 + r`
with `k = ⌊⌊x / ln 2⌋⌋` computed against the bracket of `ln 2` at a working precision that grows
with the exponent of `x`, so that `|r| < 3/4` and the bracket of `r` has width `2^(−w−10)`
(`expReduce`); `exp r` on the dyadic truncation `M / 2^(2^K)` of `|r|` by the bit-burst
algorithm — chunks of `2^i` bits at scale `2^(−2^(i+1))`, each `exp (p / 2^s)` summed exactly as
a fraction by binary splitting (`AzNat.expNumDen`) and bracketed by a directed-rounding
division (`expChunkBracket`), the brackets multiplied (`expDyadicBracket`) — with the upper end
widened by `exp d ≤ 1 + 2d` for the distance `d` to the upper end of the bracket of `r`
(`expSmallBracket`); a negative `r` goes through `exp (−r)` and a reciprocal
(`expSignedBracket`); the shift by `k` is exact (`expBracket`).  The result is rounded by the
certified Ziv loop: `exp x` is irrational for every finite `x` (`irrational_exp_rat`) and the
bracket width tends to zero (`expApprox_spec`, `tendsto_expEps`), so `zivLoopCertified` needs
no fuel and `expPrecRound` is total and proven correctly rounded (`Equiv/Exp.lean`).

The cost at precision `p` is dominated by the first Ziv level, `w = p + 64`: the bracket of
`ln 2` and one division at `w + 16 + max(e, 0)` bits (`e` the exponent of `x`), and
`K + 1 = O(log w)` chunk series of `O(w / 2^i)` terms, each by binary splitting at `O(w)` bits,
for `O(M(w) log² w)` in all.

Special values follow IEEE 754 / MPFR conventions: `exp NaN = NaN`, `exp (+∞) = +∞`,
`exp (−∞) = 0`, and `exp 0 = 1` exactly.
-/

namespace Azurite.AzFloat

/-- `exp x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def expPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (zero, .eq)
  | zero => if p = 0 then (nan, .eq) else setPrecRound one p mode
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (expApprox (finite s e q m hv) e) p mode (p + zivGuardBits)
        (expApprox_isSome_exists p mode s e hv (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `exp x` rounded to nearest at the precision of `x`. -/
def exp (x : AzFloat) : AzFloat := (expPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
