/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.ExpApprox

/-!
## The exponential of a rational

`expRatPrecRound q p mode` is `exp q` correctly rounded to precision `p` in `mode`, for a
rational `q`, with the comparison against the exact value; `expRat q p` rounds to nearest.  The
bracket (`expRatApprox`) is `exp` of the float `⌊q⌋_W` below `q` at the working precision
`W = w + 16 + size (num q)` — one run of `expBracket` — with the upper end widened by the factor
`1 + 2^(−w−14) ≥ exp (q − ⌊q⌋_W)`; the certified Ziv loop needs no fuel since `exp q` is
irrational for every rational `q ≠ 0` (`irrational_exp_rat`).  `exp 0 = 1` exactly.  The
specification `expRatPrecRound_eq` is in `Equiv/ExpRat.lean`.
-/

namespace Azurite.AzFloat

/-- `exp q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def expRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else if h0 : q.num = 0 then setPrecRound one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified (expRatApprox q) p mode (p + zivGuardBits)
      (expRatApprox_isSome_exists p mode q h0 (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `exp q` rounded to nearest at precision `p`. -/
def expRat (q : AzRat) (p : Nat) : AzFloat := (expRatPrecRound q p .Nearest).1

end Azurite.AzFloat
