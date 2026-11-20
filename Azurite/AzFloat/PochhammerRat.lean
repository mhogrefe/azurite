/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PochhammerRatCertificate

/-!
## Pochhammer's symbol of a rational

`pochhammerRatPrecRound q n p mode` is `(q)ₙ = q (q + 1) ⋯ (q + n − 1)` for an `AzRat` `q` and a
natural number `n`, rounded to precision `p` in `mode` with the comparison against the exact
value; `pochhammerRat q n p` rounds to nearest.  The value is a rational number.

* **Special values**: `(q)₀ = 1`; `0` exactly when a factor vanishes — `q` an integer with
  `−n < q ≤ 0` (`pochRatHasZero`).
* **Exact path** (`pochRatExact?`): for `n ≤ 128` and a `q = N/D` whose numerator and
  denominator have at most `2p + 1024` bits together, or whenever the product is cheaper
  than the loop (`pochExactCheap`), `∏ (N + j D) / Dⁿ` by one correctly rounded division of
  exact floats (`pochIntQuot`).
* **Otherwise** Ziv's loop on `pochCoreOf` (`AzFloat/Pochhammer.lean`) at the roundings of
  `q`, split at the number `pochRatSplit q n` of negative factors
  (`AzFloat/PochhammerRatBracket.lean`).
* **No fuel when the denominator is not a power of two** (`pochRatSpecial`): `(q)ₙ` is then
  a reduced fraction with the denominator `denⁿ`, not dyadic, hence no rounding boundary, and
  the loop is backed by the certified one (`zivLoopBacked`, `pochRatApprox_cert`).  With a
  power of two for a denominator the value is dyadic and the loop keeps its fuel.
* **Contract**: `pochhammerRatPrecRoundFuel_zivSpec` (`Equiv/PochhammerRat.lean`).
-/

namespace Azurite.AzFloat

/-- `(q)ₙ` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`, or if the fuel runs out — which it cannot
when the denominator of `q` is not a power of two), with the fuel of the Ziv loop explicit. -/
def pochhammerRatPrecRoundFuel (fuel : Nat) (q : AzRat) (n p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hn : n = 0 then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
  else if pochRatHasZero q n then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    match pochRatExact? q n p mode with
    | some r => r
    | none =>
      if hc : pochRatSpecial q = true then
        haveI : NeZero p := ⟨hp⟩
        zivLoopBacked (pochRatApprox q n) p mode fuel (max 64 (p + 32))
          (pochRatApprox_cert hn hc p mode _
            (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _)))
      else zivLoop (pochRatApprox q n) p mode fuel (max 64 (p + 32))

/-- `(q)ₙ` rounded to precision `p` with `mode`, and the comparison with the exact value:
`pochhammerRatPrecRoundFuel` at the fuel `gammaFuel p`.  The specification is
`pochhammerRatPrecRoundFuel_zivSpec` (`Equiv/PochhammerRat.lean`). -/
def pochhammerRatPrecRound (q : AzRat) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  pochhammerRatPrecRoundFuel (gammaFuel p) q n p mode

/-- `(q)ₙ` rounded to nearest at precision `p`. -/
def pochhammerRat (q : AzRat) (n p : Nat) : AzFloat := (pochhammerRatPrecRound q n p .Nearest).1

end Azurite.AzFloat
