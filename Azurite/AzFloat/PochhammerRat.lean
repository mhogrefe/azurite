/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pochhammer
import Azurite.AzFloat.GammaRat
import Azurite.AzNat.Compare

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
* **Otherwise** Ziv's loop with fuel on `pochCoreOf` (`AzFloat/Pochhammer.lean`) at the
  roundings of `q`, split at the number `pochRatSplit q n` of negative factors.
* **Contract**: `pochhammerRatPrecRound_eq_or` (`Equiv/PochhammerRat.lean`).
-/

namespace Azurite.AzFloat

/-- Does a factor of `(q)ₙ` vanish: is `q` an integer with `−n < q ≤ 0`? -/
def pochRatHasZero (q : AzRat) (n : Nat) : Bool :=
  decide (q.den = 1) && (decide (q.num = 0) || !q.sign)
    && (AzNat.compare q.num (AzNat.ofNat n) == .lt)

/-- **The exact path**: `pochIntQuot` for `n ≤ 128` and a short `q`, or a cheap product
(`pochExactCheap`); `none` otherwise. -/
def pochRatExact? (q : AzRat) (n p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if (n ≤ 128 ∧ q.num.size + q.den.size ≤ 2 * p + 1024)
      ∨ pochExactCheap (q.num.size + q.den.size) n p = true then
    some (pochIntQuot (AzInt.mkNorm q.sign q.num) q.den.toAzInt n p mode)
  else none

/-- The number of negative factors of `(q)ₙ`: `0` for `q ≥ 0`, `n` for `q ≤ −n`, and `⌈−q⌉`
in between. -/
def pochRatSplit (q : AzRat) (n : Nat) : Nat :=
  if q.sign then 0
  else if AzNat.ofNat n * q.den ≤ q.num then n
  else min n ((q.num / q.den).toNat + (if q.den = 1 then 0 else 1))

/-- `pochCoreOf` for a rational `q`: the sign of `(q)ₙ` and a positive enclosure of
`|(q)ₙ|`. -/
def pochRatCore (q : AzRat) (n w : Nat) : Option (Bool × Encl) :=
  pochCoreOf (lnGammaRatEncl q) (pochRatSplit q n) n
    (gammaLnBits (expOf (addPrecRound (ofAzRatRound q.abs 64 .Ceiling).1
      (ofAzNat (AzNat.ofNat n)) 64 .Ceiling).1)) w

/-- The bracket of `(q)ₙ` as a pair of `Roundable`s. -/
def pochRatApprox (q : AzRat) (n w : Nat) : Roundable × Roundable :=
  gammaApproxOf (pochRatCore q n w) w

/-- `(q)ₙ` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`, or if the fuel runs out). -/
def pochhammerRatPrecRound (q : AzRat) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if n = 0 then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
  else if pochRatHasZero q n then (zero, .eq)
  else if p = 0 then (nan, .eq)
  else
    match pochRatExact? q n p mode with
    | some r => r
    | none => zivLoop (pochRatApprox q n) p mode gammaFuel (max 64 (p + 32))

/-- `(q)ₙ` rounded to nearest at precision `p`. -/
def pochhammerRat (q : AzRat) (n p : Nat) : AzFloat := (pochhammerRatPrecRound q n p .Nearest).1

end Azurite.AzFloat
