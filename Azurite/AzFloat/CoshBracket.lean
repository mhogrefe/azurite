/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.PowRatBracket

/-!
## The brackets of `cosh x` and `cosh q`

`cosh a = (E + 1/E)/2` with `E = exp |a| ≥ 1`: a sum of positive terms, increasing in `E` on
`[1, ∞)`.  `coshOfExp b W` evaluates it on an enclosure `b` of `E` with outward rounding at `W`
bits (two divisions; the lower end of `b` is first raised to `1`), `coshBracket x e w` applies
it to `expBracket |x| e w` for a float, and `coshRatBracket q w` to `expRatBracket |q| w` for a
rational.  `coshApprox`, `coshRatApprox` are the pairs of `Roundable`s for the Ziv loops of
`AzFloat/Cosh.lean` and `AzFloat/CoshRat.lean`.

**Tiny arguments**: `1 < cosh x ≤ exp (x²/2)`, so for `|x| < 2^e` the value is `exp v` with
`0 < v < 2^(2e−1)`, and the tiny-exponent test of the exponential, `expNearOne?` (exact end `1`
at the open side), applies at the exponent `2e − 1` (`coshTinyExp`; for a rational,
`coshRatTinyExp`).

The proofs are in `Equiv/CoshBracket.lean`.
-/

namespace Azurite.AzFloat

/-- `(E + 1/E)/2` on an enclosure of `E ≥ 1`, rounded outwards at precision `W`. -/
def coshOfExp (b : Encl) (W : Nat) : Encl :=
  let l := maxOf b.1 one
  let s1 := (addPrecRound l (divPrecRound one l W .Floor).1 W .Floor).1
  let s2 := (addPrecRound b.2 (divPrecRound one b.2 W .Ceiling).1 W .Ceiling).1
  (s1 <<< AzInt.ofInt (-1), s2 <<< AzInt.ofInt (-1))

/-- The bracket of `cosh x` at Ziv level `w` for a finite float `x` with `|x| < 2^e`. -/
def coshBracket (x : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  coshOfExp (expBracket x.abs e w) (w + 16)

/-- The bracket of `cosh x` as a pair of `Roundable`s. -/
def coshApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox false (coshBracket x e w)

/-- The exponent `2e − 1` of the tiny-exponent test for `|x| < 2^e`. -/
def coshTinyExp (e : AzInt) : AzInt := e + e + AzInt.ofInt (-1)

/-- The bracket of `cosh q` at Ziv level `w` for a rational `q`. -/
def coshRatBracket (q : AzRat) (w : Nat) : Encl :=
  coshOfExp (expRatBracket q.abs w) (w + 16)

/-- The bracket of `cosh q` as a pair of `Roundable`s. -/
def coshRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox false (coshRatBracket q w)

/-- The exponent of the tiny-exponent test for a rational `q`: `|q| < 2^(ratExpBound q − 1)`. -/
def coshRatTinyExp (q : AzRat) : AzInt := coshTinyExp (ratExpBound q + AzInt.ofInt (-1))

end Azurite.AzFloat
